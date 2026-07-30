//! An SMT-LIB frontend for the incremental 2QBF solver.
//!
//! Supported fragment: Boolean constants, `define-fun` definitions (the
//! definition-level input path — bodies become two-sided gate encodings,
//! so no structure is lost to one-sided clausal encodings), assertions
//! over `and`/`or`/`not`/`=>`/`=`/`xor`/`ite`/`distinct`, quantified
//! assertions with an alternating `forall`/`exists` chain of **any
//! depth**, the incremental commands `push`/`pop`/`check-sat`/
//! `check-sat-assuming`, and `get-model`, which prints the piecewise
//! Skolem functions of the existentials as `define-fun`s parameterized by
//! the universal variables.
//!
//! The frontend infers a session's quantifier structure from its
//! assertions. Two-block sessions run on the 2QBF core, in one of two
//! shapes; anything deeper goes to the alternation front-end:
//!
//! - **∀∃** (Skolem function synthesis): no free constant occurs under a
//!   `forall`. Free constants are solved in the innermost existential
//!   block (truth-equivalent), and `get-model` prints piecewise Skolem
//!   functions of the existentials parameterized by the universals.
//! - **∃∀** (constant synthesis): free constants occur under `forall`
//!   binders, with no `exists` binders. The frontend solves the
//!   *negation*: the gate definitions are self-dual, so only the
//!   assertion roots flip — the internal instance is `∀ constants
//!   ∃ binders, gates: ¬(∧ roots)` — and the verdict is inverted. On
//!   `sat`, `get-model` prints the constant values recovered from the
//!   verified winning universal move of the negation. This is the shape
//!   a synthesis tool needs (∃ strategy bits ∀ inputs: specification).
//!
//! - **Deep** (more than two blocks): the session keeps its own prefix,
//!   built positionally — block `i` of any assertion joins block `i` of
//!   the session, generalizing the two-block rule — with free constants
//!   outermost and the gates innermost, and each check goes to
//!   [`crate::alternation`]. Verdicts only for now: the composed
//!   strategy exists but is not yet rendered as `define-fun`s, so
//!   `get-model` reports that rather than guessing.
//!
//! The structure is fixed by the first quantified assertion (or the
//! first check, defaulting to ∀∃); mixing both shapes in one session
//! would need three quantifier blocks and is rejected.

use crate::{incdet::Options, incremental::IncrementalSolver, SolverResult};
use std::collections::HashMap;
use std::fmt::Write;

#[derive(Debug, Clone, PartialEq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    fn atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(a) => Some(a),
            SExpr::List(_) => None,
        }
    }
}

fn tokenize(source: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            ';' => {
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '(' | ')' => tokens.push(c.to_string()),
            '|' => {
                let mut atom = String::new();
                for c in chars.by_ref() {
                    if c == '|' {
                        break;
                    }
                    atom.push(c);
                }
                tokens.push(atom);
            }
            '"' => {
                let mut atom = String::from("\"");
                for c in chars.by_ref() {
                    atom.push(c);
                    if c == '"' {
                        break;
                    }
                }
                tokens.push(atom);
            }
            c if c.is_whitespace() => {}
            c => {
                let mut atom = String::from(c);
                while let Some(&n) = chars.peek() {
                    if n.is_whitespace() || n == '(' || n == ')' || n == ';' {
                        break;
                    }
                    atom.push(n);
                    chars.next();
                }
                tokens.push(atom);
            }
        }
    }
    tokens
}

fn parse(tokens: &[String]) -> Result<Vec<SExpr>, String> {
    let mut stack: Vec<Vec<SExpr>> = vec![Vec::new()];
    for token in tokens {
        match token.as_str() {
            "(" => stack.push(Vec::new()),
            ")" => {
                let list = stack.pop().ok_or("unbalanced ')'")?;
                stack.last_mut().ok_or("unbalanced ')'")?.push(SExpr::List(list));
            }
            atom => {
                stack.last_mut().expect("stack never empty").push(SExpr::Atom(atom.to_string()));
            }
        }
    }
    if stack.len() != 1 {
        return Err("unbalanced '('".to_string());
    }
    Ok(stack.pop().expect("checked"))
}

/// Scope of a surface symbol.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Binding {
    /// a free constant (existential; must not occur under a forall)
    Constant(i32),
    /// a universal variable bound by a forall
    Universal(i32),
    /// an existential variable bound by an exists (under a forall)
    Inner(i32),
    /// a defined symbol (gate literal), flagged if its body referenced a
    /// free constant (using it under a forall then counts as using a
    /// constant there)
    Defined(i32, bool),
}

impl Binding {
    fn lit(self) -> i32 {
        match self {
            Binding::Constant(l)
            | Binding::Universal(l)
            | Binding::Inner(l)
            | Binding::Defined(l, _) => l,
        }
    }
}

/// The quantifier structure of a session, inferred from its assertions.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Mode {
    /// no quantified assertion or check yet; assertion roots stay pending
    Undecided,
    /// ∀∃: forall binders universal, free constants existential
    ForallExists,
    /// ∃∀: free constants universal, forall binders existential; solved
    /// as the negation with the verdict inverted
    ExistsForall,
    /// more than two blocks: the session keeps its own prefix and the
    /// checks go to the alternation front-end rather than the 2QBF core
    Deep,
}

/// One frame of surface-level state, kept in sync with the solver's
/// assertion stack.
#[derive(Debug, Default, Clone)]
struct SurfaceFrame {
    symbols: Vec<(String, Binding)>,
    gates: Vec<((String, Vec<i32>), i32)>,
    /// assertion root literals not materialized as unit clauses: pending
    /// while the quantifier structure is undecided, and the conjuncts of
    /// the surface formula in ∃∀ mode
    asserts: Vec<i32>,
    /// free constants declared in this frame
    constants: Vec<u32>,
}

pub struct Frontend {
    solver: IncrementalSolver,
    frames: Vec<SurfaceFrame>,
    /// user-visible names for the model, by variable
    names: HashMap<i32, String>,
    true_lit: Option<i32>,
    mode: Mode,
    /// scratch flag: set during expression translation when a free
    /// constant (or a defined symbol referencing one) is used
    used_constant: bool,
    /// in ∃∀ mode: the constant values of the last sat check, from the
    /// verified winning universal move of the internal negation
    witness: Option<Vec<i32>>,
    options: Options,
    /// in `Deep` mode: the session's quantifier blocks, outermost first.
    /// Assertions contribute positionally — block `i` of any assertion
    /// joins block `i` of the session — which generalizes the two-block
    /// rule that all `forall` binders are universal and all `exists`
    /// binders inner.
    blocks: Vec<(bool, Vec<u32>)>,
    last: Option<SolverResult>,
}

impl Frontend {
    #[must_use]
    pub fn new(options: Options) -> Self {
        Self {
            solver: IncrementalSolver::new(options),
            options,
            frames: vec![SurfaceFrame::default()],
            names: HashMap::new(),
            true_lit: None,
            mode: Mode::Undecided,
            used_constant: false,
            witness: None,
            blocks: Vec::new(),
            last: None,
        }
    }

    fn lookup(&self, name: &str, locals: &[(String, Binding)]) -> Option<Binding> {
        if let Some((_, b)) = locals.iter().rev().find(|(n, _)| n == name) {
            return Some(*b);
        }
        for frame in self.frames.iter().rev() {
            if let Some((_, b)) = frame.symbols.iter().rev().find(|(n, _)| n == name) {
                return Some(*b);
            }
        }
        None
    }

    fn declare(&mut self, name: &str, binding: Binding) {
        // a defined symbol can alias an existing variable's literal; the
        // variable keeps its original name in models
        self.names.entry(binding.lit().abs()).or_insert_with(|| name.to_string());
        self.frames
            .last_mut()
            .expect("base frame exists")
            .symbols
            .push((name.to_string(), binding));
    }

    fn true_lit(&mut self) -> i32 {
        if let Some(t) = self.true_lit {
            return t;
        }
        let var = self.solver.fresh_var();
        self.solver.declare_existential(var);
        let t = i32::try_from(var).expect("fits");
        self.solver.add_clause(&[t]);
        self.true_lit = Some(t);
        t
    }

    /// A gate literal for `g = AND(lits)`, hash-consed per structural key.
    fn and_gate(&mut self, mut lits: Vec<i32>) -> i32 {
        lits.sort_unstable();
        lits.dedup();
        if lits.iter().any(|&l| lits.contains(&-l) && l > 0) {
            return -self.true_lit();
        }
        match lits.len() {
            0 => return self.true_lit(),
            1 => return lits[0],
            _ => {}
        }
        let key = ("and".to_string(), lits.clone());
        for frame in self.frames.iter().rev() {
            if let Some((_, g)) = frame.gates.iter().find(|(k, _)| *k == key) {
                return *g;
            }
        }
        let var = self.solver.fresh_var();
        self.solver.define_and(var, &lits);
        let g = i32::try_from(var).expect("fits");
        self.frames.last_mut().expect("base frame exists").gates.push((key, g));
        g
    }

    fn or_gate(&mut self, lits: Vec<i32>) -> i32 {
        -self.and_gate(lits.into_iter().map(|l| -l).collect())
    }

    /// Translates an expression into a literal, Tseitin-encoding gates on
    /// the way. `locals` holds quantifier-bound symbols; `quantified` is
    /// true under a forall, where free constants are rejected.
    fn expr(
        &mut self,
        expr: &SExpr,
        locals: &mut Vec<(String, Binding)>,
        quantified: bool,
    ) -> Result<i32, String> {
        match expr {
            SExpr::Atom(a) => match a.as_str() {
                "true" => Ok(self.true_lit()),
                "false" => Ok(-self.true_lit()),
                name => {
                    let binding = self
                        .lookup(name, locals)
                        .ok_or_else(|| format!("unknown symbol {name}"))?;
                    let is_constant = match binding {
                        Binding::Constant(_) => true,
                        Binding::Defined(_, uses_constant) => uses_constant,
                        Binding::Universal(_) | Binding::Inner(_) => false,
                    };
                    if is_constant {
                        self.used_constant = true;
                        if quantified && self.mode == Mode::ForallExists {
                            return Err(format!(
                                "free constant {name} under a forall cannot be mixed with \
                                 earlier ∀∃ assertions (three quantifier blocks)"
                            ));
                        }
                    }
                    Ok(binding.lit())
                }
            },
            SExpr::List(items) => {
                let Some(head) = items.first().and_then(SExpr::atom) else {
                    return Err("expected an operator".to_string());
                };
                let args = &items[1..];
                let mut lits = |this: &mut Self| -> Result<Vec<i32>, String> {
                    args.iter().map(|a| this.expr(a, locals, quantified)).collect()
                };
                match head {
                    "and" => {
                        let lits = lits(self)?;
                        Ok(self.and_gate(lits))
                    }
                    "or" => {
                        let lits = lits(self)?;
                        Ok(self.or_gate(lits))
                    }
                    "not" => {
                        if args.len() != 1 {
                            return Err("not takes one argument".to_string());
                        }
                        Ok(-self.expr(&args[0], locals, quantified)?)
                    }
                    "=>" => {
                        let lits = lits(self)?;
                        if lits.is_empty() {
                            return Err("=> needs arguments".to_string());
                        }
                        let (last, premises) = lits.split_last().expect("nonempty");
                        let mut clause: Vec<i32> = premises.iter().map(|&l| -l).collect();
                        clause.push(*last);
                        Ok(self.or_gate(clause))
                    }
                    "=" | "xor" => {
                        let lits = lits(self)?;
                        if lits.len() < 2 {
                            return Err(format!("{head} needs at least two arguments"));
                        }
                        let mut acc = lits[0];
                        for &b in &lits[1..] {
                            let same = self.and_gate(vec![acc, b]);
                            let diff = self.and_gate(vec![-acc, -b]);
                            let eq = self.or_gate(vec![same, diff]);
                            acc = if head == "=" { eq } else { -eq };
                        }
                        // n-ary xor chains; n-ary = is pairwise-chained,
                        // which for Bool coincides with chained equality
                        Ok(acc)
                    }
                    "distinct" => {
                        let lits = lits(self)?;
                        if lits.len() != 2 {
                            return Err("distinct supports exactly two Booleans".to_string());
                        }
                        let same = self.and_gate(vec![lits[0], lits[1]]);
                        let diff = self.and_gate(vec![-lits[0], -lits[1]]);
                        Ok(-self.or_gate(vec![same, diff]))
                    }
                    "ite" => {
                        let lits = lits(self)?;
                        if lits.len() != 3 {
                            return Err("ite takes three arguments".to_string());
                        }
                        let then = self.and_gate(vec![lits[0], lits[1]]);
                        let els = self.and_gate(vec![-lits[0], lits[2]]);
                        Ok(self.or_gate(vec![then, els]))
                    }
                    "forall" | "exists" => {
                        Err(format!("{head} is only supported at the top of an assertion"))
                    }
                    other => Err(format!("unsupported operator {other}")),
                }
            }
        }
    }

    /// Parses a binding list, allocating fresh variables and pushing them
    /// onto `locals` and `vars`. The variables are *not* yet declared to
    /// the solver: their quantifier depends on the assertion's shape (∀∃
    /// vs ∃∀), which is only known after translating the body.
    fn bind_quantifier(
        &mut self,
        bindings: &SExpr,
        universal: bool,
        locals: &mut Vec<(String, Binding)>,
        vars: &mut Vec<u32>,
    ) -> Result<(), String> {
        let SExpr::List(pairs) = bindings else {
            return Err("expected a binding list".to_string());
        };
        for pair in pairs {
            let SExpr::List(pair) = pair else {
                return Err("expected (name Bool) bindings".to_string());
            };
            let [SExpr::Atom(name), SExpr::Atom(sort)] = &pair[..] else {
                return Err("expected (name Bool) bindings".to_string());
            };
            if sort != "Bool" {
                return Err(format!("only Bool is supported, got {sort}"));
            }
            let var = self.solver.fresh_var();
            let lit = i32::try_from(var).expect("fits");
            let binding = if universal { Binding::Universal(lit) } else { Binding::Inner(lit) };
            self.names.insert(lit, name.clone());
            locals.push((name.clone(), binding));
            vars.push(var);
        }
        Ok(())
    }

    /// Fixes the session's quantifier structure as ∀∃ and materializes
    /// the pending assertion roots as unit clauses, each in the frame its
    /// assertion belongs to.
    fn fix_forall_exists(&mut self) {
        debug_assert_eq!(self.mode, Mode::Undecided);
        self.mode = Mode::ForallExists;
        for depth in 0..self.frames.len() {
            let roots = std::mem::take(&mut self.frames[depth].asserts);
            for root in roots {
                self.solver.add_clause_at(depth, &[root]);
            }
        }
    }

    /// Fixes the session's quantifier structure as ∃∀: the free constants
    /// become the universal block of the internal negation.
    fn fix_exists_forall(&mut self) {
        debug_assert_eq!(self.mode, Mode::Undecided);
        self.mode = Mode::ExistsForall;
        for frame in &self.frames {
            for &var in &frame.constants {
                self.solver.redeclare_universal(var);
            }
        }
    }

    fn assert(&mut self, expr: &SExpr) -> Result<(), String> {
        let mut locals = Vec::new();
        // (forall (...) body) and (forall (...) (exists (...) body))
        let mut body = expr;
        // the whole alternating quantifier chain, however deep: a
        // two-block prefix keeps the 2QBF path, anything deeper switches
        // the session to the alternation front-end
        let mut chain: Vec<(bool, Vec<u32>)> = Vec::new();
        loop {
            let SExpr::List(items) = body else { break };
            let head = items.first().and_then(SExpr::atom);
            let universal = match head {
                Some("forall") => true,
                Some("exists") if !chain.is_empty() => false,
                _ => break,
            };
            if items.len() != 3 {
                return Err(format!(
                    "{} takes a binding list and a body",
                    head.unwrap_or("quantifier")
                ));
            }
            if chain.last().is_some_and(|&(previous, _)| previous == universal) {
                return Err("adjacent quantifier blocks must alternate".to_string());
            }
            let mut vars = Vec::new();
            self.bind_quantifier(&items[1], universal, &mut locals, &mut vars)?;
            chain.push((universal, vars));
            body = &items[2];
        }
        let quantified = !chain.is_empty();
        let deep = chain.len() > 2 || self.mode == Mode::Deep;
        let mut forall_vars = Vec::new();
        let mut exists_vars = Vec::new();
        if !deep {
            for (universal, vars) in &chain {
                if *universal {
                    forall_vars.extend(vars.iter().copied());
                } else {
                    exists_vars.extend(vars.iter().copied());
                }
            }
        }
        self.used_constant = false;
        let lit = self.expr(body, &mut locals, quantified)?;
        if deep {
            if self.mode == Mode::ForallExists || self.mode == Mode::ExistsForall {
                return Err("a deep prefix cannot follow a two-block assertion".to_string());
            }
            self.mode = Mode::Deep;
            // assertions contribute positionally to the session prefix
            for (index, (universal, vars)) in chain.into_iter().enumerate() {
                match self.blocks.get_mut(index) {
                    Some((existing, block)) if *existing == universal => block.extend(vars),
                    Some(_) => {
                        return Err(
                            "assertions disagree on the quantifier of a prefix block".to_string()
                        )
                    }
                    None => self.blocks.push((universal, vars)),
                }
            }
            // the solver's own prefix is unused in this mode: every
            // variable is declared existential so the clause machinery
            // works, and the block structure is imposed at check time
            for (_, block) in &self.blocks {
                for &var in block {
                    self.solver.declare_existential(var);
                }
            }
            self.solver.add_clause(&[lit]);
            return Ok(());
        }
        if quantified {
            if self.used_constant || self.mode == Mode::ExistsForall {
                // ∃∀ shape: in the internal negation the forall binders
                // are inner existentials
                if !exists_vars.is_empty() {
                    return Err("free constants or earlier ∃∀ assertions cannot be \
                                combined with an exists under a forall (three \
                                quantifier blocks)"
                        .to_string());
                }
                if self.mode == Mode::Undecided {
                    self.fix_exists_forall();
                }
                for var in forall_vars {
                    self.solver.declare_existential(var);
                }
            } else {
                if self.mode == Mode::Undecided {
                    self.fix_forall_exists();
                }
                for var in forall_vars {
                    self.solver.declare_universal(var);
                }
                for var in exists_vars {
                    self.solver.declare_existential(var);
                }
            }
        }
        // the assertion root: a unit clause in ∀∃ mode, a pending
        // conjunct otherwise
        if self.mode == Mode::ForallExists {
            self.solver.add_clause(&[lit]);
        } else {
            self.frames.last_mut().expect("base frame exists").asserts.push(lit);
        }
        Ok(())
    }

    fn get_model(&self) -> Result<String, String> {
        if self.mode == Mode::Deep {
            return Err("no model available; models beyond two quantifier blocks are not \
                        emitted yet (the verdict is decided, the composed strategy is not \
                        yet rendered as define-funs)"
                .to_string());
        }
        if self.mode == Mode::ExistsForall {
            if self.last != Some(SolverResult::Satisfiable) {
                return Err("no model available; the last check-sat was not sat".to_string());
            }
            // the winning universal move of the internal negation is a
            // partial assignment no extension of which has a response, so
            // unmentioned constants can take any value
            let witness = self
                .witness
                .as_ref()
                .ok_or("no model available; no winning move passed verification")?;
            let mut out = String::from("(\n");
            for frame in &self.frames {
                for &var in &frame.constants {
                    let var = i32::try_from(var).expect("fits");
                    let name = self.names.get(&var).cloned().unwrap_or_else(|| format!("_c{var}"));
                    let value = witness.contains(&var);
                    let _ = writeln!(out, "  (define-fun {name} () Bool {value})");
                }
            }
            out.push_str(")\n");
            return Ok(out);
        }
        let model = self
            .solver
            .skolem_model()
            .ok_or("no model available; the last check-sat was not sat")?;
        let names = self.names.clone();
        Ok(model.to_smtlib(&move |var: i32| names.get(&var).cloned()))
    }

    /// Runs a check under extra assumption roots, dispatching on the
    /// session's quantifier structure, and returns the surface verdict.
    fn check(&mut self, extra: &[i32]) -> SolverResult {
        if self.mode == Mode::Undecided {
            // no quantified assertion so far: a propositional (∃-only)
            // session, solved as ∀∃ with an empty universal block
            self.fix_forall_exists();
        }
        if self.mode == Mode::Deep {
            let mut qcnf = self.solver.qcnf();
            // impose the session's prefix: free constants outermost,
            // then the declared blocks, with the gates innermost (they
            // are defined by the matrix, so they must follow everything
            // they read)
            let constants: Vec<crate::literal::Var> = self
                .frames
                .iter()
                .flat_map(|f| f.constants.iter())
                .map(|&v| crate::literal::Var::from_index(v - 1))
                .collect();
            let mut placed: std::collections::HashSet<crate::literal::Var> =
                constants.iter().copied().collect();
            let mut prefix: Vec<(crate::QuantTy, Vec<crate::literal::Var>)> =
                vec![(crate::QuantTy::Exists, constants)];
            for (universal, block) in &self.blocks {
                let vars: Vec<crate::literal::Var> = block
                    .iter()
                    .map(|&v| crate::literal::Var::from_index(v - 1))
                    .collect();
                placed.extend(vars.iter().copied());
                prefix.push((
                    if *universal { crate::QuantTy::Forall } else { crate::QuantTy::Exists },
                    vars,
                ));
            }
            // everything else is a gate or a temporary: innermost
            let gates: Vec<crate::literal::Var> = qcnf
                .prefix
                .iter()
                .flat_map(|(_, vars)| vars.iter().copied())
                .chain(qcnf.matrix.iter().flatten().map(|l| l.var()))
                .filter(|v| !placed.contains(v))
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            match prefix.last_mut() {
                Some((crate::QuantTy::Exists, block)) => block.extend(gates),
                _ => prefix.push((crate::QuantTy::Exists, gates)),
            }
            qcnf.prefix = prefix;
            for &lit in extra {
                qcnf.matrix.push(vec![crate::literal::Lit::from_dimacs(lit)]);
            }
            let (result, _strategy) = crate::alternation::solve_certified(
                &qcnf,
                self.options,
                crate::alternation::EXPANSION_BUDGET,
            );
            self.witness = None;
            self.last = Some(result);
            return result;
        }
        let result = if self.mode == Mode::ExistsForall {
            // Solve the negation ∀ constants ∃ binders, gates: ¬(∧ roots)
            // and invert the verdict. The disjunction of the negated
            // roots weakens whenever an assertion is added, so it must
            // stay a temporary clause: carried learnt clauses must never
            // resolve against it. (Reifying it as a hash-consed AND gate
            // to make the check an in-place assumption query was measured
            // 25–90x slower — the accumulated gates make the instances
            // harder than the flat clause; see RESEARCH.md.)
            let clause: Vec<i32> = self
                .frames
                .iter()
                .flat_map(|f| f.asserts.iter())
                .chain(extra.iter())
                .map(|&l| -l)
                .collect();
            let internal = self.solver.solve_with_clauses(&[clause]);
            // the synthesized parameters: complete, so a satisfiable
            // synthesis answer always carries a model (the recorded
            // move is heuristic and can fail verification, in which
            // case the solver re-derives one by self-reduction)
            self.witness = match internal {
                SolverResult::Unsatisfiable => {
                    self.solver.universal_witness_complete(&|_| true)
                }
                _ => None,
            };
            match internal {
                SolverResult::Satisfiable => SolverResult::Unsatisfiable,
                SolverResult::Unsatisfiable => SolverResult::Satisfiable,
                SolverResult::Unknown => SolverResult::Unknown,
            }
        } else if extra.is_empty() {
            self.solver.solve()
        } else {
            self.solver.solve_with_assumptions(extra)
        };
        self.last = Some(result);
        result
    }

    #[allow(clippy::too_many_lines)]
    fn command(&mut self, cmd: &SExpr, out: &mut String) -> Result<(), String> {
        let SExpr::List(items) = cmd else {
            return Err("expected a command".to_string());
        };
        let Some(head) = items.first().and_then(SExpr::atom) else {
            return Err("expected a command".to_string());
        };
        let args = &items[1..];
        match head {
            "set-logic" | "set-info" | "set-option" | "exit" | "reset-assertions" | "get-info" => {}
            "declare-const" | "declare-fun" => {
                let Some(name) = args.first().and_then(SExpr::atom) else {
                    return Err(format!("{head} needs a name"));
                };
                let sort = match (head, args.len()) {
                    ("declare-const", 2) => args[1].atom(),
                    ("declare-fun", 3) if args[1] == SExpr::List(vec![]) => args[2].atom(),
                    _ => None,
                };
                if sort != Some("Bool") {
                    return Err(format!("{head}: only nullary Bool symbols are supported"));
                }
                let var = self.solver.fresh_var();
                if self.mode == Mode::ExistsForall {
                    self.solver.declare_universal(var);
                } else {
                    self.solver.declare_existential(var);
                }
                self.frames.last_mut().expect("base frame exists").constants.push(var);
                self.declare(name, Binding::Constant(i32::try_from(var).expect("fits")));
            }
            "define-fun" => {
                let [SExpr::Atom(name), SExpr::List(params), SExpr::Atom(sort), body] = args
                else {
                    return Err("define-fun: expected name, parameters, sort, body".to_string());
                };
                if !params.is_empty() || sort != "Bool" {
                    return Err(
                        "define-fun: only nullary Bool definitions are supported".to_string()
                    );
                }
                let mut locals = Vec::new();
                self.used_constant = false;
                let lit = self.expr(body, &mut locals, false)?;
                self.declare(name, Binding::Defined(lit, self.used_constant));
            }
            "assert" => {
                let [expr] = args else {
                    return Err("assert takes one argument".to_string());
                };
                self.assert(expr)?;
            }
            "push" | "pop" => {
                let n = match args {
                    [] => 1,
                    [SExpr::Atom(n)] => n.parse::<usize>().map_err(|_| "invalid level count")?,
                    _ => return Err(format!("{head} takes an optional count")),
                };
                for _ in 0..n {
                    if head == "push" {
                        self.solver.push();
                        self.frames.push(SurfaceFrame::default());
                    } else {
                        if !self.solver.pop() {
                            return Err("pop below the base frame".to_string());
                        }
                        self.frames.pop();
                    }
                }
            }
            "check-sat" => {
                let result = self.check(&[]);
                let _ = writeln!(out, "{}", verdict(result));
            }
            "check-sat-assuming" => {
                let [SExpr::List(assumptions)] = args else {
                    return Err("check-sat-assuming takes a literal list".to_string());
                };
                // gates created for assumption expressions stay in the
                // current frame; their definitions are harmless and get
                // reused through hash-consing
                let mut extra = Vec::new();
                for a in assumptions {
                    let mut locals = Vec::new();
                    extra.push(self.expr(a, &mut locals, false)?);
                }
                let result = self.check(&extra);
                let _ = writeln!(out, "{}", verdict(result));
            }
            "get-model" => {
                let model = self.get_model()?;
                out.push_str(&model);
            }
            "echo" => {
                if let Some(text) = args.first().and_then(SExpr::atom) {
                    let _ = writeln!(out, "{}", text.trim_matches('"'));
                }
            }
            other => return Err(format!("unsupported command {other}")),
        }
        Ok(())
    }

    /// Runs an SMT-LIB script, returning the produced output. Errors are
    /// reported inline in SMT-LIB style and abort the run.
    pub fn run(&mut self, source: &str) -> String {
        let mut out = String::new();
        let commands = match parse(&tokenize(source)) {
            Ok(commands) => commands,
            Err(e) => {
                let _ = writeln!(out, "(error \"{e}\")");
                return out;
            }
        };
        for cmd in &commands {
            if let Err(e) = self.command(cmd, &mut out) {
                let _ = writeln!(out, "(error \"{e}\")");
                break;
            }
        }
        out
    }

    /// The result of the last `check-sat`, for the process exit code.
    #[must_use]
    pub fn last_result(&self) -> Option<SolverResult> {
        self.last
    }
}

fn verdict(result: SolverResult) -> &'static str {
    match result {
        SolverResult::Satisfiable => "sat",
        SolverResult::Unsatisfiable => "unsat",
        SolverResult::Unknown => "unknown",
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    /// Alternating evaluation of a CNF over a block structure: conjoin
    /// over universal blocks, disjoin over existential ones.
    fn game(
        blocks: &[(bool, Vec<usize>)],
        index: usize,
        values: &mut Vec<bool>,
        clauses: &[Vec<i32>],
    ) -> bool {
        let Some((forall, vars)) = blocks.get(index) else {
            return clauses.iter().all(|clause| {
                clause.iter().any(|&l| values[l.unsigned_abs() as usize - 1] == (l > 0))
            });
        };
        let mut all = true;
        let mut any = false;
        for point in 0..1u32 << vars.len() {
            for (bit, &var) in vars.iter().enumerate() {
                values[var] = point >> bit & 1 == 1;
            }
            let sub = game(blocks, index + 1, values, clauses);
            all &= sub;
            any |= sub;
            if (*forall && !all) || (!*forall && any) {
                break;
            }
        }
        if *forall {
            all
        } else {
            any
        }
    }

    fn run(source: &str) -> String {
        Frontend::new(Options::default()).run(source)
    }

    #[test]
    fn propositional() {
        assert_eq!(run("(declare-const x Bool)(assert x)(check-sat)"), "sat\n");
        assert_eq!(run("(declare-const x Bool)(assert x)(assert (not x))(check-sat)"), "unsat\n");
    }

    #[test]
    fn forall_exists() {
        // forall u exists e: e = u
        let sat = "(assert (forall ((u Bool)) (exists ((e Bool)) (= e u))))(check-sat)";
        assert_eq!(run(sat), "sat\n");
        // forall u v: u or v
        let unsat = "(assert (forall ((u Bool) (v Bool)) (or u v)))(check-sat)";
        assert_eq!(run(unsat), "unsat\n");
    }

    #[test]
    fn definitions_and_gates() {
        // forall a b exists c: c = (a xor b), via a definition inside
        let source = "
            (assert (forall ((a Bool) (b Bool))
              (exists ((c Bool)) (= c (xor a b)))))
            (check-sat)";
        assert_eq!(run(source), "sat\n");
    }

    #[test]
    fn incremental_push_pop() {
        let source = "
            (assert (forall ((u Bool)) (exists ((e Bool)) (= e u))))
            (check-sat)
            (push 1)
            (assert (forall ((u Bool)) (exists ((e Bool)) (and e (not e)))))
            (check-sat)
            (pop 1)
            (check-sat)";
        assert_eq!(run(source), "sat\nunsat\nsat\n");
    }

    #[test]
    fn check_sat_assuming() {
        let source = "
            (declare-const x Bool)
            (declare-const y Bool)
            (assert (or x y))
            (check-sat-assuming ((not x) (not y)))
            (check-sat)";
        assert_eq!(run(source), "unsat\nsat\n");
    }

    #[test]
    fn exists_forall_synthesis() {
        let source = "
            (declare-const p Bool)
            (assert (forall ((u Bool)) (or p u)))
            (check-sat)
            (get-model)";
        let out = run(source);
        assert!(out.starts_with("sat\n"), "{out}");
        assert!(out.contains("(define-fun p () Bool true)"), "{out}");
    }

    #[test]
    fn exists_forall_unsat() {
        let source = "
            (declare-const p Bool)
            (assert (forall ((u Bool)) (= p u)))
            (check-sat)";
        assert_eq!(run(source), "unsat\n");
    }

    #[test]
    fn exists_forall_pending_asserts() {
        // the propositional assertion made before the structure is known
        // joins the ∃∀ conjunction
        let source = "
            (declare-const p Bool)
            (declare-const q Bool)
            (assert (not q))
            (assert (forall ((u Bool)) (or p q u)))
            (check-sat)
            (get-model)";
        let out = run(source);
        assert!(out.starts_with("sat\n"), "{out}");
        assert!(out.contains("(define-fun p () Bool true)"), "{out}");
        assert!(out.contains("(define-fun q () Bool false)"), "{out}");
    }

    #[test]
    fn exists_forall_push_pop() {
        let source = "
            (declare-const p Bool)
            (assert (forall ((u Bool)) (or p u)))
            (check-sat)
            (push 1)
            (assert (not p))
            (check-sat)
            (pop 1)
            (check-sat)";
        assert_eq!(run(source), "sat\nunsat\nsat\n");
    }

    #[test]
    fn exists_forall_assuming() {
        let source = "
            (declare-const p Bool)
            (assert (forall ((u Bool)) (or p u)))
            (check-sat-assuming ((not p)))
            (check-sat)";
        assert_eq!(run(source), "unsat\nsat\n");
    }

    #[test]
    fn defined_symbol_carries_constants() {
        // f references the constant p, so using f under a forall makes
        // the session ∃∀
        let source = "
            (declare-const p Bool)
            (define-fun f () Bool (not p))
            (assert (forall ((u Bool)) (or (not f) u)))
            (check-sat)
            (get-model)";
        let out = run(source);
        assert!(out.starts_with("sat\n"), "{out}");
        assert!(out.contains("(define-fun p () Bool true)"), "{out}");
    }

    #[test]
    fn mixed_quantifier_shapes_rejected() {
        // a ∀∃ assertion fixes the structure; a later constant under a
        // forall would need three quantifier blocks
        let source = "
            (declare-const x Bool)
            (assert (forall ((u Bool)) (exists ((e Bool)) (= e u))))
            (assert (forall ((u Bool)) (or x u)))
            (check-sat)";
        assert!(run(source).contains("(error"), "{}", run(source));
    }

    #[test]
    fn exists_forall_with_inner_exists_rejected() {
        let source = "
            (declare-const x Bool)
            (assert (forall ((u Bool)) (exists ((e Bool)) (and x (= e u)))))
            (check-sat)";
        assert!(run(source).contains("(error"), "{}", run(source));
    }

    #[test]
    fn get_model_emits_definitions() {
        let source = "
            (assert (forall ((u Bool) (v Bool))
              (exists ((e Bool)) (= e (and u v)))))
            (check-sat)
            (get-model)";
        let out = run(source);
        assert!(out.starts_with("sat\n"), "{out}");
        assert!(out.contains("(define-fun e "), "{out}");
        assert_eq!(out.matches('(').count(), out.matches(')').count(), "{out}");
    }

    /// Brute-force oracle for ∃ constants ∀ universals: matrix. Variables
    /// `1..=constants` are the constants, the rest the universals.
    fn exists_forall_oracle(constants: u32, universals: u32, clauses: &[Vec<i32>]) -> bool {
        (0..1u32 << constants).any(|p| {
            (0..1u32 << universals).all(|u| {
                clauses.iter().all(|clause| {
                    clause.iter().any(|&l| {
                        let var = l.unsigned_abs();
                        let value = if var <= constants {
                            p & (1 << (var - 1)) != 0
                        } else {
                            u & (1 << (var - constants - 1)) != 0
                        };
                        (l > 0) == value
                    })
                })
            })
        })
    }

    fn exists_forall_script(constants: u32, universals: u32, clauses: &[Vec<i32>]) -> String {
        let mut s = String::new();
        for p in 1..=constants {
            let _ = writeln!(s, "(declare-const p{p} Bool)");
        }
        let binders: String =
            (1..=universals).map(|u| format!("(u{u} Bool)")).collect::<Vec<_>>().join(" ");
        let clause = |c: &Vec<i32>| -> String {
            let lits: Vec<String> = c
                .iter()
                .map(|&l| {
                    let var = l.unsigned_abs();
                    let base = if var <= constants {
                        format!("p{var}")
                    } else {
                        format!("u{}", var - constants)
                    };
                    if l < 0 {
                        format!("(not {base})")
                    } else {
                        base
                    }
                })
                .collect();
            format!("(or {})", lits.join(" "))
        };
        // the tautology mentions a constant, pinning the ∃∀ structure
        // even when no generated clause references one
        let conjuncts: Vec<String> = std::iter::once("(or p1 (not p1))".to_string())
            .chain(clauses.iter().map(clause))
            .collect();
        let _ = writeln!(s, "(assert (forall ({binders}) (and {})))", conjuncts.join(" "));
        s.push_str("(check-sat)\n(get-model)\n");
        s
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(512))]
        /// Random ∃∀ instances against the enumeration oracle; on sat,
        /// the synthesized constants must satisfy the matrix for every
        /// universal assignment.
        #[test]
        /// Deep prefixes against a recursive game oracle over the same
        /// CNF body: the definition of QBF truth, evaluated directly on
        /// the surface formula rather than through the frontend.
        #[test]
        fn differential_deep_prefix(
            sizes in proptest::collection::vec(1usize..=2, 3..=4),
            clauses in proptest::collection::vec(
                proptest::collection::vec(
                    (-8i32..=8).prop_filter("nonzero", |l| *l != 0),
                    1..=3,
                ),
                1..=6,
            ),
        ) {
            let total: usize = sizes.iter().sum();
            let bound = i32::try_from(total).unwrap();
            let clauses: Vec<Vec<i32>> = clauses
                .into_iter()
                .map(|clause| {
                    clause
                        .into_iter()
                        .map(|l| {
                            let m = (l.abs() - 1) % bound + 1;
                            if l < 0 { -m } else { m }
                        })
                        .collect()
                })
                .collect();

            // render the nested quantifier chain, outermost forall
            let mut blocks: Vec<(bool, Vec<usize>)> = Vec::new();
            let mut next = 0usize;
            let mut opens = String::new();
            for (index, &size) in sizes.iter().enumerate() {
                let forall = index % 2 == 0;
                let vars: Vec<usize> = (next..next + size).collect();
                next += size;
                let bindings: Vec<String> =
                    vars.iter().map(|v| format!("(v{v} Bool)")).collect();
                opens.push_str(&format!(
                    "({} ({}) ",
                    if forall { "forall" } else { "exists" },
                    bindings.join(" ")
                ));
                blocks.push((forall, vars));
            }
            let body: Vec<String> = clauses
                .iter()
                .map(|clause| {
                    let lits: Vec<String> = clause
                        .iter()
                        .map(|&l| {
                            let v = l.unsigned_abs() - 1;
                            if l < 0 { format!("(not v{v})") } else { format!("v{v}") }
                        })
                        .collect();
                    format!("(or {})", lits.join(" "))
                })
                .collect();
            let source = format!(
                "(assert {}(and {}){})\n(check-sat)\n",
                opens,
                body.join(" "),
                ")".repeat(sizes.len())
            );

            let mut values = vec![false; total];
            let wins = game(&blocks, 0, &mut values, &clauses);
            let expected = if wins { "sat" } else { "unsat" };
            let actual = run(&source);
            proptest::prop_assert_eq!(actual.trim(), expected, "instance:\n{}", &source);
        }

        #[test]
        fn differential_exists_forall(
            constants in 1u32..=3,
            universals in 1u32..=3,
            clauses in proptest::collection::vec(
                proptest::collection::vec(
                    (-6i32..=6).prop_filter("nonzero", |l| *l != 0),
                    1..=4,
                ),
                1..=8,
            ),
        ) {
            let bound = constants + universals;
            let clauses: Vec<Vec<i32>> = clauses
                .iter()
                .map(|c| {
                    c.iter()
                        .map(|&l| {
                            let m = i32::try_from((l.unsigned_abs() - 1) % bound + 1)
                                .expect("fits");
                            if l < 0 { -m } else { m }
                        })
                        .collect()
                })
                .collect();
            let expected = exists_forall_oracle(constants, universals, &clauses);
            let script = exists_forall_script(constants, universals, &clauses);
            let out = Frontend::new(Options::default()).run(&script);
            let verdict = out.lines().next().unwrap_or("");
            prop_assert_eq!(
                verdict,
                if expected { "sat" } else { "unsat" },
                "script:\n{}\nout:\n{}",
                &script,
                &out
            );
            // a missing model (unverifiable winning move) is reported as
            // an error and tolerated; a printed model must be correct
            if expected && !out.contains("(error") {
                let values: Vec<bool> = (1..=constants)
                    .map(|p| {
                        assert!(
                            out.contains(&format!("(define-fun p{p} () Bool ")),
                            "constant p{p} missing from the model:\n{out}"
                        );
                        out.contains(&format!("(define-fun p{p} () Bool true)"))
                    })
                    .collect();
                for u in 0..1u32 << universals {
                    for clause in &clauses {
                        prop_assert!(
                            clause.iter().any(|&l| {
                                let var = l.unsigned_abs();
                                let value = if var <= constants {
                                    values[usize::try_from(var).expect("fits") - 1]
                                } else {
                                    u & (1 << (var - constants - 1)) != 0
                                };
                                (l > 0) == value
                            }),
                            "synthesized constants falsify the matrix; script:\n{}\nout:\n{}",
                            &script,
                            &out
                        );
                    }
                }
            }
        }
    }
}
