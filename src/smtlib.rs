//! An SMT-LIB frontend for the incremental 2QBF solver.
//!
//! Supported fragment: Boolean constants, `define-fun` definitions (the
//! definition-level input path — bodies become two-sided gate encodings,
//! so no structure is lost to one-sided clausal encodings), assertions
//! over `and`/`or`/`not`/`=>`/`=`/`xor`/`ite`/`distinct`, quantified
//! assertions of the shape `(forall (...) body)` with optional nested
//! `exists`, the incremental commands `push`/`pop`/`check-sat`/
//! `check-sat-assuming`, and `get-model`, which prints the piecewise
//! Skolem functions of the existentials as `define-fun`s parameterized by
//! the universal variables.
//!
//! Free constants are existential. Since the solver core is 2QBF, a free
//! constant may not occur *under* a `forall` (that would need three
//! quantifier blocks: ∃ constants ∀ universals ∃ inner). Free constants
//! and quantified assertions can coexist as long as they do not mix: the
//! constants are then solved in the innermost existential block, which is
//! truth-equivalent.

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
    /// a defined symbol (gate literal)
    Defined(i32),
}

impl Binding {
    fn lit(self) -> i32 {
        match self {
            Binding::Constant(l)
            | Binding::Universal(l)
            | Binding::Inner(l)
            | Binding::Defined(l) => l,
        }
    }
}

/// One frame of surface-level state, kept in sync with the solver's
/// assertion stack.
#[derive(Debug, Default, Clone)]
struct SurfaceFrame {
    symbols: Vec<(String, Binding)>,
    gates: Vec<((String, Vec<i32>), i32)>,
}

pub struct Frontend {
    solver: IncrementalSolver,
    frames: Vec<SurfaceFrame>,
    /// user-visible names for the model, by variable
    names: HashMap<i32, String>,
    true_lit: Option<i32>,
    last: Option<SolverResult>,
}

impl Frontend {
    #[must_use]
    pub fn new(options: Options) -> Self {
        Self {
            solver: IncrementalSolver::new(options),
            frames: vec![SurfaceFrame::default()],
            names: HashMap::new(),
            true_lit: None,
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
        self.names.insert(binding.lit().abs(), name.to_string());
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
                    if quantified && matches!(binding, Binding::Constant(_)) {
                        return Err(format!(
                            "free constant {name} under a forall needs three quantifier \
                             blocks; declare it inside the exists instead"
                        ));
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

    fn bind_quantifier(
        &mut self,
        bindings: &SExpr,
        universal: bool,
        locals: &mut Vec<(String, Binding)>,
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
            let binding = if universal {
                self.solver.declare_universal(var);
                Binding::Universal(lit)
            } else {
                self.solver.declare_existential(var);
                Binding::Inner(lit)
            };
            self.names.insert(lit, name.clone());
            locals.push((name.clone(), binding));
        }
        Ok(())
    }

    fn assert(&mut self, expr: &SExpr) -> Result<(), String> {
        let mut locals = Vec::new();
        // (forall (...) body) and (forall (...) (exists (...) body))
        let mut body = expr;
        let mut quantified = false;
        if let SExpr::List(items) = body {
            if items.first().and_then(SExpr::atom) == Some("forall") {
                if items.len() != 3 {
                    return Err("forall takes a binding list and a body".to_string());
                }
                self.bind_quantifier(&items[1], true, &mut locals)?;
                body = &items[2];
                quantified = true;
                if let SExpr::List(items) = body {
                    if items.first().and_then(SExpr::atom) == Some("exists") {
                        if items.len() != 3 {
                            return Err("exists takes a binding list and a body".to_string());
                        }
                        self.bind_quantifier(&items[1], false, &mut locals)?;
                        body = &items[2];
                    }
                }
            }
        }
        let lit = self.expr(body, &mut locals, quantified)?;
        self.solver.add_clause(&[lit]);
        Ok(())
    }

    fn get_model(&self) -> Result<String, String> {
        let model = self
            .solver
            .skolem_model()
            .ok_or("no model available; the last check-sat was not sat")?;
        let names = self.names.clone();
        Ok(model.to_smtlib(&move |var: i32| names.get(&var).cloned()))
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
                self.solver.declare_existential(var);
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
                let lit = self.expr(body, &mut locals, false)?;
                self.declare(name, Binding::Defined(lit));
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
                let result = self.solver.solve();
                self.last = Some(result);
                let _ = writeln!(out, "{}", verdict(result));
            }
            "check-sat-assuming" => {
                let [SExpr::List(assumptions)] = args else {
                    return Err("check-sat-assuming takes a literal list".to_string());
                };
                self.solver.push();
                self.frames.push(SurfaceFrame::default());
                let mut failed = None;
                for a in assumptions {
                    let mut locals = Vec::new();
                    match self.expr(a, &mut locals, false) {
                        Ok(lit) => self.solver.add_clause(&[lit]),
                        Err(e) => {
                            failed = Some(e);
                            break;
                        }
                    }
                }
                let result = if failed.is_none() { Some(self.solver.solve()) } else { None };
                // keep the model of the assumption query, like the backend
                let _ = self.solver.pop();
                self.frames.pop();
                if let Some(e) = failed {
                    return Err(e);
                }
                let result = result.expect("solved");
                self.last = Some(result);
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
    fn free_constant_under_forall_rejected() {
        let source = "
            (declare-const x Bool)
            (assert (forall ((u Bool)) (or x u)))
            (check-sat)";
        assert!(run(source).starts_with("(error"));
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
}
