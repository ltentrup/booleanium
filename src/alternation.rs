//! Quantifier alternations beyond 2QBF: recursive expansion with the
//! incremental 2QBF core as a persistent oracle (see `RESEARCH.md`,
//! RQ6).
//!
//! The outermost existential block `X` is solved by CEGAR over a plain
//! SAT *abstraction*: candidates `X*` are proposed, the remainder of the
//! prefix is solved under the assumptions `X*`, and inner refutations
//! refine the abstraction. When the remainder is exactly ∀Y∃Z, the
//! oracle is one persistent [`IncrementalSolver`] — `Y` universal,
//! `Z ∪ X` existential, one `solve_with_assumptions(X*)` per candidate,
//! with everything learnt carrying across candidates — and an inner
//! refutation returns a *verified* universal witness `Y*`, so the
//! refinement is the classic expansion `matrix[Y := Y*]` over fresh
//! `Z`-copies — the blocking clause `¬X*` is added alongside (sound,
//! since the oracle refuted the candidate; it guarantees progress even
//! when `Y*` is only the unverified recorded candidate). Without any
//! witness (deep recursion) the blocking clause alone keeps the loop
//! total. A ∀-outermost prefix runs the dual candidate loop — search
//! for a refuting outer assignment, block answered candidates — which
//! keeps the matrix fixed instead of cascading negation gates through
//! the recursion.
//!
//! Every level first *simplifies* its instance ([`simplify`]): the
//! restrictions and expansions the recursion performs manufacture units
//! and pure literals in bulk, and propagating them once per level
//! compounds all the way down.
//!
//! Satisfiable answers come with a composed winning strategy
//! ([`Strategy`], via [`solve_certified`]) wherever the pipeline can
//! build one: simplification contributes the literals it forced, an
//! ∃-loop the constants of its winning candidate, a ∀-loop one
//! sub-strategy per enumerated cube (exhaustive, since the loop only
//! succeeds once every candidate is answered), a leaf the core's
//! certified Skolem model, and a ∀-expansion a multiplexer selecting
//! the copy the actual assignment of the enumerated block picks.
//!
//! Before either loop runs, a *small innermost universal block* is
//! enumerated away instead ([`expand_universal_block`]): ∀-expansion
//! removes an alternation outright, and at the innermost block only the
//! final existential block is copied — a three-block prefix collapses
//! to plain SAT. Only small blocks qualify, because CEGAR enumerates
//! just the relevant assignments while expansion pays for all of them,
//! and only the *collapsing* expansion qualifies at all: handing a
//! multiplied matrix back to the loops instead of to the core loses by
//! two orders of magnitude on deep prefixes.

use crate::{
    incdet::{model::AigBuilder, IncDet, Options},
    incremental::IncrementalSolver,
    literal::{Lit, Var},
    qcnf::QCNF,
    QuantTy, SolverResult,
};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[cfg(feature = "probe")]
pub static LEAF_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static LEAF_VARS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static LEAF_CLAUSES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static MEMO_PROBES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static MEMO_HITS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static MEMO_KEY_UNITS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static MEMO_STRATEGY_UNITS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static ROUNDS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Clause budget for ∀-expansion: a universal block is enumerated away
/// when the expanded matrix stays below this size. Enumerating a small
/// block is far cheaper than reasoning about it, and it removes a
/// quantifier alternation outright.
pub const EXPANSION_BUDGET: usize = 2_000_000;

/// Largest universal block that is enumerated rather than reasoned
/// about. Beyond this the CEGAR loop usually wins: it enumerates only
/// the *relevant* assignments of the block, while expansion pays for
/// all `2^|Y|` of them (measured: a 10-variable block costs 17x more
/// expanded than searched on `p10-1.pddl`, a 7-variable one turns a
/// 30 s timeout into 3 s on `BLOCKS4iii.7`).
const MAX_EXPANDED_BLOCK: usize = 8;


/// The inverse of one ∀-expansion: for every assignment of the
/// enumerated block, the cube selecting it and the renaming that maps
/// each variable bound after the block to its copy in the expanded
/// instance. Applying the renaming of the copy the actual assignment
/// selects turns a strategy for the expansion into one for the
/// original.
type Copies = Vec<(Vec<Lit>, HashMap<Var, Var>)>;

/// Wires already built for a strategy node, keyed by node identity and
/// by the values of the variables that node's subtree mentions. Alive
/// only for one [`Strategy::build`], so the pointers cannot dangle.
/// What one node did to the values it was handed: a wire per variable
/// it defined, and `None` for one it removed.
type Delta = Vec<(Var, Option<u64>)>;

#[derive(Default)]
struct BuildMemo {
    entries: HashMap<(*const Strategy, u128), Delta>,
    relevant: HashMap<*const Strategy, Rc<Vec<Var>>>,
}

impl BuildMemo {
    fn touched(&mut self, node: &Strategy) -> Rc<Vec<Var>> {
        let key = std::ptr::addr_of!(*node);
        if let Some(vars) = self.relevant.get(&key) {
            return Rc::clone(vars);
        }
        let mut vars = Vec::new();
        node.mentions(&mut vars);
        vars.sort_unstable();
        vars.dedup();
        let vars = Rc::new(vars);
        self.relevant.insert(key, Rc::clone(&vars));
        vars
    }
}

/// A 128-bit fingerprint of the values a node can actually read. The
/// variables arrive sorted, so the sequence is canonical.
fn values_key(relevant: &[Var], values: &HashMap<Var, u64>) -> u128 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let digest = |salt: u8| {
        let mut hasher = DefaultHasher::new();
        salt.hash(&mut hasher);
        for var in relevant {
            values.get(var).hash(&mut hasher);
        }
        hasher.finish()
    };
    u128::from(digest(0)) << 64 | u128::from(digest(1))
}

/// A winning strategy for the existential player, composed through the
/// recursion. Evaluated against a full assignment of the *original*
/// universal variables, it yields a value for every existential the
/// solve determined; variables it leaves out were dropped as
/// irrelevant and may take any value.
///
/// The shapes mirror the pipeline: [`Strategy::Fixed`] carries what
/// simplification forced, [`Strategy::Choose`] the constants an ∃-loop
/// candidate committed to, [`Strategy::Split`] one sub-strategy per
/// universal candidate a ∀-loop enumerated (exhaustive, because that
/// loop only succeeds once every candidate is answered), and
/// [`Strategy::Leaf`] a 2QBF Skolem model.
#[derive(Debug, Clone)]
pub enum Strategy {
    /// values a simplification pass forced (units, pure literals)
    Fixed { assignments: Vec<Lit>, rest: Rc<Strategy> },
    /// the constants an outermost existential block committed to
    Choose { constants: Vec<Lit>, rest: Rc<Strategy> },
    /// one sub-strategy per enumerated cube of a universal block
    Split { cases: Vec<(Vec<Lit>, Rc<Strategy>)> },
    /// the inverse of a ∀-expansion: the sub-strategy plays all copies
    /// of the variables bound after the enumerated block at once, and
    /// the copy the actual assignment of the block selects supplies
    /// the value
    Expanded { copies: Copies, rest: Rc<Strategy> },
    /// the certified Skolem functions of a 2QBF leaf
    Leaf(Rc<crate::incdet::model::SkolemModel>),
    /// nothing left to decide
    Done,
}

impl Strategy {
    /// Collects the existential values this strategy prescribes under a
    /// full universal assignment (DIMACS literals).
    pub fn evaluate(&self, universal: &[i32], values: &mut HashMap<i32, bool>) {
        match self {
            Strategy::Done => {}
            Strategy::Fixed { assignments, rest }
            | Strategy::Choose { constants: assignments, rest } => {
                for l in assignments {
                    values.insert(l.var().to_dimacs(), l.is_positive());
                }
                rest.evaluate(universal, values);
            }
            Strategy::Split { cases } => {
                let holds = |cube: &[Lit]| {
                    cube.iter().all(|l| {
                        universal.contains(&l.to_dimacs())
                            || values.get(&l.var().to_dimacs()) == Some(&l.is_positive())
                    })
                };
                if let Some((_, sub)) = cases.iter().find(|(cube, _)| holds(cube)) {
                    sub.evaluate(universal, values);
                }
            }
            Strategy::Expanded { copies, rest } => {
                rest.evaluate(universal, values);
                // the expanded block is universal, so the selecting
                // cube is read straight off the assignment
                let selected = copies
                    .iter()
                    .find(|(cube, _)| cube.iter().all(|l| universal.contains(&l.to_dimacs())));
                if let Some((_, rename)) = selected {
                    let projected: Vec<(i32, bool)> = rename
                        .iter()
                        .filter_map(|(original, copy)| {
                            Some((original.to_dimacs(), *values.get(&copy.to_dimacs())?))
                        })
                        .collect();
                    values.extend(projected);
                }
                // the copies are internal to the expansion
                for (_, rename) in copies {
                    for copy in rename.values() {
                        values.remove(&copy.to_dimacs());
                    }
                }
            }
            Strategy::Leaf(model) => {
                // the leaf's universals are a subset of the outer ones
                let leaf: Vec<i32> = model
                    .universals()
                    .into_iter()
                    .map(|v| if universal.contains(&v) { v } else { -v })
                    .collect();
                values.extend(model.evaluate(&leaf));
            }
        }
    }

    /// A rough node count. Used to keep the sub-solve memo within its
    /// size budget, and worth reporting: on deep prefixes the composed
    /// strategy, not the solve, is what grows out of hand.
    ///
    /// Counts *distinct* nodes: sub-strategies are shared, so a node
    /// reached along several paths is one node, not many. What the
    /// memo has to bound is memory, and memory is the DAG.
    #[must_use]
    pub fn size(&self) -> usize {
        let mut seen = HashSet::new();
        self.size_into(&mut seen)
    }

    fn size_into(&self, seen: &mut HashSet<*const Strategy>) -> usize {
        fn sub(child: &Rc<Strategy>, seen: &mut HashSet<*const Strategy>) -> usize {
            if seen.insert(Rc::as_ptr(child)) {
                child.size_into(seen)
            } else {
                0
            }
        }
        match self {
            Strategy::Done => 1,
            Strategy::Fixed { assignments, rest }
            | Strategy::Choose { constants: assignments, rest } => {
                assignments.len() + sub(rest, seen)
            }
            Strategy::Split { cases } => {
                cases.iter().map(|(cube, s)| cube.len() + sub(s, seen)).sum::<usize>() + 1
            }
            Strategy::Expanded { copies, rest } => {
                copies.iter().map(|(cube, r)| cube.len() + r.len()).sum::<usize>()
                    + sub(rest, seen)
            }
            Strategy::Leaf(model) => model.size(),
        }
    }

    /// Renders the strategy as a *strategy circuit* in ASCII AIGER
    /// format over the given universal variables (one input each, in
    /// order): the same externally checkable artifact
    /// [`SkolemModel::to_aiger`](crate::incdet::model::SkolemModel::to_aiger)
    /// produces for a 2QBF result, for a prefix of any depth.
    #[must_use]
    pub fn to_aiger(&self, universals: &[Var], name: &dyn Fn(i32) -> Option<String>) -> String {
        let (aig, values) = self.build(universals);
        // deterministic output order, and one output per defined variable
        let mut outputs: Vec<(Var, u64)> = values.into_iter().collect();
        outputs.sort_unstable();
        crate::incdet::model::render(&aig, &outputs, universals, name)
    }

    /// Renders the strategy as SMT-LIB `define-fun`s over the universal
    /// variables — the same artifact
    /// [`SkolemModel::to_smtlib`](crate::incdet::model::SkolemModel::to_smtlib)
    /// produces for a 2QBF result, for a prefix of any depth.
    ///
    /// Goes through the same AIG as
    /// [`Strategy::to_aiger`](Strategy::to_aiger): each gate becomes an
    /// internal `define-fun`, each determined variable a public one, so
    /// the two formats cannot disagree about what the strategy is.
    /// `name` maps DIMACS variables to their surface names; variables
    /// without one are omitted from the public definitions, as in the
    /// 2QBF emitter.
    #[must_use]
    pub fn to_smtlib(&self, universals: &[Var], name: &dyn Fn(i32) -> Option<String>) -> String {
        use std::fmt::Write as _;
        let (aig, values) = self.build(universals);
        let params: Vec<String> = universals
            .iter()
            .map(|&v| name(v.to_dimacs()).unwrap_or_else(|| format!("_u{}", v.to_dimacs())))
            .collect();
        let decl: String =
            params.iter().map(|p| format!("({p} Bool)")).collect::<Vec<_>>().join(" ");
        let args = params.join(" ");
        let call = |f: &str| {
            if params.is_empty() {
                f.to_string()
            } else {
                format!("({f} {args})")
            }
        };
        // an AIG literal as an SMT-LIB term: constants, inputs by their
        // parameter name, gates by a call to their helper
        let term = |lit: u64| -> String {
            if lit == 0 {
                return "false".to_string();
            }
            if lit == 1 {
                return "true".to_string();
            }
            let var = lit / 2;
            let position = usize::try_from(var - 1).expect("fits");
            let base = if position < params.len() {
                params[position].clone()
            } else {
                call(&format!("_g{var}"))
            };
            if lit & 1 == 1 {
                format!("(not {base})")
            } else {
                base
            }
        };

        let mut out = String::from("(
");
        for &(lhs, rhs0, rhs1) in aig.gates() {
            let _ = writeln!(
                out,
                "  (define-fun _g{} ({decl}) Bool (and {} {}))",
                lhs / 2,
                term(rhs0),
                term(rhs1)
            );
        }
        let mut defined: Vec<(Var, u64)> = values.into_iter().collect();
        defined.sort_unstable();
        for (var, wire) in defined {
            let Some(public) = name(var.to_dimacs()) else {
                continue;
            };
            let _ = writeln!(out, "  (define-fun {public} ({decl}) Bool {})", term(wire));
        }
        out.push_str(")\n");
        out
    }

    /// The size of the circuit this strategy compiles to, in AND
    /// gates.
    ///
    /// Not [`Strategy::size`]: the strategy is a DAG and the circuit is
    /// what a monolithic build makes of it, and the two grow very
    /// differently with prefix depth — the strategy linearly, the
    /// circuit exponentially, because a shared node is rebuilt under
    /// every set of values decided above it. The circuit is what a
    /// certificate check and an AIGER file cost, so it is the number to
    /// budget against.
    #[must_use]
    pub fn gates(&self, universals: &[Var]) -> usize {
        self.build(universals).0.gates().len()
    }

    /// Builds the strategy into a fresh AIG whose inputs are the given
    /// universal variables, and returns it together with the output wire
    /// of every variable the strategy determines.
    fn build(&self, universals: &[Var]) -> (AigBuilder, HashMap<Var, u64>) {
        let mut aig = AigBuilder::new(universals.len());
        let inputs: HashMap<Var, u64> =
            universals.iter().enumerate().map(|(i, &v)| (v, AigBuilder::input(i))).collect();
        let mut values = HashMap::new();
        let mut memo = BuildMemo::default();
        self.build_into(&mut aig, &inputs, &mut values, &mut memo);
        (aig, values)
    }

    /// The circuit counterpart of [`Strategy::evaluate`]: instead of
    /// values under one universal assignment it accumulates *wires* that
    /// compute those values under every assignment at once. The two must
    /// agree pointwise, which the fuzz harness checks by running both.
    fn build_into(
        &self,
        aig: &mut AigBuilder,
        inputs: &HashMap<Var, u64>,
        values: &mut HashMap<Var, u64>,
        memo: &mut BuildMemo,
    ) {
        // Sub-strategies are shared, and a shared node reached again
        // under the same *relevant* values computes the same wires —
        // which are already in the AIG. Relevant means the variables
        // the subtree mentions: nothing else can reach its cubes, its
        // merge bases, or its leaves, so the constants an outer
        // `Choose` committed to on the way down do not count, and it is
        // exactly those that differ between the paths into a shared
        // node. Keying on the whole value map instead finds no sharing
        // at all (measured: 0 hits in 6 690 calls) and the circuit
        // grows exponentially with depth while the strategy grows
        // linearly.
        let relevant = memo.touched(self);
        let key = (std::ptr::addr_of!(*self), values_key(&relevant, values));
        if let Some(delta) = memo.entries.get(&key) {
            for (var, wire) in delta.clone() {
                match wire {
                    Some(wire) => values.insert(var, wire),
                    None => values.remove(&var),
                };
            }
            return;
        }
        self.build_uncached(aig, inputs, values, memo);
        let delta: Delta = relevant.iter().map(|&v| (v, values.get(&v).copied())).collect();
        memo.entries.insert(key, delta);
    }

    /// Every variable the subtree mentions: what it may write, and what
    /// it may read out of the values it is handed.
    fn mentions(&self, into: &mut Vec<Var>) {
        match self {
            Strategy::Done => {}
            Strategy::Fixed { assignments, rest }
            | Strategy::Choose { constants: assignments, rest } => {
                into.extend(assignments.iter().map(|l| l.var()));
                rest.mentions(into);
            }
            Strategy::Split { cases } => {
                for (cube, sub) in cases {
                    into.extend(cube.iter().map(|l| l.var()));
                    sub.mentions(into);
                }
            }
            Strategy::Expanded { copies, rest } => {
                for (cube, rename) in copies {
                    into.extend(cube.iter().map(|l| l.var()));
                    into.extend(rename.iter().flat_map(|(&o, &c)| [o, c]));
                }
                rest.mentions(into);
            }
            Strategy::Leaf(model) => {
                into.extend(model.defined_vars());
            }
        }
    }

    fn build_uncached(
        &self,
        aig: &mut AigBuilder,
        inputs: &HashMap<Var, u64>,
        values: &mut HashMap<Var, u64>,
        memo: &mut BuildMemo,
    ) {
        match self {
            Strategy::Done => {}
            Strategy::Fixed { assignments, rest }
            | Strategy::Choose { constants: assignments, rest } => {
                for l in assignments {
                    values.insert(l.var(), u64::from(l.is_positive()));
                }
                rest.build_into(aig, inputs, values, memo);
            }
            Strategy::Split { cases } => {
                // the first case whose cube holds wins, as in `evaluate`;
                // each case is built over its own copy of the values so
                // far and the copies are muxed back together afterwards
                let mut no_earlier = 1u64;
                let mut branches: Vec<(u64, HashMap<Var, u64>)> = Vec::new();
                for (cube, sub) in cases {
                    let lits: Vec<u64> = cube
                        .iter()
                        .map(|&l| {
                            // an unknown variable makes the literal
                            // false whatever its polarity, as in
                            // `evaluate`
                            match inputs.get(&l.var()).or_else(|| values.get(&l.var())) {
                                Some(&base) => base ^ u64::from(l.is_negative()),
                                None => 0,
                            }
                        })
                        .collect();
                    let holds = aig.and_all(&lits);
                    let select = aig.and(no_earlier, holds);
                    no_earlier = aig.and(no_earlier, holds ^ 1);
                    let mut branch = values.clone();
                    sub.build_into(aig, inputs, &mut branch, memo);
                    branches.push((select, branch));
                }
                let mut defined: Vec<Var> =
                    branches.iter().flat_map(|(_, b)| b.keys().copied()).collect();
                defined.sort_unstable();
                defined.dedup();
                for var in defined {
                    // outside every cube the value is whatever held
                    // before the split (`evaluate` leaves it alone;
                    // a variable no branch inherited reads false)
                    let before = values.get(&var).copied();
                    if branches.iter().all(|(_, b)| b.get(&var).copied() == before) {
                        continue;
                    }
                    let base = before.unwrap_or(0);
                    let mut terms = vec![aig.and(no_earlier, base)];
                    for (select, branch) in &branches {
                        let value = branch.get(&var).copied().unwrap_or(base);
                        terms.push(aig.and(*select, value));
                    }
                    let merged = aig.or_all(&terms);
                    values.insert(var, merged);
                }
            }
            Strategy::Expanded { copies, rest } => {
                rest.build_into(aig, inputs, values, memo);
                let mut no_earlier = 1u64;
                let mut selected: Vec<u64> = Vec::new();
                for (cube, _) in copies {
                    let lits: Vec<u64> = cube
                        .iter()
                        .map(|&l| match inputs.get(&l.var()) {
                            Some(&wire) => wire ^ u64::from(l.is_negative()),
                            None => 0,
                        })
                        .collect();
                    let holds = aig.and_all(&lits);
                    selected.push(aig.and(no_earlier, holds));
                    no_earlier = aig.and(no_earlier, holds ^ 1);
                }
                let mut originals: Vec<Var> =
                    copies.iter().flat_map(|(_, r)| r.keys().copied()).collect();
                originals.sort_unstable();
                originals.dedup();
                let mut projected: Vec<(Var, u64)> = Vec::new();
                for var in originals {
                    let base = values.get(&var).copied().unwrap_or(0);
                    let mut terms = vec![aig.and(no_earlier, base)];
                    for (&select, (_, rename)) in selected.iter().zip(copies) {
                        let value = rename
                            .get(&var)
                            .and_then(|copy| values.get(copy).copied())
                            .unwrap_or(base);
                        terms.push(aig.and(select, value));
                    }
                    projected.push((var, aig.or_all(&terms)));
                }
                for (_, rename) in copies {
                    for copy in rename.values() {
                        values.remove(copy);
                    }
                }
                values.extend(projected);
            }
            Strategy::Leaf(model) => {
                // a leaf universal outside the outer ones reads false,
                // matching `evaluate`
                let leaf_inputs: HashMap<Var, u64> = model
                    .universals()
                    .into_iter()
                    .map(|v| {
                        let var = Lit::from_dimacs(v).var();
                        (var, inputs.get(&var).copied().unwrap_or(0))
                    })
                    .collect();
                values.extend(model.build_into(aig, &leaf_inputs));
            }
        }
    }
}

/// Verifies a composed [`Strategy`] against the original instance: the
/// strategy circuit is encoded into CNF alongside the matrix, and the
/// query asks for an assignment of the universal variables that
/// falsifies some clause. Unsatisfiable means the strategy wins
/// everywhere, which is exactly the claim a satisfiable verdict makes.
///
/// The query is issued *one clause at a time*, under assumptions that
/// falsify it, against a single solver that keeps everything it learns.
/// The disjunction over all clauses is one enormous query the solver
/// has no handle on; the individual clauses are small queries sharing
/// the expensive part — the circuit — and the learnt clauses from each
/// carry to the next. Measured on `lights3_021_0_009` (43 blocks, a
/// 98k-gate strategy): 123 s as one query, 33 s as 2023 of them.
///
/// The universal variables and the existentials the strategy leaves
/// undetermined are left free, so the check reads "for *all* universal
/// assignments and *all* values of the undetermined variables" — the
/// strong form, since a variable is only left out when the solve found
/// it irrelevant.
///
/// This is the scalable counterpart of evaluating the strategy at every
/// universal assignment, which the fuzz harness does but which is
/// hopeless on real instances (their universal blocks run to dozens of
/// variables).
#[must_use]
pub fn verify_strategy(qcnf: &QCNF, strategy: &Strategy) -> bool {
    use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};
    type SatLit = <Varisat as SatSolver>::Lit;

    let universals: Vec<Var> = qcnf
        .prefix
        .iter()
        .filter(|(q, _)| *q == QuantTy::Forall)
        .flat_map(|(_, vars)| vars.iter().copied())
        .collect();
    let built = std::time::Instant::now();
    let (aig, values) = strategy.build(&universals);
    tracing::debug!(
        nodes = strategy.size(),
        gates = aig.gates().len(),
        seconds = built.elapsed().as_secs_f64(),
        "built the strategy circuit"
    );

    let mut solver = LookupSolver::<Varisat>::default();
    let var_count = qcnf
        .prefix
        .iter()
        .flat_map(|(_, vars)| vars.iter().copied())
        .chain(qcnf.matrix.iter().flatten().map(|l| l.var()))
        .map(|v| v.as_index() + 2)
        .max()
        .unwrap_or(0);
    solver.set_var_count(var_count);

    // AIG literals into solver literals: constants through a unit-fixed
    // variable, inputs through the universal variables themselves, gates
    // through fresh variables with the usual Tseitin clauses
    let one = solver.add_variable();
    solver.add_clause(&[one]);
    let mut wires: HashMap<u64, SatLit> = HashMap::new();
    for (position, &v) in universals.iter().enumerate() {
        wires.insert(AigBuilder::input(position) / 2, solver.lookup(Lit::positive(v)));
    }
    let sat_of = |lit: u64, wires: &HashMap<u64, SatLit>| -> SatLit {
        match lit {
            0 => !one,
            1 => one,
            _ => {
                let base = wires[&(lit / 2)];
                if lit & 1 == 1 {
                    !base
                } else {
                    base
                }
            }
        }
    };
    for &(lhs, rhs0, rhs1) in aig.gates() {
        let gate = solver.add_variable();
        let (a, b) = (sat_of(rhs0, &wires), sat_of(rhs1, &wires));
        solver.add_clause(&[!gate, a]);
        solver.add_clause(&[!gate, b]);
        solver.add_clause(&[gate, !a, !b]);
        wires.insert(lhs / 2, gate);
    }
    // tie every determined existential to the wire computing it
    for (var, wire) in values {
        let value = sat_of(wire, &wires);
        let var = solver.lookup(Lit::positive(var));
        solver.add_clause(&[!var, value]);
        solver.add_clause(&[var, !value]);
    }

    // one query per clause: "this clause is falsified"
    let checked = std::time::Instant::now();
    let mut wins = true;
    let mut assumptions: Vec<SatLit> = Vec::new();
    for clause in &qcnf.matrix {
        assumptions.clear();
        assumptions.extend(clause.iter().map(|&l| !solver.lookup(l)));
        if solver
            .solve_with_assumptions(&assumptions)
            .expect("the strategy check is a plain SAT query")
        {
            wins = false;
            break;
        }
    }
    tracing::debug!(
        clauses = qcnf.matrix.len(),
        seconds = checked.elapsed().as_secs_f64(),
        wins,
        "checked the strategy"
    );
    wins
}

/// The result of an internal solve: the verdict, the refuting
/// assignment of an outermost universal block (for the ∃-loop above),
/// and a composed winning strategy when one is available.
#[derive(Clone)]
struct Outcome {
    verdict: SolverResult,
    witness: Option<Vec<Lit>>,
    strategy: Option<Rc<Strategy>>,
}

impl Outcome {
    fn verdict(verdict: SolverResult) -> Self {
        Self { verdict, witness: None, strategy: None }
    }

    fn sat(strategy: Option<Rc<Strategy>>) -> Self {
        Self { verdict: SolverResult::Satisfiable, witness: None, strategy }
    }
}

/// A memo key: a 128-bit fingerprint of the instance's canonical form
/// — the prefix in order, and the matrix as a *multiset* of clauses,
/// each with its literals sorted, combined commutatively so the clause
/// order does not matter.
///
/// Fingerprints rather than the canonical form itself, because the
/// form is as large as the instance and the recursion holds hundreds
/// of them: storing 16 bytes instead of a matrix copy is what makes
/// the memo affordable. Two distinct instances collide with
/// probability under `n^2 / 2^129`, i.e. below 1e-25 for the largest
/// tables this ever builds — many orders of magnitude below the rate
/// at which the hardware miscomputes the same answer.
type CacheKey = u128;

fn cache_key(qcnf: &QCNF) -> CacheKey {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    // two independently salted passes over the same canonical form
    let digest = |salt: u8, clause: &[i32]| {
        let mut hasher = DefaultHasher::new();
        salt.hash(&mut hasher);
        clause.hash(&mut hasher);
        hasher.finish()
    };
    let mut clauses: u128 = 0;
    let mut lits: Vec<i32> = Vec::new();
    for clause in &qcnf.matrix {
        lits.clear();
        lits.extend(clause.iter().map(|l| l.to_dimacs()));
        lits.sort_unstable();
        lits.dedup();
        let wide = u128::from(digest(0, &lits)) << 64 | u128::from(digest(1, &lits));
        // commutative, and duplicated clauses stay distinguishable
        clauses = clauses.wrapping_add(wide);
    }
    let prefix: Vec<i32> = qcnf
        .prefix
        .iter()
        .flat_map(|(q, vars)| {
            std::iter::once(if *q == QuantTy::Forall { -1 } else { 0 })
                .chain(vars.iter().map(|v| v.to_dimacs()))
        })
        .collect();
    let mut hasher = DefaultHasher::new();
    clauses.hash(&mut hasher);
    prefix.hash(&mut hasher);
    let low = hasher.finish();
    let mut hasher = DefaultHasher::new();
    2u8.hash(&mut hasher);
    clauses.hash(&mut hasher);
    prefix.hash(&mut hasher);
    u128::from(hasher.finish()) << 64 | u128::from(low)
}

/// Memo of the recursion's sub-solves. The candidate loops restrict
/// one block at a time, and different candidates of an *outer* loop
/// routinely restrict to the same inner instance — on the deepest
/// suite instance 363 of 377 sub-solves repeat one already answered —
/// so every level looks up its simplified instance before dispatching.
///
/// The keys are over *simplified, normalized* instances, which is
/// where the repeats become visible: distinct restrictions collapse
/// onto the same instance only after their units and pure literals are
/// propagated away.
///
/// Two guards keep it from costing more than it saves: the table stops
/// growing once the strategies it holds reach [`MEMO_BUDGET`] nodes,
/// and a recursion whose sub-solves simply do not repeat switches the
/// memo off rather than paying for a fingerprint per call.
#[derive(Default)]
struct Cache {
    entries: HashMap<CacheKey, Outcome>,
    stored: usize,
    probes: usize,
    hits: usize,
}

/// Strategy nodes the memo may hold before it stops growing. The
/// fingerprints themselves are 16 bytes each, so the cached strategies
/// are all that can grow.
const MEMO_BUDGET: usize = 32_000_000;

/// Probes to take before judging the hit rate, and the reciprocal of
/// the rate below which the memo switches itself off.
const MEMO_WARMUP: usize = 256;
const MEMO_MIN_RATE: usize = 8;

impl Cache {
    /// Looks the instance up, returning its key when the caller should
    /// insert the result afterwards.
    fn probe(&mut self, qcnf: &QCNF) -> (Option<Outcome>, Option<CacheKey>) {
        let cold = self.probes > MEMO_WARMUP && self.hits * MEMO_MIN_RATE < self.probes;
        if self.stored >= MEMO_BUDGET || cold {
            return (None, None);
        }
        self.probes += 1;
        let key = cache_key(qcnf);
        match self.entries.get(&key) {
            Some(hit) => {
                self.hits += 1;
                (Some(hit.clone()), None)
            }
            None => (None, Some(key)),
        }
    }

    fn insert(&mut self, key: CacheKey, outcome: &Outcome) {
        self.stored += outcome.strategy.as_ref().map_or(0, |s| s.size());
        self.entries.insert(key, outcome.clone());
    }
}

/// Solves a prenex QBF with any number of quantifier blocks.
#[must_use]
pub fn solve(qcnf: &QCNF, options: Options) -> SolverResult {
    solve_with_expansion_budget(qcnf, options, EXPANSION_BUDGET)
}

/// Solves with an explicit ∀-expansion budget; `0` disables expansion
/// (used by the differential tests to exercise the CEGAR loops).
#[must_use]
pub fn solve_with_expansion_budget(qcnf: &QCNF, options: Options, budget: usize) -> SolverResult {
    solve_certified(qcnf, options, budget).0
}

/// Solves and, on a satisfiable verdict, returns a winning existential
/// strategy when the pipeline could compose one. Strategy composition
/// does not yet invert ∀-expansion (the expanded copies would have to
/// be folded back into a multiplexer over the expanded block), so an
/// instance that needed an expansion answers `None`.
#[must_use]
pub fn solve_certified(
    qcnf: &QCNF,
    options: Options,
    budget: usize,
) -> (SolverResult, Option<Rc<Strategy>>) {
    // ∀-expansion is a *global* transformation: it depends on the
    // instance, not on any candidate. Running it once here, to a
    // fixpoint interleaved with simplification, is the difference
    // between transforming the instance and transforming it again for
    // every candidate of every enclosing loop — with `expand` left
    // inside the recursion, deep prefixes (a 22-block `lights3`, the
    // depth-6 arbiter) never reached a single leaf solve because each
    // level redid the matrix doubling.
    let mut current = normalized(qcnf);
    let mut forced: Vec<Lit> = Vec::new();
    // one entry per expansion performed, outermost first; each undoes
    // its own renaming when the strategy is composed back up
    let mut inversions: Vec<Copies> = Vec::new();
    let mut floor = max_var(qcnf) + 1;
    loop {
        if current.prefix.len() <= 2 {
            break;
        }
        let Some((reduced, assigned)) = simplify(&current) else {
            return (SolverResult::Unsatisfiable, None);
        };
        forced.extend(assigned);
        if reduced.matrix.is_empty() {
            let strategy = invert(&inversions, Rc::new(Strategy::Done));
            return (SolverResult::Satisfiable, Some(wrap(forced, Some(strategy)).unwrap()));
        }
        current = normalized(&reduced);
        let Some(block) = expandable_block(&current, budget) else {
            break;
        };
        let (expanded, copies) = expand_universal_block(&current, block, floor);
        floor = max_var(&expanded) + 1;
        inversions.push(copies);
        current = normalized(&expanded);
    }
    let outcome = solve_normalized(&current, options, &mut Cache::default());
    let strategy = wrap(forced, outcome.strategy.map(|rest| invert(&inversions, rest)));
    (outcome.verdict, strategy)
}

/// Undoes the expansions, innermost first, around a strategy for the
/// fully expanded instance.
fn invert(inversions: &[Copies], mut strategy: Rc<Strategy>) -> Rc<Strategy> {
    for copies in inversions.iter().rev() {
        strategy = Rc::new(Strategy::Expanded { copies: copies.clone(), rest: strategy });
    }
    strategy
}

/// The largest variable the instance declares or mentions, in DIMACS
/// numbering.
fn max_var(qcnf: &QCNF) -> i32 {
    qcnf.prefix
        .iter()
        .flat_map(|(_, vars)| vars.iter().copied())
        .chain(qcnf.matrix.iter().flatten().map(|l| l.var()))
        .map(Var::to_dimacs)
        .max()
        .unwrap_or(0)
}

/// The internal solve additionally returns, on an unsatisfiable
/// verdict whose outermost block is universal, the refuting assignment
/// of that block — the expansion witness of the ∃-loop one level up
/// (already computed by the ∀-loop and by the 2QBF core; threading it
/// upgrades deep recursion from blocking-only to strong refinements).
fn solve_normalized(qcnf: &QCNF, options: Options, cache: &mut Cache) -> Outcome {
    // Restrictions and expansions manufacture units and pure literals by
    // the hundred, so simplify before dispatching; without this every
    // recursion level rediscovers them. The 2QBF core does its own
    // preprocessing (and owns the certified path), so leaves are left
    // alone.
    let simplified;
    let mut forced: Vec<Lit> = Vec::new();
    let qcnf = if qcnf.prefix.len() > 2 {
        let Some((reduced, assigned)) = simplify(qcnf) else {
            return Outcome::verdict(SolverResult::Unsatisfiable);
        };
        forced.extend(assigned);
        if reduced.matrix.is_empty() {
            return Outcome::sat(Some(Rc::new(Strategy::Fixed {
                assignments: forced,
                rest: Rc::new(Strategy::Done),
            })));
        }
        simplified = normalized(&reduced);
        &simplified
    } else {
        qcnf
    };
    if qcnf.prefix.len() <= 2 {
        #[cfg(feature = "probe")]
        {
            let n = LEAF_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if n % 2048 == 0 {
                eprintln!(
                    "probe: {n} leaf solves, {} abstraction rounds",
                    ROUNDS.load(std::sync::atomic::Ordering::Relaxed)
                );
            }
            LEAF_VARS.fetch_add(
                qcnf.prefix.iter().map(|(_, v)| v.len()).sum::<usize>(),
                std::sync::atomic::Ordering::Relaxed,
            );
            LEAF_CLAUSES.fetch_add(qcnf.matrix.len(), std::sync::atomic::Ordering::Relaxed);
        }
        let mut solver = IncDet::from_qcnf_with_options(qcnf, options);
        let verdict = solver.solve();
        let witness = if verdict == SolverResult::Unsatisfiable
            && matches!(qcnf.prefix.first(), Some((QuantTy::Forall, _)))
        {
            solver.unsat_witness_candidate().map(|w| w.into_iter().map(Lit::from_dimacs).collect())
        } else {
            None
        };
        let strategy = (verdict == SolverResult::Satisfiable)
            .then(|| Rc::new(Strategy::Leaf(Rc::new(solver.skolem_model()))));
        return Outcome { verdict, witness, strategy: wrap(forced, strategy) };
    }
    let (hit, key) = cache.probe(qcnf);
    let inner = if let Some(hit) = hit {
        hit
    } else {
        let inner = match qcnf.prefix[0].0 {
            QuantTy::Exists => expansion_loop(qcnf, options, cache),
            QuantTy::Forall => forall_loop(qcnf, options, cache),
        };
        if let Some(key) = key {
            cache.insert(key, &inner);
        }
        inner
    };
    Outcome { strategy: wrap(forced, inner.strategy), ..inner }
}

/// Prefixes a strategy with the literals a simplification pass forced.
fn wrap(forced: Vec<Lit>, strategy: Option<Rc<Strategy>>) -> Option<Rc<Strategy>> {
    let strategy = strategy?;
    if forced.is_empty() {
        return Some(strategy);
    }
    Some(Rc::new(Strategy::Fixed { assignments: forced, rest: strategy }))
}

/// The dual candidate loop at a ∀-outermost block: search for a
/// refuting outer assignment; every answered candidate is blocked.
/// (Negating the matrix instead would cascade Tseitin gates through the
/// recursion and blow up; the dual loop keeps the matrix fixed. Strong
/// dual refinements would need regions of answered candidates — future
/// work, the weak blocking clause keeps the loop total.)
fn forall_loop(qcnf: &QCNF, options: Options, cache: &mut Cache) -> Outcome {
    use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};

    let outer: Vec<Var> = qcnf.prefix[0].1.clone();
    let mut alpha = LookupSolver::<Varisat>::default();
    alpha.set_var_count(
        outer.iter().map(|v| usize::try_from(v.to_dimacs()).expect("fits")).max().unwrap_or(0) + 1,
    );
    // force the solver to materialize every outer variable so models
    // cover them
    for &v in &outer {
        let l = alpha.lookup(Lit::positive(v));
        alpha.add_clause(&[l, !l]);
    }
    // one sub-strategy per answered candidate; the loop only succeeds
    // once every assignment of the block has been enumerated, so the
    // cases partition it
    let mut cases: Vec<(Vec<Lit>, Rc<Strategy>)> = Vec::new();
    let mut composable = true;
    let mut rounds = 0u32;
    loop {
        rounds += 1;
        #[cfg(feature = "probe")]
        ROUNDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if rounds > 4096 {
            tracing::warn!("universal candidate budget exhausted");
            return Outcome::verdict(SolverResult::Unknown);
        }
        if !alpha.solve().unwrap() {
            // every universal choice is answered
            return Outcome::sat(composable.then(|| Rc::new(Strategy::Split { cases })));
        }
        let model: HashMap<Var, bool> = alpha
            .orig_model()
            .expect("model after sat")
            .into_iter()
            .map(|l| (l.var(), l.is_positive()))
            .collect();
        let candidate: Vec<Lit> = outer
            .iter()
            .map(|&v| {
                if model.get(&v).copied().unwrap_or(false) {
                    Lit::positive(v)
                } else {
                    Lit::negative(v)
                }
            })
            .collect();
        let restricted = normalized(&restrict(qcnf, &candidate, 1));
        let outcome = solve_normalized(&restricted, options, cache);
        match outcome.verdict {
            // the candidate is a winning universal prefix move — and the
            // expansion witness for the ∃-loop above
            SolverResult::Unsatisfiable => {
                return Outcome {
                    verdict: SolverResult::Unsatisfiable,
                    witness: Some(candidate),
                    strategy: None,
                }
            }
            SolverResult::Unknown => return Outcome::verdict(SolverResult::Unknown),
            SolverResult::Satisfiable => {
                match outcome.strategy {
                    Some(sub) => cases.push((candidate.clone(), sub)),
                    None => composable = false,
                }
                let blocking: Vec<_> = candidate.iter().map(|&l| alpha.lookup(!l)).collect();
                alpha.add_clause(&blocking);
            }
        }
    }
}

/// Simplifies a *normalized* instance to a fixpoint with the standard
/// sound QBF rules, and returns `None` when the instance is refuted
/// outright (a clause reduces to empty). An empty matrix means
/// satisfiable.
///
/// * **Universal reduction**: a universal literal with no existential
///   literal of a later block in its clause is dropped — the ∀ player
///   moves last on it, so it can always falsify it.
/// * **Unit propagation**: after universal reduction every unit clause
///   is existential and forces its literal.
/// * **Pure literals**: an existential occurring in one polarity only
///   takes that polarity (nothing is harmed); a universal occurring in
///   one polarity only takes the *opposite* one (the ∀ player never
///   benefits from satisfying clauses).
///
/// The alternation front-end needs this because [`restrict`] and
/// [`expand_universal_block`] manufacture units and pure literals by
/// the hundred — a restriction fixes a whole block — and without a
/// simplification pass every recursion level rediscovers them from
/// scratch.
fn simplify(qcnf: &QCNF) -> Option<(QCNF, Vec<Lit>)> {
    let mut prefix = qcnf.prefix.clone();
    let mut matrix = qcnf.matrix.clone();
    // the existential literals the pass fixes, in application order:
    // a composed strategy replays them as constants (guessing them
    // afterwards from occurrence patterns is wrong once the fixpoint
    // cascades — the differential checker caught exactly that)
    let mut assigned_existentials: Vec<Lit> = Vec::new();
    loop {
        let mut block_of: HashMap<Var, (usize, QuantTy)> = HashMap::new();
        for (block, (quant, vars)) in prefix.iter().enumerate() {
            for &v in vars {
                block_of.insert(v, (block, *quant));
            }
        }
        let universal = |l: &Lit| matches!(block_of.get(&l.var()), Some((_, QuantTy::Forall)));
        let block = |l: &Lit| block_of.get(&l.var()).map_or(0, |&(b, _)| b);

        // clause-local rules: duplicates, tautologies, universal reduction
        let mut changed = false;
        let mut reduced: Vec<Vec<Lit>> = Vec::with_capacity(matrix.len());
        for clause in &matrix {
            let mut lits = clause.clone();
            lits.sort_unstable_by_key(|l| l.to_dimacs());
            lits.dedup();
            if lits.len() != clause.len() {
                changed = true;
            }
            if lits.iter().any(|l| lits.contains(&!*l)) {
                changed = true;
                continue;
            }
            let innermost_existential = lits.iter().filter(|l| !universal(l)).map(block).max();
            let before = lits.len();
            match innermost_existential {
                Some(bound) => lits.retain(|l| !universal(l) || block(l) < bound),
                None => lits.clear(),
            }
            if lits.len() != before {
                changed = true;
            }
            if lits.is_empty() {
                return None;
            }
            reduced.push(lits);
        }
        matrix = reduced;
        if matrix.is_empty() {
            break;
        }

        // forced literals: existential units, then pure literals
        let mut forced: HashSet<Lit> =
            matrix.iter().filter(|clause| clause.len() == 1).map(|clause| clause[0]).collect();
        if forced.iter().any(|l| forced.contains(&!*l)) {
            return None;
        }
        if forced.is_empty() {
            let mut seen: HashSet<Lit> = HashSet::new();
            for clause in &matrix {
                seen.extend(clause.iter().copied());
            }
            for &lit in &seen {
                if seen.contains(&!lit) {
                    continue;
                }
                // the existential takes the polarity it occurs in, the
                // universal the opposite one
                forced.insert(if universal(&lit) { !lit } else { lit });
            }
        }
        if forced.is_empty() {
            if !changed {
                break;
            }
            continue;
        }

        let mut next: Vec<Vec<Lit>> = Vec::with_capacity(matrix.len());
        for clause in &matrix {
            if clause.iter().any(|l| forced.contains(l)) {
                continue;
            }
            let lits: Vec<Lit> =
                clause.iter().copied().filter(|l| !forced.contains(&!*l)).collect();
            if lits.is_empty() {
                return None;
            }
            next.push(lits);
        }
        matrix = next;
        assigned_existentials.extend(forced.iter().filter(|l| !universal(l)));
        let assigned: HashSet<Var> = forced.iter().map(|l| l.var()).collect();
        for (_, vars) in &mut prefix {
            vars.retain(|v| !assigned.contains(v));
        }
        if matrix.is_empty() {
            break;
        }
    }
    // Variables that no longer occur are irrelevant: an existential can
    // take any value, and a universal cannot influence anything. Keeping
    // them would make the candidate loops enumerate over them (universal
    // reduction and clause deletion strand them by the dozen).
    let occurring: HashSet<Var> = matrix.iter().flatten().map(|l| l.var()).collect();
    for (_, vars) in &mut prefix {
        vars.retain(|v| occurring.contains(v));
    }
    Some((QCNF { prefix, matrix }, assigned_existentials))
}

/// The *innermost* universal block, if enumerating it fits the budget.
///
/// Only the innermost block is worth expanding: expansion copies
/// everything bound after the block, so expanding an outer block
/// multiplies every remaining block by `2^|Y|` — the prefix loses one
/// alternation but the survivors become far too wide for the CEGAR
/// loops (the differential fuzz caught exactly this as instances that
/// solve directly but exhaust the budget after expanding block 0).
/// At the innermost block only the final existential block is copied,
/// and a three-block prefix collapses to plain SAT.
fn expandable_block(qcnf: &QCNF, budget: usize) -> Option<usize> {
    if budget == 0 {
        return None;
    }
    let (block, vars) = qcnf
        .prefix
        .iter()
        .enumerate()
        .filter(|(_, (quant, _))| *quant == QuantTy::Forall)
        .next_back()
        .map(|(block, (_, vars))| (block, vars))?;
    if vars.len() > MAX_EXPANDED_BLOCK {
        return None;
    }
    // Only an expansion that *collapses* the prefix is worth doing: the
    // result goes straight to the 2QBF core, which is what the budget
    // pays for. A speculative one — leaving more than two blocks —
    // hands its multiplied matrix back to the loops, which pay per
    // clause many times over, and on a deep prefix the fixpoint
    // performs one per remaining ∀ block so the growth compounds. Each
    // step passes a per-step budget while the product does not:
    // measured on the reactive arbiter at depth 8, 245 clauses grew to
    // 46 602 across the fixpoint and the run took 22 s, against 0.05 s
    // for the same instance solved by the loops alone.
    if qcnf.prefix.len() > 3 {
        return None;
    }
    let copies = 1usize << vars.len();
    let copied_vars: usize =
        qcnf.prefix[block + 1..].iter().map(|(_, vars)| vars.len()).sum::<usize>();
    let clauses = copies.checked_mul(qcnf.matrix.len())?;
    let fresh = copies.checked_mul(copied_vars)?;
    (clauses <= budget && fresh <= budget).then_some(block)
}

/// ∀-expansion of one universal block: the block is replaced by a
/// conjunction of copies, one per assignment of its variables, with
/// fresh copies of every variable bound after it (copies of the same
/// original block merge into one block, preserving the quantifier
/// order). Clauses satisfied by an assignment are dropped, falsified
/// literals deleted, and clauses over neither the block nor anything
/// after it are kept once.
///
/// Soundness: the conjunct of copy `y` mentions only copy-`y`
/// variables, so a winning strategy for the expansion projects back to
/// the original by fixing the other copies' universals arbitrarily —
/// the cross-copy dependencies the merged blocks allow are never
/// needed.
///
/// Alongside the expanded instance it returns the [`Copies`] that undo
/// the transformation on a strategy, and fresh variables start above
/// `floor` so the copies can never collide with a variable of the
/// *original* instance that simplification dropped along the way.
fn expand_universal_block(qcnf: &QCNF, block: usize, floor: i32) -> (QCNF, Copies) {
    let ys: Vec<Var> = qcnf.prefix[block].1.clone();
    let after: Vec<(QuantTy, Vec<Var>)> = qcnf.prefix[block + 1..].to_vec();
    let after_set: HashSet<Var> = after.iter().flat_map(|(_, vars)| vars.iter().copied()).collect();
    let y_set: HashSet<Var> = ys.iter().copied().collect();
    let declared = qcnf.prefix.iter().flat_map(|(_, vars)| vars.iter()).map(|v| v.to_dimacs());
    let mentioned = qcnf.matrix.iter().flatten().map(|l| l.var().to_dimacs());
    let mut next = declared.chain(mentioned).max().unwrap_or(0).max(floor - 1) + 1;

    let mut copies: Copies = Vec::new();
    let mut copied_blocks: Vec<Vec<Var>> = vec![Vec::new(); after.len()];
    let mut matrix: Vec<Vec<Lit>> = Vec::new();
    for point in 0..1u64 << ys.len() {
        // the assignment of this copy, and fresh names for everything
        // bound after the expanded block
        let cube: Vec<Lit> = ys
            .iter()
            .enumerate()
            .map(|(i, &v)| if point >> i & 1 == 1 { Lit::positive(v) } else { Lit::negative(v) })
            .collect();
        let assigned: HashSet<Lit> = cube.iter().copied().collect();
        let mut rename: HashMap<Var, Var> = HashMap::new();
        for (index, (_, vars)) in after.iter().enumerate() {
            for &v in vars {
                let fresh = Var::from_dimacs(next);
                next += 1;
                rename.insert(v, fresh);
                copied_blocks[index].push(fresh);
            }
        }
        for clause in &qcnf.matrix {
            if clause.iter().any(|l| assigned.contains(l)) {
                continue;
            }
            let touches_copy =
                clause.iter().any(|l| y_set.contains(&l.var()) || after_set.contains(&l.var()));
            if !touches_copy && point > 0 {
                // independent of this expansion; kept once
                continue;
            }
            let lits: Vec<Lit> = clause
                .iter()
                .filter(|l| !assigned.contains(&!**l))
                .map(|&l| match rename.get(&l.var()) {
                    Some(&fresh) => {
                        let lit = Lit::positive(fresh);
                        if l.is_positive() {
                            lit
                        } else {
                            !lit
                        }
                    }
                    None => l,
                })
                .collect();
            matrix.push(lits);
        }
        copies.push((cube, rename));
    }

    let mut prefix: Vec<(QuantTy, Vec<Var>)> = qcnf.prefix[..block].to_vec();
    for ((quant, _), vars) in after.iter().zip(copied_blocks) {
        prefix.push((*quant, vars));
    }
    (QCNF { prefix, matrix }, copies)
}

/// Drops empty blocks, merges adjacent blocks of the same quantifier,
/// and binds free variables to an outermost existential block.
fn normalized(qcnf: &QCNF) -> QCNF {
    let mut prefix: Vec<(QuantTy, Vec<Var>)> = Vec::new();
    let declared: HashSet<Var> =
        qcnf.prefix.iter().flat_map(|(_, vars)| vars.iter().copied()).collect();
    let mut free: Vec<Var> = qcnf
        .matrix
        .iter()
        .flatten()
        .map(|l| l.var())
        .filter(|v| !declared.contains(v))
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();
    free.sort_unstable_by_key(|v| v.to_dimacs());
    if !free.is_empty() {
        prefix.push((QuantTy::Exists, free));
    }
    for (quant, vars) in &qcnf.prefix {
        if vars.is_empty() {
            continue;
        }
        match prefix.last_mut() {
            Some((q, block)) if q == quant => block.extend(vars.iter().copied()),
            _ => prefix.push((*quant, vars.clone())),
        }
    }
    QCNF { prefix, matrix: qcnf.matrix.clone() }
}

/// CEGAR at the outermost existential block of a normalized prefix with
/// at least three blocks.
// the loop reads best as one piece: oracle setup, candidates, refinements
#[allow(clippy::too_many_lines)]
fn expansion_loop(qcnf: &QCNF, options: Options, cache: &mut Cache) -> Outcome {
    use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};

    let outer: Vec<Var> = qcnf.prefix[0].1.clone();
    let outer_set: HashSet<Var> = outer.iter().copied().collect();
    let rest = &qcnf.prefix[1..];

    // the persistent 2QBF oracle for a three-block prefix ∃X ∀Y ∃Z:
    // Y universal, Z and X existential, X assumed per candidate
    let oracle = if rest.len() == 2 {
        let mut solver = IncrementalSolver::new(options);
        for v in &rest[0].1 {
            solver.declare_universal(u32::try_from(v.to_dimacs()).expect("fits"));
        }
        for v in outer.iter().chain(&rest[1].1) {
            solver.declare_existential(u32::try_from(v.to_dimacs()).expect("fits"));
        }
        for clause in &qcnf.matrix {
            let lits: Vec<i32> = clause.iter().map(|l| l.to_dimacs()).collect();
            solver.add_clause(&lits);
        }
        Some(solver)
    } else {
        None
    };
    let mut oracle = oracle;

    // the abstraction over X: seeded with the clauses that mention only
    // outer variables (they must hold under any strategy). Every
    // refinement introduces fresh copy variables, so the lookup table
    // grows by one round's worth of variables up front each iteration.
    let mut alpha = LookupSolver::<Varisat>::default();
    let total_vars = usize::try_from(
        qcnf.prefix
            .iter()
            .flat_map(|(_, vars)| vars.iter())
            .map(|v| v.to_dimacs())
            .max()
            .unwrap_or(0),
    )
    .expect("fits");
    let mut next_copy_var = i32::try_from(total_vars).expect("fits") + 1;
    alpha.set_var_count(total_vars + 2);
    for clause in &qcnf.matrix {
        if clause.iter().all(|l| outer_set.contains(&l.var())) {
            let lits: Vec<_> = clause.iter().map(|&l| alpha.lookup(l)).collect();
            alpha.add_clause(&lits);
        }
    }
    // seed with one existentially relaxed matrix copy: candidates then
    // satisfy the necessary condition ∃(rest) matrix before any oracle
    // call is spent
    let mut added_literals = 0usize;
    alpha.set_var_count(2 * total_vars + 2);
    add_relaxed_copy(
        &mut alpha,
        qcnf,
        &outer_set,
        &HashSet::new(),
        &mut next_copy_var,
        &mut added_literals,
    );

    // expansion can blow up on hard instances (the known weakness of
    // the algorithm family); give up honestly instead of exhausting
    // memory
    let mut rounds = 0u32;
    loop {
        rounds += 1;
        #[cfg(feature = "probe")]
        ROUNDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if rounds > 4096 || added_literals > 8_000_000 {
            tracing::warn!("expansion budget exhausted after {rounds} refinements");
            return Outcome::verdict(SolverResult::Unknown);
        }
        if !alpha.solve().unwrap() {
            return Outcome::verdict(SolverResult::Unsatisfiable);
        }
        let model: HashMap<Var, bool> = alpha
            .orig_model()
            .expect("model after sat")
            .into_iter()
            .map(|l| (l.var(), l.is_positive()))
            .collect();
        let candidate: Vec<Lit> = outer
            .iter()
            .map(|&v| {
                if model.get(&v).copied().unwrap_or(false) {
                    Lit::positive(v)
                } else {
                    Lit::negative(v)
                }
            })
            .collect();

        // ask the remainder under the candidate
        // room for one refinement round of fresh copies
        alpha.set_var_count(usize::try_from(next_copy_var).expect("fits") + total_vars + 2);

        let (verdict, witness, sub_strategy) = match &mut oracle {
            Some(solver) => {
                let assumptions: Vec<i32> = candidate.iter().map(|l| l.to_dimacs()).collect();
                let verdict = solver.solve_with_assumptions(&assumptions);
                // any universal assignment is a sound expansion point (a
                // winning outer choice must answer it), so the unverified
                // candidate serves; the blocking clause below guarantees
                // progress either way
                let witness = solver
                    .universal_witness_candidate()
                    .map(|w| w.into_iter().map(Lit::from_dimacs).collect::<Vec<_>>());
                let strategy = (verdict == SolverResult::Satisfiable)
                    .then(|| solver.skolem_model().map(|m| Rc::new(Strategy::Leaf(Rc::new(m)))))
                    .flatten();
                (verdict, witness, strategy)
            }
            None => {
                // the recursion hands back the refuting assignment of the
                // block below, which is exactly this loop's expansion
                // witness
                let restricted = restrict(qcnf, &candidate, 1);
                let outcome = solve_normalized(&normalized(&restricted), options, cache);
                (outcome.verdict, outcome.witness, outcome.strategy)
            }
        };
        match verdict {
            SolverResult::Satisfiable => {
                // this candidate wins: it commits the outer block to
                // constants, the sub-strategy handles the rest
                return Outcome::sat(
                    sub_strategy.map(|rest| {
                        Rc::new(Strategy::Choose { constants: candidate, rest })
                    }),
                );
            }
            SolverResult::Unknown => return Outcome::verdict(SolverResult::Unknown),
            SolverResult::Unsatisfiable => {}
        }

        // the oracle refuted this candidate: excluding it is always
        // sound and guarantees progress
        let blocking: Vec<_> = candidate.iter().map(|&l| alpha.lookup(!l)).collect();
        alpha.add_clause(&blocking);

        if let Some(universal) = witness {
            // strong refinement: the expansion matrix[Y := Y*] over a
            // fresh copy of every non-outer variable
            let assigned: HashSet<Lit> = universal.iter().copied().collect();
            if add_relaxed_copy(
                &mut alpha,
                qcnf,
                &outer_set,
                &assigned,
                &mut next_copy_var,
                &mut added_literals,
            ) {
                // some clause is falsified by the witness alone: no
                // outer choice can answer it
                return Outcome::verdict(SolverResult::Unsatisfiable);
            }
        }
    }
}

/// Adds one copy of the matrix restricted by `assigned` to the
/// abstraction: outer literals stay shared, every other variable gets a
/// fresh (existentially relaxed) copy. Returns `true` if an empty
/// clause was added (the restriction alone falsifies a clause).
fn add_relaxed_copy(
    alpha: &mut crate::sat::LookupSolver<crate::sat::varisat::Varisat>,
    qcnf: &QCNF,
    outer_set: &HashSet<Var>,
    assigned: &HashSet<Lit>,
    next_copy_var: &mut i32,
    added_literals: &mut usize,
) -> bool {
    use crate::sat::SatSolver;
    let mut rename: HashMap<Var, i32> = HashMap::new();
    let mut empty_added = false;
    for clause in &qcnf.matrix {
        if clause.iter().any(|l| assigned.contains(l)) {
            continue;
        }
        let mut lits: Vec<_> = Vec::new();
        for &l in clause {
            if assigned.contains(&!l) {
                continue;
            }
            let mapped = if outer_set.contains(&l.var()) {
                l
            } else {
                let raw = *rename.entry(l.var()).or_insert_with(|| {
                    let fresh = *next_copy_var;
                    *next_copy_var += 1;
                    fresh
                });
                let lit = Lit::from_dimacs(raw);
                if l.is_positive() {
                    lit
                } else {
                    !lit
                }
            };
            lits.push(alpha.lookup(mapped));
        }
        if lits.is_empty() {
            empty_added = true;
        }
        *added_literals += lits.len() + 1;
        alpha.add_clause(&lits);
    }
    empty_added
}

/// The instance restricted by the given outer-block assignment: satisfied
/// clauses dropped, falsified literals deleted, the first `blocks` prefix
/// blocks removed.
fn restrict(qcnf: &QCNF, assignment: &[Lit], blocks: usize) -> QCNF {
    let assigned: HashSet<Lit> = assignment.iter().copied().collect();
    let matrix: Vec<Vec<Lit>> = qcnf
        .matrix
        .iter()
        .filter(|clause| !clause.iter().any(|l| assigned.contains(l)))
        .map(|clause| clause.iter().copied().filter(|l| !assigned.contains(&!*l)).collect())
        .collect();
    QCNF { prefix: qcnf.prefix[blocks..].to_vec(), matrix }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::qcnf::strategy;
    use proptest::prelude::*;

    static STRATEGIES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    static SAT_RESULTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    /// Checks both dispatch paths: with ∀-expansion enabled (the
    /// production default, which the small generated blocks always
    /// trigger) and with it disabled, so the CEGAR loops stay covered.
    /// Every composed strategy is verified exhaustively.
    fn check(qcnf: &QCNF) -> Result<(), TestCaseError> {
        let expected = qcnf.brute_force();
        for budget in [EXPANSION_BUDGET, 0] {
            let (actual, strategy) = solve_certified(qcnf, Options::default(), budget);
            prop_assert_eq!(
                actual,
                expected,
                "alternation solver (expansion budget {}) disagrees on:\n{}",
                budget,
                qcnf
            );
            if actual == SolverResult::Satisfiable {
                SAT_RESULTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if let Some(strategy) = strategy {
                    STRATEGIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    check_strategy(qcnf, &strategy)?;
                    // the same claim, checked through the circuit
                    // encoding instead of pointwise evaluation: a
                    // disagreement is a bug in whichever of the two is
                    // wrong, and only the circuit scales to real
                    // instances
                    prop_assert!(
                        verify_strategy(qcnf, &strategy),
                        "the SAT check rejects a strategy the exhaustive check accepts on:\n{}\nstrategy: {:?}",
                        qcnf,
                        strategy
                    );
                    check_circuit(qcnf, &strategy)?;
                }
            } else {
                prop_assert!(
                    strategy.is_none(),
                    "a strategy was produced for an unsatisfiable instance:\n{}",
                    qcnf
                );
            }
            #[cfg(feature = "probe")]
            {
                use std::sync::atomic::Ordering::Relaxed;
                eprintln!(
                    "strategies {} / {} satisfiable",
                    STRATEGIES.load(Relaxed),
                    SAT_RESULTS.load(Relaxed)
                );
            }
        }
        Ok(())
    }

    /// The emitted strategy circuit must compute what
    /// [`super::Strategy::evaluate`] prescribes. This goes through the
    /// rendered AIGER text — parsed and simulated here by a few lines
    /// that share nothing with the emitter — so it also covers the
    /// rendering, which the SAT check bypasses.
    fn check_circuit(qcnf: &QCNF, strategy: &super::Strategy) -> Result<(), TestCaseError> {
        let universals: Vec<Var> = qcnf
            .prefix
            .iter()
            .filter(|(q, _)| *q == QuantTy::Forall)
            .flat_map(|(_, vars)| vars.iter().copied())
            .collect();
        let text = strategy.to_aiger(&universals, &|_| None);
        for point in 0..1u32 << universals.len() {
            let bits: Vec<bool> = (0..universals.len()).map(|i| point >> i & 1 == 1).collect();
            let outputs = simulate(&text, &bits);
            let assignment: Vec<i32> = universals
                .iter()
                .zip(&bits)
                .map(|(v, &b)| if b { v.to_dimacs() } else { -v.to_dimacs() })
                .collect();
            let mut expected: HashMap<i32, bool> = HashMap::new();
            strategy.evaluate(&assignment, &mut expected);
            // the SMT-LIB rendering of the same AIG must agree too
            let names = |v: i32| Some(format!("v{v}"));
            let smt = strategy.to_smtlib(&universals, &names);
            let bound: Vec<(String, bool)> = universals
                .iter()
                .zip(&bits)
                .map(|(v, &b)| (format!("v{}", v.to_dimacs()), b))
                .collect();
            let interpreted = interpret(&smt, &bound);
            for (var, value) in &expected {
                prop_assert_eq!(
                    interpreted.get(&format!("v{var}")),
                    Some(value),
                    "the SMT-LIB model disagrees on variable {} at {:?} on:\n{}\n{}",
                    var,
                    &assignment,
                    qcnf,
                    smt
                );
            }
            for (var, value) in &expected {
                prop_assert_eq!(
                    outputs.get(var),
                    Some(value),
                    "strategy circuit disagrees on variable {} at {:?} on:\n{}\ncircuit:\n{}",
                    var,
                    &assignment,
                    qcnf,
                    text
                );
            }
        }
        Ok(())
    }

    /// Evaluates the SMT-LIB rendering of a strategy under one
    /// assignment of the universals, returning the value of every
    /// publicly defined variable. A tiny reader for the shape the
    /// emitter produces — `and`, `not`, constants, parameters, and
    /// calls to earlier definitions — so the check is independent of the
    /// emitter's own bookkeeping.
    fn interpret(text: &str, params: &[(String, bool)]) -> HashMap<String, bool> {
        let mut defs: HashMap<String, bool> = params.iter().cloned().collect();
        for line in text.lines() {
            let line = line.trim();
            let Some(rest) = line.strip_prefix("(define-fun ") else {
                continue;
            };
            let (name, rest) = rest.split_once(' ').expect("a name");
            // the parameter list is fixed and already bound; the body is
            // whatever follows it, minus the trailing paren of the form
            let body = rest
                .split_once(") Bool ")
                .expect("a parameter list and a body")
                .1
                .strip_suffix(')')
                .expect("a closing paren")
                .trim();
            let mut tokens = body
                .replace('(', " ( ")
                .replace(')', " ) ")
                .split_whitespace()
                .map(str::to_string)
                .collect::<Vec<_>>()
                .into_iter()
                .peekable();
            let value = eval_term(&mut tokens, &defs);
            defs.insert(name.to_string(), value);
        }
        defs
    }

    /// One term of the emitter's grammar.
    fn eval_term(
        tokens: &mut std::iter::Peekable<std::vec::IntoIter<String>>,
        defs: &HashMap<String, bool>,
    ) -> bool {
        let token = tokens.next().expect("a term");
        if token != "(" {
            return match token.as_str() {
                "false" => false,
                "true" => true,
                name => *defs.get(name).expect("a bound name"),
            };
        }
        let head = tokens.next().expect("an application head");
        let mut value = match head.as_str() {
            "not" => !eval_term(tokens, defs),
            "and" => {
                let mut all = true;
                while tokens.peek().is_some_and(|t| t != ")") {
                    all &= eval_term(tokens, defs);
                }
                all
            }
            // a call to an earlier definition: its arguments are always
            // the full parameter list, so the stored value applies
            name => {
                let stored = *defs.get(name).expect("a defined function");
                while tokens.peek().is_some_and(|t| t != ")") {
                    let _ = tokens.next();
                }
                stored
            }
        };
        // `and` may have stopped early on a false conjunct
        while tokens.peek().is_some_and(|t| t != ")") {
            value &= eval_term(tokens, defs);
        }
        assert_eq!(tokens.next().as_deref(), Some(")"), "unbalanced term");
        value
    }

    /// Simulates an ASCII AIGER combinational circuit, returning the
    /// value of every output indexed by the DIMACS variable in its
    /// symbol-table name.
    fn simulate(text: &str, inputs: &[bool]) -> HashMap<i32, bool> {
        let mut lines = text.lines();
        let header: Vec<usize> = lines
            .next()
            .expect("a header")
            .split_whitespace()
            .skip(1)
            .map(|f| f.parse().expect("a numeric header field"))
            .collect();
        let (max_var, num_inputs, num_outputs, num_ands) =
            (header[0], header[1], header[3], header[4]);
        // index 0 stays false, so literal 0 reads false and literal 1 true
        let mut values = vec![false; max_var + 1];
        let read = |line: Option<&str>| -> usize {
            line.expect("a literal line").trim().parse().expect("a numeric literal")
        };
        for &input in inputs.iter().take(num_inputs) {
            let lit = read(lines.next());
            values[lit / 2] = input;
        }
        let outputs: Vec<usize> = (0..num_outputs).map(|_| read(lines.next())).collect();
        let truth = |lit: usize, values: &[bool]| values[lit / 2] ^ (lit & 1 == 1);
        for _ in 0..num_ands {
            let gate: Vec<usize> = lines
                .next()
                .expect("an and line")
                .split_whitespace()
                .map(|f| f.parse().expect("a numeric literal"))
                .collect();
            values[gate[0] / 2] = truth(gate[1], &values) && truth(gate[2], &values);
        }
        // the symbol table names each output by its DIMACS variable
        let mut named = HashMap::new();
        for line in lines {
            let Some(rest) = line.strip_prefix('o') else {
                continue;
            };
            let (position, name) = rest.split_once(' ').expect("a named output");
            let position: usize = position.parse().expect("an output position");
            named.insert(name.parse().expect("a DIMACS name"), truth(outputs[position], &values));
        }
        named
    }

    /// A composed strategy must satisfy the *original* matrix at every
    /// universal assignment. Variables the strategy leaves undetermined
    /// were dropped as irrelevant, so any value must do — checked by
    /// trying both.
    fn check_strategy(qcnf: &QCNF, strategy: &super::Strategy) -> Result<(), TestCaseError> {
        let universals: Vec<i32> = qcnf
            .prefix
            .iter()
            .filter(|(q, _)| *q == QuantTy::Forall)
            .flat_map(|(_, vars)| vars.iter().map(|v| v.to_dimacs()))
            .collect();
        let all: Vec<i32> = qcnf
            .prefix
            .iter()
            .flat_map(|(_, vars)| vars.iter().map(|v| v.to_dimacs()))
            .chain(qcnf.matrix.iter().flatten().map(|l| l.var().to_dimacs()))
            .collect();
        for point in 0..1u32 << universals.len() {
            let assignment: Vec<i32> = universals
                .iter()
                .enumerate()
                .map(|(i, &v)| if point >> i & 1 == 1 { v } else { -v })
                .collect();
            let mut values: HashMap<i32, bool> = HashMap::new();
            strategy.evaluate(&assignment, &mut values);
            for &l in &assignment {
                values.insert(l.abs(), l > 0);
            }
            // undetermined variables are irrelevant; default them
            let undetermined: Vec<i32> =
                all.iter().copied().filter(|v| !values.contains_key(v)).collect();
            for v in undetermined {
                values.insert(v, false);
            }
            for clause in &qcnf.matrix {
                let satisfied = clause
                    .iter()
                    .any(|l| values.get(&l.var().to_dimacs()) == Some(&l.is_positive()));
                prop_assert!(
                    satisfied,
                    "strategy falsifies clause {:?} at {:?} on:\n{}\nstrategy: {:?}",
                    clause,
                    &assignment,
                    qcnf,
                    strategy
                );
            }
        }
        Ok(())
    }

    #[test]
    fn three_block_basics() {
        // ∃x ∀y ∃z: z ↔ (x xor y) and z must equal x — forces x-choice
        // to survive both y values; unsatisfiable
        let qcnf = QCNF::new(
            &[
                (QuantTy::Exists, &[1][..]),
                (QuantTy::Forall, &[2][..]),
                (QuantTy::Exists, &[3][..]),
            ],
            &[
                &[-3, 1, 2][..],
                &[-3, -1, -2][..],
                &[3, -1, 2][..],
                &[3, 1, -2][..],
                &[-3, 1][..],
                &[3, -1][..],
            ],
        );
        assert_eq!(solve(&qcnf, Options::default()), qcnf.brute_force());
        assert_eq!(solve_with_expansion_budget(&qcnf, Options::default(), 0), qcnf.brute_force());
        // ∃x ∀y ∃z: z ↔ (x xor y) — satisfiable for any x
        let qcnf = QCNF::new(
            &[
                (QuantTy::Exists, &[1][..]),
                (QuantTy::Forall, &[2][..]),
                (QuantTy::Exists, &[3][..]),
            ],
            &[&[-3, 1, 2][..], &[-3, -1, -2][..], &[3, -1, 2][..], &[3, 1, -2][..]],
        );
        assert_eq!(solve(&qcnf, Options::default()), SolverResult::Satisfiable);
    }

    /// The alternation front-end drives the 2QBF core through its
    /// assumption-query and CEGAR paths, whose behavior depends on the
    /// core options; the verdict must not.
    fn check_all_options(qcnf: &QCNF) -> Result<(), TestCaseError> {
        let expected = qcnf.brute_force();
        for flags in 0..8 {
            let options = Options {
                cegar: flags & 1 != 0,
                case_splits: flags & 2 != 0,
                clause_deletion: flags & 4 != 0,
                // split almost immediately to exercise the machinery
                case_split_threshold: 2,
                ..Options::default()
            };
            let actual = solve(qcnf, options);
            prop_assert_eq!(
                actual,
                expected,
                "alternation solver with {:?} disagrees on:\n{}",
                options,
                qcnf
            );
        }
        Ok(())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]
        /// Every core option combination, on prefixes deep enough to
        /// exercise the recursion.
        #[test]
        fn differential_alternation_options(qcnf in strategy::qcnf(3..=5, 1..=3, 2..=12, 2..=4)) {
            check_all_options(&qcnf)?;
        }

        /// Random instances with one to four quantifier blocks against
        /// the brute-force oracle.
        #[test]
        fn differential_alternations(qcnf in strategy::qcnf(1..=6, 1..=3, 1..=14, 1..=4)) {
            check(&qcnf)?;
        }

        /// Denser three-block instances (the persistent-oracle path).
        #[test]
        fn differential_three_blocks(qcnf in strategy::qcnf(3..=3, 1..=4, 4..=16, 2..=4)) {
            check(&qcnf)?;
        }
    }
}
