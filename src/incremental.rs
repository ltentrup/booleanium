//! An incremental 2QBF solving API.
//!
//! The solver maintains an *assertion stack* of frames holding variable
//! declarations and clauses ([`IncrementalSolver::push`] /
//! [`IncrementalSolver::pop`]), solves the conjunction of all frames under
//! a ∀∃ prefix, and extracts piecewise Skolem functions from satisfiable
//! results.
//!
//! Incrementality has three layers:
//!
//! * **In-place continuation** (default; see
//!   [`IncDet::extend_and_resolve`]): while the stack changes stay
//!   monotone — declarations and clause additions, including in frames
//!   that are pushed and popped without a solve in between — a plain
//!   solve continues the live solver of the previous solve instead of
//!   rebuilding, keeping all derived state. Popping a frame the live
//!   solver has integrated, or redeclaring a variable, falls back to a
//!   rebuild.
//! * **Learnt-clause carrying**: rebuilds are seeded with the clauses
//!   learnt by earlier solves. Learnt clauses are resolvents of the
//!   matrix they were learnt under, so they remain valid for every
//!   extension of that matrix; each carried clause is tagged with the
//!   stack depth at which it was harvested and dropped as soon as that
//!   depth is popped.
//! * **Temporary queries** ([`IncrementalSolver::solve_with_assumptions`]
//!   / [`IncrementalSolver::solve_with_clauses`]): solved on a throwaway
//!   solver beside the continuation base, so a query never costs future
//!   incrementality; the query solver serves the model calls until the
//!   next solve. Nothing learnt under temporary clauses is carried.

use crate::{
    incdet::{model::SkolemModel, IncDet, Options},
    literal::{Lit, Var},
    qcnf::QCNF,
    qdimacs::FromQdimacs,
    QuantTy, SolverResult,
};
use std::collections::{HashMap, HashSet};

/// Restricts the universal domain of an instance to the given literals:
/// clauses satisfied by a restriction literal are dropped, falsified
/// literals are deleted, and the restricted variables leave the prefix
/// (their value is fixed). Must not be called with contradictory
/// restriction literals.
fn restrict_universals(qcnf: &mut QCNF, restriction: &[i32]) {
    for &raw in restriction {
        let lit = crate::literal::Lit::from_dimacs(raw);
        qcnf.matrix.retain(|clause| !clause.contains(&lit));
        for clause in &mut qcnf.matrix {
            clause.retain(|&l| l != !lit);
        }
        for (_, vars) in &mut qcnf.prefix {
            vars.retain(|&v| v != lit.var());
        }
    }
}

/// One frame of the assertion stack.
#[derive(Debug, Default, Clone)]
struct Frame {
    universals: Vec<u32>,
    existentials: Vec<u32>,
    clauses: Vec<Vec<i32>>,
}

/// The continuation state of the last plain [`IncrementalSolver::solve`]:
/// the live solver, its verdict, and how much of every stack frame it has
/// integrated. Frames are append-only (apart from whole-frame pops and
/// redeclarations, which invalidate the base), so the per-frame lengths
/// identify the integrated prefix and everything beyond them is the delta
/// of the next solve — including content of frames that were pushed and
/// popped in between without ever being solved.
#[derive(Debug)]
struct Base {
    result: SolverResult,
    solver: IncDet,
    /// per-frame `(universals, existentials, clauses)` lengths at the
    /// time of integration
    integrated: Vec<(usize, usize, usize)>,
    /// whether the solver sits in a lazily retracted query state instead
    /// of the plain solve state (models must not be served as plain, and
    /// the next plain solve re-searches)
    queried: bool,
}

/// Which solver serves model queries for the most recent solve.
#[derive(Debug, Clone, Copy)]
enum Served {
    /// the continuation base (a plain solve)
    Base,
    /// the continuation base, left in the state of an in-place assumption
    /// query with the given verdict
    BaseQuery(SolverResult),
    /// the throwaway solver of a temporary query
    Query,
}

/// The generalisation solver of [`IncrementalSolver::unanswerable_core`]
/// and how much of the stack it holds.
struct Responder {
    solver: crate::sat::LookupSolver<crate::sat::varisat::Varisat>,
    /// the stack depth it was built for
    depth: usize,
    /// clauses integrated per frame
    integrated: Vec<usize>,
}

impl std::fmt::Debug for Responder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Responder").field("depth", &self.depth).finish_non_exhaustive()
    }
}

/// A term under construction: a literal over the solver's variables,
/// negated by `!`. Terms are built with [`IncrementalSolver::and`] and
/// friends, which Tseitin-encode them and keep the variables they
/// introduce to themselves.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Node(i32);

impl std::ops::Not for Node {
    type Output = Node;

    fn not(self) -> Node {
        Node(-self.0)
    }
}

/// An incremental ∀∃ (2QBF) solver.
#[derive(Debug)]
pub struct IncrementalSolver {
    options: Options,
    /// the assertion stack; index 0 is the base frame that can never be
    /// popped
    frames: Vec<Frame>,
    /// carried learnt clauses, tagged with the stack depth they were
    /// learnt at
    learnt: Vec<(usize, Vec<i32>)>,
    /// dedup mirror of `learnt`: the live solver reports its whole learnt
    /// set on every harvest, and each clause is carried at most once
    carried: HashSet<Vec<i32>>,
    /// the continuation base: the live solver of the last plain solve
    base: Option<Base>,
    /// the solver of the most recent temporary query
    /// ([`IncrementalSolver::solve_with_assumptions`] /
    /// [`IncrementalSolver::solve_with_clauses`]), kept for model queries
    query: Option<(SolverResult, IncDet)>,
    /// what the most recent throwaway query added to the stack: extra
    /// clauses and a universal-domain restriction. Kept so that a
    /// winning move can be *re-derived* against the same instance the
    /// query answered rather than against the bare stack.
    query_extra: (Vec<Vec<i32>>, Vec<i32>),
    /// which solver answers model queries; `None` after a stack change
    /// that staled the models (pop, redeclaration)
    last: Option<Served>,
    /// whether monotone deltas continue the live solver in place instead
    /// of rebuilding
    continuation: bool,
    /// the next fresh variable for [`IncrementalSolver::fresh_var`]
    next_var: u32,
    /// variables the *solver* introduced while Tseitin-encoding a term
    /// the caller built, as opposed to variables the caller declared.
    /// They are existential and innermost by construction, and they are
    /// the solver's business: no answer speaks about them.
    auxiliary: HashSet<u32>,
    /// structural hash over the terms built so far, so an expression
    /// written twice is encoded once. Cleared on `pop`, which can
    /// retire the variables it names.
    shared: HashMap<(i32, i32), i32>,
    /// the inputs of each gate, by variable: the reverse of `shared`,
    /// so asserting a term can walk its structure
    inputs: HashMap<u32, Vec<i32>>,
    /// structural hash for conjunctions wider than two
    shared_wide: HashMap<Vec<i32>, i32>,
    /// the constant-true node, allocated on first use
    truth: Option<i32>,
    /// the plain-SAT solver [`IncrementalSolver::unanswerable_core`]
    /// asks, kept across calls: the frames it reads are append-only, so
    /// it grows by a delta per call instead of being rebuilt
    responder: Option<Responder>,
    /// lifetime count of in-place monotone extensions, across rebuilds
    extensions: u32,
}

impl Default for IncrementalSolver {
    fn default() -> Self {
        Self::new(Options::default())
    }
}

impl IncrementalSolver {
    #[must_use]
    pub fn new(options: Options) -> Self {
        Self {
            options,
            frames: vec![Frame::default()],
            learnt: Vec::new(),
            carried: HashSet::new(),
            base: None,
            query: None,
            query_extra: (Vec::new(), Vec::new()),
            last: None,
            continuation: true,
            next_var: 1,
            extensions: 0,
            auxiliary: HashSet::new(),
            shared: HashMap::new(),
            inputs: HashMap::new(),
            shared_wide: HashMap::new(),
            truth: None,
            responder: None,
        }
    }

    /// Enables or disables in-place continuation of the live solver across
    /// monotone stack changes (enabled by default; rebuild-per-solve
    /// remains available for comparison and as the fallback).
    pub fn set_continuation(&mut self, enabled: bool) {
        self.continuation = enabled;
    }

    /// A fresh variable, unused by any declaration so far. The variable
    /// still needs to be declared to be quantified.
    pub fn fresh_var(&mut self) -> u32 {
        let var = self.next_var;
        self.next_var += 1;
        var
    }

    fn note_var(&mut self, var: u32) {
        self.next_var = self.next_var.max(var + 1);
    }

    /// Declares a universal variable in the current frame.
    pub fn declare_universal(&mut self, var: u32) {
        self.note_var(var);
        self.frames.last_mut().expect("base frame exists").universals.push(var);
    }

    /// Declares an existential variable in the current frame.
    pub fn declare_existential(&mut self, var: u32) {
        self.note_var(var);
        self.frames.last_mut().expect("base frame exists").existentials.push(var);
    }

    /// Lifts a declared variable into a term.
    #[must_use]
    pub fn node(var: u32) -> Node {
        Node(i32::try_from(var).expect("variable fits an i32"))
    }

    /// The constant term.
    pub fn constant(&mut self, value: bool) -> Node {
        let truth = if let Some(truth) = self.truth {
            truth
        } else {
            let var = self.aux_var();
            self.add_clause(&[var]);
            self.truth = Some(var);
            var
        };
        if value {
            Node(truth)
        } else {
            Node(-truth)
        }
    }

    /// The conjunction of two terms.
    pub fn and(&mut self, a: Node, b: Node) -> Node {
        let (a, b) = (a.0, b.0);
        // the folds a circuit builder owes its caller: a term written
        // twice is encoded once, and a trivial one is not encoded at all
        if a == b {
            return Node(a);
        }
        if a == -b {
            return self.constant(false);
        }
        if let Some(truth) = self.truth {
            if a == truth {
                return Node(b);
            }
            if b == truth {
                return Node(a);
            }
            if a == -truth || b == -truth {
                return self.constant(false);
            }
        }
        let key = if a <= b { (a, b) } else { (b, a) };
        if let Some(&existing) = self.shared.get(&key) {
            return Node(existing);
        }
        let gate = self.aux_var();
        self.add_clause(&[-gate, a]);
        self.add_clause(&[-gate, b]);
        self.add_clause(&[gate, -a, -b]);
        self.shared.insert(key, gate);
        self.inputs.insert(gate.unsigned_abs(), vec![a, b]);
        Node(gate)
    }

    /// The conjunction of any number of terms.
    ///
    /// One variable, not one per pair. A `k`-ary conjunction folded
    /// into binary gates costs `k - 1` existentials, and every one of
    /// them is a variable the solver has to determinize and propagate
    /// through — which is how a term interface can quietly hand the
    /// solver several times the instance a hand-written encoding would
    /// have.
    pub fn and_all(&mut self, nodes: &[Node]) -> Node {
        let mut lits: Vec<i32> = Vec::with_capacity(nodes.len());
        for &n in nodes {
            if let Some(truth) = self.truth {
                if n.0 == truth {
                    continue;
                }
                if n.0 == -truth {
                    return self.constant(false);
                }
            }
            if lits.contains(&-n.0) {
                return self.constant(false);
            }
            if !lits.contains(&n.0) {
                lits.push(n.0);
            }
        }
        match lits.len() {
            0 => return self.constant(true),
            1 => return Node(lits[0]),
            2 => return self.and(Node(lits[0]), Node(lits[1])),
            _ => {}
        }
        let mut key = lits.clone();
        key.sort_unstable();
        if let Some(&existing) = self.shared_wide.get(&key) {
            return Node(existing);
        }
        let gate = self.aux_var();
        for &l in &lits {
            self.add_clause(&[-gate, l]);
        }
        let mut reverse = vec![gate];
        reverse.extend(lits.iter().map(|l| -l));
        self.add_clause(&reverse);
        self.shared_wide.insert(key, gate);
        self.inputs.insert(gate.unsigned_abs(), lits);
        Node(gate)
    }

    /// The disjunction of two terms.
    pub fn or(&mut self, a: Node, b: Node) -> Node {
        !self.and(!a, !b)
    }

    /// The disjunction of any number of terms.
    pub fn or_all(&mut self, nodes: &[Node]) -> Node {
        let negated: Vec<Node> = nodes.iter().map(|&n| !n).collect();
        !self.and_all(&negated)
    }

    /// The exclusive disjunction of two terms.
    pub fn xor(&mut self, a: Node, b: Node) -> Node {
        let left = self.and(a, !b);
        let right = self.and(!a, b);
        self.or(left, right)
    }

    /// `if cond then a else b`.
    pub fn ite(&mut self, cond: Node, a: Node, b: Node) -> Node {
        let taken = self.and(cond, a);
        let skipped = self.and(!cond, b);
        self.or(taken, skipped)
    }

    /// Binds a term to a variable of its own.
    ///
    /// Folding and sharing are usually what a caller wants from a term
    /// interface, but incremental determinization runs on *named*
    /// definitions: a signal with a variable is one the solver can
    /// determinize, propagate through and record a Skolem function for,
    /// while the same signal inlined into its uses is none of those.
    /// Naming the signals a hand-written encoding would have named
    /// keeps that substrate.
    pub fn named(&mut self, node: Node) -> Node {
        let var = self.aux_var();
        self.add_clause(&[-var, node.0]);
        self.add_clause(&[var, -node.0]);
        Node(var)
    }

    /// Asserts a term in the current frame.
    ///
    /// The top-level structure becomes clauses rather than a unit on a
    /// reified literal: a conjunction is asserted conjunct by conjunct,
    /// and a disjunction is flattened into one clause. Only what sits
    /// under that is left to the gates. Asserting the reified literal
    /// instead costs a propagation step per level, which is exactly the
    /// structure a caller hand-writing clauses would not have given
    /// away.
    pub fn assert_node(&mut self, node: Node) {
        let mut conjuncts = vec![node];
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        while let Some(node) = conjuncts.pop() {
            if let Some(children) = self.gate(node.0) {
                // a positive gate is a conjunction: assert every side
                conjuncts.extend(children.into_iter().map(Node));
                continue;
            }
            let mut clause = Vec::new();
            let mut pending = vec![node];
            while let Some(term) = pending.pop() {
                match self.gate(-term.0) {
                    // a negated gate is a disjunction: flatten it
                    Some(children) => {
                        pending.extend(children.into_iter().map(|l| Node(-l)));
                    }
                    None => clause.push(term.0),
                }
            }
            clauses.push(clause);
        }
        for clause in clauses {
            self.add_clause(&clause);
        }
    }

    /// The two inputs of a term, when it is a positively-signed gate the
    /// solver introduced itself.
    fn gate(&self, literal: i32) -> Option<Vec<i32>> {
        if literal <= 0 || !self.auxiliary.contains(&literal.unsigned_abs()) {
            return None;
        }
        self.inputs.get(&literal.unsigned_abs()).cloned()
    }

    /// The literal a term denotes, for callers that still speak in
    /// clauses.
    #[must_use]
    pub fn literal(node: Node) -> i32 {
        node.0
    }

    /// A fresh *auxiliary* variable: existential, innermost, and the
    /// solver's own. Auxiliaries are excluded from every answer, which
    /// is the whole point of building terms instead of clauses — a
    /// caller that hand-encodes a circuit puts its gate variables in the
    /// same namespace as its quantified ones, and then every model,
    /// witness and cube it gets back is polluted with them.
    fn aux_var(&mut self) -> i32 {
        let var = self.fresh_var();
        self.declare_existential(var);
        self.auxiliary.insert(var);
        i32::try_from(var).expect("variable fits an i32")
    }

    /// Whether a variable is one the solver introduced itself.
    #[must_use]
    pub fn is_auxiliary(&self, var: u32) -> bool {
        self.auxiliary.contains(&var)
    }

    /// Adds a clause (DIMACS literals) to the current frame.
    pub fn add_clause(&mut self, lits: &[i32]) {
        for &l in lits {
            self.note_var(l.unsigned_abs());
        }
        self.frames.last_mut().expect("base frame exists").clauses.push(lits.to_vec());
    }

    /// Adds a clause to the frame at stack depth `depth` instead of the
    /// top frame. Frontends use this to materialize assertions they had
    /// deferred while the quantifier structure was still undetermined, in
    /// the frame the assertion belongs to.
    ///
    /// # Panics
    ///
    /// Panics if `depth` exceeds the current stack depth.
    pub fn add_clause_at(&mut self, depth: usize, lits: &[i32]) {
        for &l in lits {
            self.note_var(l.unsigned_abs());
        }
        self.frames[depth].clauses.push(lits.to_vec());
    }

    /// Changes an existing existential declaration into a universal one,
    /// in whatever frame it was declared. Frontends use this when the
    /// intended quantifier of a symbol only becomes clear after its
    /// declaration.
    pub fn redeclare_universal(&mut self, var: u32) {
        for frame in &mut self.frames {
            if let Some(pos) = frame.existentials.iter().position(|&v| v == var) {
                frame.existentials.remove(pos);
                frame.universals.push(var);
                // an integrated frame was edited: the live solver no
                // longer matches any prefix of the stack
                self.base = None;
                self.query = None;
        self.query_extra = (Vec::new(), Vec::new());
                self.last = None;
                return;
            }
        }
    }

    /// Adds the definition `var ↔ AND(lits)` to the current frame and
    /// declares `var` existential. This is the definition-level input
    /// path: the two-sided encoding keeps the variable deterministic by
    /// construction.
    pub fn define_and(&mut self, var: u32, lits: &[i32]) {
        self.declare_existential(var);
        let var = i32::try_from(var).expect("variable fits an i32");
        let mut last = Vec::with_capacity(lits.len() + 1);
        for &l in lits {
            self.add_clause(&[-var, l]);
            last.push(-l);
        }
        last.push(var);
        self.add_clause(&last);
    }

    /// Pushes a new frame onto the assertion stack.
    pub fn push(&mut self) {
        self.frames.push(Frame::default());
    }

    /// Pops the top frame, dropping its declarations and clauses, and
    /// every carried learnt clause that was learnt while the frame was on
    /// the stack. Returns `false` if only the base frame is left.
    pub fn pop(&mut self) -> bool {
        // a pop can retire auxiliary variables, so the terms built
        // against them stop being shareable
        self.shared.clear();
        self.shared_wide.clear();
        self.inputs.clear();
        self.truth = None;
        if self.responder.as_ref().is_some_and(|r| self.frames.len() <= r.depth + 1) {
            self.responder = None;
        }
        if self.frames.len() <= 1 {
            return false;
        }
        let popped = self.frames.pop().expect("checked above");
        let depth = self.frames.len() - 1;
        self.learnt.retain(|(d, _)| *d <= depth);
        self.carried = self.learnt.iter().map(|(_, c)| c.clone()).collect();
        // The base survives a pop of frames it never integrated (a
        // pushed-and-popped scope without a solve inside). Popping an
        // integrated frame retracts clauses the live solver holds: for a
        // satisfiable base and a clause-only frame the solver can often
        // drop them in place ([`IncDet::retract_to_depth`]); otherwise
        // the base is discarded and the next solve rebuilds.
        let integrated_popped =
            self.base.as_ref().is_some_and(|base| self.frames.len() < base.integrated.len());
        if integrated_popped {
            let sizes = self.frame_sizes();
            let mut retained = false;
            if popped.universals.is_empty() && popped.existentials.is_empty() {
                if let Some(base) = self.base.as_mut() {
                    if base.result == SolverResult::Satisfiable
                        && base.solver.retract_to_depth(depth)
                    {
                        base.integrated = sizes;
                        // the retraction backtracked the live solver
                        base.queried = true;
                        retained = true;
                    }
                }
            }
            if !retained {
                self.base = None;
            }
        }
        self.query = None;
        self.query_extra = (Vec::new(), Vec::new());
        self.last = None;
        true
    }

    /// The current stack depth (0 for the base frame).
    #[must_use]
    pub fn depth(&self) -> usize {
        self.frames.len() - 1
    }

    /// Builds the 2QBF instance for the current stack plus the given
    /// extra clauses, including the carried learnt clauses.
    fn qcnf_with(&self, extra: &[Vec<i32>]) -> QCNF {
        let universals: Vec<u32> =
            self.frames.iter().flat_map(|f| f.universals.iter().copied()).collect();
        let existentials: Vec<u32> =
            self.frames.iter().flat_map(|f| f.existentials.iter().copied()).collect();
        let clauses: Vec<&[i32]> = self
            .frames
            .iter()
            .flat_map(|f| f.clauses.iter().map(Vec::as_slice))
            .chain(self.learnt.iter().map(|(_, c)| c.as_slice()))
            .chain(extra.iter().map(Vec::as_slice))
            .collect();
        let mut prefix: Vec<(QuantTy, &[u32])> = Vec::new();
        if !universals.is_empty() {
            prefix.push((QuantTy::Forall, &universals[..]));
        }
        prefix.push((QuantTy::Exists, &existentials[..]));
        QCNF::new(&prefix, &clauses)
    }

    /// Builds the 2QBF instance for the current stack, including the
    /// carried learnt clauses.
    pub(crate) fn qcnf(&self) -> QCNF {
        self.qcnf_with(&[])
    }

    /// The per-frame sizes of the current stack.
    fn frame_sizes(&self) -> Vec<(usize, usize, usize)> {
        self.frames
            .iter()
            .map(|f| (f.universals.len(), f.existentials.len(), f.clauses.len()))
            .collect()
    }

    /// The stack content beyond the integrated per-frame sizes: the
    /// monotone delta between the base solver and the current stack.
    fn delta(
        &self,
        integrated: &[(usize, usize, usize)],
    ) -> (Vec<u32>, Vec<u32>, Vec<Vec<i32>>, Vec<usize>) {
        let mut universals = Vec::new();
        let mut existentials = Vec::new();
        let mut clauses = Vec::new();
        let mut depths = Vec::new();
        for (i, frame) in self.frames.iter().enumerate() {
            let (u, e, c) = integrated.get(i).copied().unwrap_or((0, 0, 0));
            universals.extend_from_slice(&frame.universals[u..]);
            existentials.extend_from_slice(&frame.existentials[e..]);
            clauses.extend_from_slice(&frame.clauses[c..]);
            depths.extend(std::iter::repeat(i).take(frame.clauses.len() - c));
        }
        (universals, existentials, clauses, depths)
    }

    /// Builds a fresh core solver for the current stack plus the carried
    /// learnt clauses, tagging every clause with its frame depth (carried
    /// clauses with the depth they were harvested at) so popped frames
    /// can later be retracted in place.
    fn build_base_solver(&self) -> IncDet {
        let mut solver = IncDet::with_options(self.options);
        let to_var = |v: &u32| Var::from_dimacs(i32::try_from(*v).expect("variable fits an i32"));
        let universals: Vec<Var> =
            self.frames.iter().flat_map(|f| f.universals.iter()).map(to_var).collect();
        let existentials: Vec<Var> =
            self.frames.iter().flat_map(|f| f.existentials.iter()).map(to_var).collect();
        if !universals.is_empty() {
            solver.quantify(QuantTy::Forall, &universals);
        }
        solver.quantify(QuantTy::Exists, &existentials);
        let add = |solver: &mut IncDet, depth: usize, clause: &[i32]| {
            solver.set_load_depth(depth);
            let lits: Vec<Lit> = clause.iter().map(|&l| Lit::from_dimacs(l)).collect();
            FromQdimacs::add_clause(solver, &lits);
        };
        for (depth, frame) in self.frames.iter().enumerate() {
            for clause in &frame.clauses {
                add(&mut solver, depth, clause);
            }
        }
        for (depth, clause) in &self.learnt {
            add(&mut solver, *depth, clause);
        }
        solver
    }

    /// Solves the conjunction of the assertion stack. When the changes
    /// since the last plain solve are monotone (only declarations and
    /// clause additions, including inside frames that were pushed and
    /// popped without a solve) the live solver is continued in place;
    /// otherwise — and whenever the in-place path reports that its
    /// retained state cannot be soundly kept — a fresh solver is built
    /// from the stack plus the carried learnt clauses.
    pub fn solve(&mut self) -> SolverResult {
        self.query = None;
        self.query_extra = (Vec::new(), Vec::new());
        if self.continuation {
            if let Some(mut base) = self.base.take() {
                let (universals, existentials, clauses, depths) = self.delta(&base.integrated);
                let unchanged =
                    universals.is_empty() && existentials.is_empty() && clauses.is_empty();
                match base.result {
                    // adding clauses and variables keeps an unsatisfiable
                    // instance unsatisfiable; the delta stays un-integrated
                    SolverResult::Unsatisfiable => {
                        self.base = Some(base);
                        self.last = Some(Served::Base);
                        return SolverResult::Unsatisfiable;
                    }
                    SolverResult::Satisfiable if unchanged && !base.queried => {
                        self.base = Some(base);
                        self.last = Some(Served::Base);
                        return SolverResult::Satisfiable;
                    }
                    SolverResult::Satisfiable => {
                        let extended = base.solver.extend_and_resolve(
                            &universals,
                            &existentials,
                            &clauses,
                            &depths,
                        );
                        // the live solver's learnt clauses are valid
                        // resolvents of the current stack either way (a
                        // rejected extension integrates nothing)
                        self.harvest_learnt(&base.solver);
                        if let Some(result) = extended {
                            self.extensions += 1;
                            base.result = result;
                            base.integrated = self.frame_sizes();
                            base.queried = false;
                            self.base = Some(base);
                            self.last = Some(Served::Base);
                            return result;
                        }
                        // rejected: fall through to a rebuild
                    }
                    SolverResult::Unknown => {}
                }
            }
        }
        let mut solver = self.build_base_solver();
        let result = solver.solve();
        self.harvest_learnt(&solver);
        self.base = Some(Base { result, solver, integrated: self.frame_sizes(), queried: false });
        self.last = Some(Served::Base);
        result
    }

    /// Carries the learnt clauses of a solver, each at most once, tagged
    /// with the current stack depth. (A clause may have been learnt at a
    /// shallower depth than it is harvested at; the deeper tag only drops
    /// it earlier than necessary, which is sound.)
    fn harvest_learnt(&mut self, solver: &IncDet) {
        let depth = self.depth();
        for clause in solver.learnt_clauses() {
            if self.carried.insert(clause.clone()) {
                self.learnt.push((depth, clause));
            }
        }
    }

    /// Solves the assertion stack under the given assumption literals,
    /// retracted afterwards. An *existential* assumption is a temporary
    /// unit constraint (the variable's Skolem function must be the
    /// assumed constant). A *universal* assumption restricts the
    /// universal player's domain to the assumed polarity — the
    /// "what if the environment plays u" probe of a games loop; an
    /// unsatisfiable answer under a universal restriction therefore
    /// implies the whole stack is unsatisfiable. Contradictory universal
    /// assumptions denote an empty domain, over which the ∀-quantifier is
    /// vacuously satisfied.
    ///
    /// The query first tries to run *in place* on the live solver
    /// ([`IncDet::resolve_with_assumptions`]): the stack is brought up to
    /// date with a plain solve, the literals are assumed as retractable
    /// constants at query decision levels, and everything learnt or
    /// recorded during the query persists. When the in-place path
    /// declines (recorded cases predate the query, unsupported assumption
    /// shapes), the query falls back to a throwaway solver over the
    /// restricted instance.
    pub fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> SolverResult {
        let universal_set: HashSet<u32> =
            self.frames.iter().flat_map(|f| f.universals.iter().copied()).collect();
        let (universal, existential): (Vec<i32>, Vec<i32>) =
            assumptions.iter().partition(|l| universal_set.contains(&l.unsigned_abs()));
        if self.continuation {
            // bring the base up to date with the stack (establishing it
            // on the first query); when nothing changed the query manages
            // the solver state itself, so no re-solve is needed even
            // after an earlier query
            let unchanged = self.base.as_ref().is_some_and(|base| {
                let (u, e, c, _) = self.delta(&base.integrated);
                u.is_empty() && e.is_empty() && c.is_empty()
            });
            let result = if unchanged {
                self.base.as_ref().expect("unchanged implies present").result
            } else {
                self.solve()
            };
            match result {
                // An unsatisfiable stack answers queries that only
                // strengthen it. A universal assumption *weakens* the
                // obligation instead — the universal player's winning
                // move may lie outside the restriction — so those fall
                // through to the restricted throwaway solve.
                SolverResult::Unsatisfiable if universal.is_empty() => {
                    self.query = None;
        self.query_extra = (Vec::new(), Vec::new());
                    self.last = Some(Served::BaseQuery(SolverResult::Unsatisfiable));
                    return SolverResult::Unsatisfiable;
                }
                SolverResult::Satisfiable => {
                    let base = self.base.as_mut().expect("checked");
                    if base.solver.fast_query_available() {
                        // the attempt may backtrack the live solver even
                        // when it declines mid-way, so the next plain
                        // solve must re-search either way
                        base.queried = true;
                        if let Some(result) = base.solver.resolve_with_assumptions(assumptions) {
                            self.query = None;
        self.query_extra = (Vec::new(), Vec::new());
                            self.last = Some(Served::BaseQuery(result));
                            return result;
                        }
                    }
                }
                SolverResult::Unsatisfiable | SolverResult::Unknown => {}
            }
        }
        // throwaway fallback: existential assumptions become temporary
        // unit clauses; universal assumptions substitute their constant
        // into the instance (a unit clause would instead let the
        // universal player falsify it)
        let contradictory = universal.iter().any(|&l| universal.contains(&-l));
        let units: Vec<Vec<i32>> = existential.iter().map(|&lit| vec![lit]).collect();
        let mut qcnf = self.qcnf_with(&units);
        if contradictory {
            // an empty restricted domain: vacuously satisfiable
            qcnf = QCNF::new(&[(QuantTy::Exists, &[])], &[]);
        } else {
            restrict_universals(&mut qcnf, &universal);
        }
        let mut solver = IncDet::from_qcnf_with_options(&qcnf, self.options);
        let result = solver.solve();
        self.query = Some((result, solver));
        self.query_extra = (units, universal);
        self.last = Some(Served::Query);
        result
    }

    /// Solves the assertion stack under temporary clauses. Unlike
    /// [`IncrementalSolver::add_clause`], this supports clauses that do
    /// not stay implied when the ambient formula changes (a later solve
    /// must not resolve against them). The query runs on a throwaway
    /// solver, so the continuation base of the plain solves stays
    /// untouched; nothing learnt under the temporary clauses is carried.
    pub fn solve_with_clauses(&mut self, clauses: &[Vec<i32>]) -> SolverResult {
        let qcnf = self.qcnf_with(clauses);
        let mut solver = IncDet::from_qcnf_with_options(&qcnf, self.options);
        let result = solver.solve();
        self.query = Some((result, solver));
        self.query_extra = (clauses.to_vec(), Vec::new());
        self.last = Some(Served::Query);
        result
    }

    /// The result and solver of the most recent solve, if the stack has
    /// not changed in a model-invalidating way since (pop,
    /// redeclaration).
    fn served(&self) -> Option<(SolverResult, &IncDet)> {
        match self.last? {
            Served::Base => self.base.as_ref().map(|b| (b.result, &b.solver)),
            Served::BaseQuery(result) => self.base.as_ref().map(|b| (result, &b.solver)),
            Served::Query => self.query.as_ref().map(|(r, s)| (*r, s)),
        }
    }

    /// The result of the most recent solve, if the stack has not changed
    /// since.
    #[must_use]
    pub fn last_result(&self) -> Option<SolverResult> {
        self.served().map(|(r, _)| r)
    }

    /// The piecewise Skolem model of the most recent solve. Only valid if
    /// the last result was [`SolverResult::Satisfiable`].
    #[must_use]
    pub fn skolem_model(&self) -> Option<SkolemModel> {
        match self.served() {
            Some((SolverResult::Satisfiable, solver)) => Some(solver.skolem_model()),
            _ => None,
        }
    }

    /// Verifies the Skolem functions of the most recent satisfiable solve.
    #[must_use]
    pub fn verify(&self) -> bool {
        matches!(self.served(), Some((SolverResult::Satisfiable, solver)) if solver.verify_skolem_functions())
    }

    /// Number of in-place monotone extensions the continuation base has
    /// performed since its last rebuild (diagnostic for incremental
    /// workloads).
    #[must_use]
    pub fn extension_count(&self) -> u32 {
        self.base.as_ref().map_or(0, |base| base.solver.extension_count())
    }

    /// Number of in-place monotone extensions performed over the lifetime
    /// of this solver, across rebuilds (diagnostic for incremental
    /// workloads; [`IncrementalSolver::extension_count`] resets with
    /// every rebuild).
    #[must_use]
    pub fn extension_total(&self) -> u32 {
        self.extensions
    }

    /// The verified winning move of the universal player for the most
    /// recent unsatisfiable solve: a (partial) assignment of the
    /// universal variables (DIMACS literals) such that no extension
    /// admits an existential response. `None` if the last result was not
    /// unsatisfiable or the recorded candidate did not pass verification
    /// (see [`IncDet::unsat_witness`]).
    #[must_use]
    pub fn universal_witness(&self) -> Option<Vec<i32>> {
        self.universal_witness_minimized(&|_| false)
    }

    /// A winning move of the universal player that is *always*
    /// available for an unsatisfiable stack, unlike
    /// [`IncrementalSolver::universal_witness`].
    ///
    /// The core records a winning move as a by-product of the
    /// refutation, but that move is heuristic — pure-literal
    /// assignments are winnability-preserving *choices* rather than
    /// pointwise-forced values — so it is verified before exposure and
    /// discarded when it fails. Callers that need the move rather than
    /// merely the verdict (bounded synthesis wanting its parameters,
    /// a game refinement wanting a state to exclude) were left with
    /// nothing.
    ///
    /// The fallback is self-reduction. The stack is unsatisfiable, so
    /// *some* move wins; fix one universal variable at a time and ask
    /// whether the restriction is still unsatisfiable. If it is, that
    /// value stays; if not, the opposite value must win, because a
    /// winning region cannot vanish under a two-way split. Each step
    /// is one restricted solve on a throwaway core, so the base and
    /// its continuation are untouched, and the result is complete by
    /// construction. The move is then minimized over the variables the
    /// caller marks removable — see [`IncDet::unsat_witness_minimized`]
    /// for why that choice belongs to the caller.
    #[must_use]
    pub fn universal_witness_complete(&self, removable: &dyn Fn(i32) -> bool) -> Option<Vec<i32>> {
        if let Some(witness) = self.universal_witness_minimized(removable) {
            return Some(witness);
        }
        if !matches!(self.served(), Some((SolverResult::Unsatisfiable, _))) {
            return None;
        }
        let restricted: HashSet<u32> =
            self.query_extra.1.iter().map(|l| l.unsigned_abs()).collect();
        let universals: Vec<i32> = self
            .frames
            .iter()
            .flat_map(|f| f.universals.iter())
            .filter(|v| !restricted.contains(v))
            .map(|&v| i32::try_from(v).expect("variable fits an i32"))
            .collect();
        // fix the variables one at a time, keeping the restriction
        // unsatisfiable — the invariant that makes this complete
        let mut fixed: Vec<i32> = Vec::new();
        for var in universals {
            fixed.push(var);
            if !self.restricted_is_unsatisfiable(&fixed) {
                // every extension with `var` true is answerable, so a
                // winning move must set it false
                let last = fixed.last_mut().expect("just pushed");
                *last = -var;
                debug_assert!(self.restricted_is_unsatisfiable(&fixed));
            }
        }
        // Generalize the complete move, and note that this must use the
        // *strong* test, not the one that drove the self-reduction.
        // "The stack restricted to this cube is unsatisfiable" says only
        // that *some* point of the cube wins — enough to keep narrowing
        // towards one, useless as a claim about the cube — whereas a
        // caller that acts on the whole cube (a game excluding a region)
        // needs every point of it to win. That is exactly the plain-SAT
        // check [`IncDet::unsat_witness_minimized`] applies: no
        // completion of the universals admits any response.
        let mut kept: Vec<Option<i32>> = fixed.into_iter().map(Some).collect();
        for position in 0..kept.len() {
            let Some(lit) = kept[position] else { continue };
            if !removable(lit) {
                continue;
            }
            kept[position] = None;
            let reduced: Vec<i32> = kept.iter().flatten().copied().collect();
            if !self.move_is_unanswerable(&reduced) {
                kept[position] = Some(lit);
            }
        }
        Some(kept.into_iter().flatten().collect())
    }

    /// Whether *no* completion of the given universal literals admits an
    /// existential response — the strong reading of a winning move, and
    /// the one a caller may act on for the whole cube. A plain SAT
    /// question over the matrix, mirroring
    /// [`IncDet::unsat_witness_minimized`].
    fn move_is_unanswerable(&self, universal: &[i32]) -> bool {
        use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};
        let (extra, restriction) = &self.query_extra;
        let mut qcnf = self.qcnf_with(extra);
        restrict_universals(&mut qcnf, restriction);
        let mut solver = LookupSolver::<Varisat>::default();
        let count = qcnf
            .prefix
            .iter()
            .flat_map(|(_, vars)| vars.iter().copied())
            .chain(qcnf.matrix.iter().flatten().map(|l| l.var()))
            .map(|v| usize::try_from(v.to_dimacs()).expect("fits") + 1)
            .max()
            .unwrap_or(0);
        solver.set_var_count(count);
        for clause in &qcnf.matrix {
            let lits: Vec<_> = clause.iter().map(|&l| solver.lookup(l)).collect();
            solver.add_clause(&lits);
        }
        let assumptions: Vec<_> =
            universal.iter().map(|&l| solver.lookup(crate::literal::Lit::from_dimacs(l))).collect();
        !solver.solve_with_assumptions(&assumptions).expect("a plain SAT query")
    }

    /// Whether the stack stays unsatisfiable once the universal domain
    /// is restricted to the given literals. Runs on a throwaway core.
    fn restricted_is_unsatisfiable(&self, universal: &[i32]) -> bool {
        let (extra, restriction) = &self.query_extra;
        let mut qcnf = self.qcnf_with(extra);
        restrict_universals(&mut qcnf, restriction);
        restrict_universals(&mut qcnf, universal);
        IncDet::from_qcnf_with_options(&qcnf, self.options).solve() == SolverResult::Unsatisfiable
    }

    /// [`IncrementalSolver::universal_witness`] with the move minimized
    /// over the variables the caller marks removable — see
    /// [`IncDet::unsat_witness_minimized`] for why that choice belongs
    /// to the caller.
    #[must_use]
    pub fn universal_witness_minimized(
        &self,
        removable: &dyn Fn(i32) -> bool,
    ) -> Option<Vec<i32>> {
        match self.served() {
            Some((SolverResult::Unsatisfiable, solver)) => {
                solver.unsat_witness_minimized(removable)
            }
            _ => None,
        }
    }

    /// Whether any existential response satisfies `question` under the
    /// given universal literals, and if not, which of those literals the
    /// refutation needed.
    ///
    /// This is the generalisation primitive a counterexample-guided
    /// caller wants, and the reason it takes a *term* rather than using
    /// the whole assertion stack is measured: minimising a universal
    /// move against everything the solver holds — matrix, auxiliary
    /// definitions, and whatever constraints the caller has pushed for
    /// its own bookkeeping — produces cubes an order of magnitude
    /// weaker than minimising it against the question actually being
    /// asked (`RESEARCH.md`, RQ5: 64 cubes against 6 on one game).
    /// Only the caller knows which term is the question, so only the
    /// caller can say.
    ///
    /// `depth` bounds the assertion stack the question is asked
    /// against, as if the stack had been popped to it: a caller whose
    /// top frame holds round bookkeeping asks below it, and the term it
    /// names must have been built below it too.
    ///
    /// `None` means the move is answerable and there is nothing to
    /// generalise. The core is a subset of `universal`; auxiliary
    /// variables never appear in it, because they are never assumed.
    pub fn unanswerable_core(
        &mut self,
        depth: usize,
        universal: &[i32],
        question: Node,
    ) -> Option<Vec<i32>> {
        use crate::sat::{varisat::Varisat, LookupSolver, SatSolver, SatSolverLit};
        let stale = !self
            .responder
            .as_ref()
            .is_some_and(|r| r.depth == depth && r.integrated.len() <= self.frames.len());
        if stale {
            let mut solver = LookupSolver::<Varisat>::default();
            solver.set_var_count(usize::try_from(self.next_var).expect("fits") + 1);
            self.responder = Some(Responder { solver, depth, integrated: Vec::new() });
        }
        let responder = self.responder.as_mut().expect("just built");
        responder.solver.set_var_count(usize::try_from(self.next_var).expect("fits") + 1);
        responder.integrated.resize(depth + 1, 0);
        for (index, frame) in self.frames.iter().take(depth + 1).enumerate() {
            for clause in frame.clauses.iter().skip(responder.integrated[index]) {
                let encoded: Vec<_> =
                    clause.iter().map(|&l| responder.solver.lookup(Lit::from_dimacs(l))).collect();
                responder.solver.add_clause(&encoded);
            }
            responder.integrated[index] = frame.clauses.len();
        }
        // the question is assumed, not asserted: it changes between
        // calls as the caller's refinement grows, and the solver has to
        // outlive it
        let mut assumptions: Vec<_> =
            universal.iter().map(|&l| responder.solver.lookup(Lit::from_dimacs(l))).collect();
        let asked = responder.solver.lookup(Lit::from_dimacs(question.0));
        assumptions.push(asked);
        if responder.solver.solve_with_assumptions(&assumptions).expect("plain SAT") {
            return None;
        }
        let core: HashSet<usize> =
            responder.solver.failed_assumptions()?.iter().map(|&l| l.var_index()).collect();
        Some(
            universal
                .iter()
                .zip(&assumptions)
                .filter(|(_, &mapped)| core.contains(&mapped.var_index()))
                .map(|(&l, _)| l)
                .collect(),
        )
    }

    /// The *unverified* recorded universal candidate of the most recent
    /// unsatisfiable solve (see [`IncDet::unsat_witness_candidate`]):
    /// sound only where any universal assignment is, e.g. as an
    /// expansion point.
    #[must_use]
    pub fn universal_witness_candidate(&self) -> Option<Vec<i32>> {
        match self.served() {
            Some((SolverResult::Unsatisfiable, solver)) => solver.unsat_witness_candidate(),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn push_pop_basics() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        // e2 must equal u1
        solver.add_clause(&[-1, 2]);
        solver.add_clause(&[1, -2]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());

        solver.push();
        // additionally force e2 constant true: unsatisfiable
        solver.add_clause(&[2]);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert!(solver.pop());

        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        // assumptions behave like a temporary frame
        assert_eq!(solver.solve_with_assumptions(&[2]), SolverResult::Unsatisfiable);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
    }

    #[test]
    fn universal_witness_of_unsat() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        solver.add_clause(&[-1, 2]);
        // no witness on satisfiable results
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.universal_witness(), None);
        // now for u1 = true, neither value of e2 works
        solver.add_clause(&[-1, -2]);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        let witness = solver.universal_witness().expect("witness available");
        assert_eq!(witness, vec![1]);
    }

    #[test]
    fn monotone_continuation() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        solver.add_clause(&[-1, 2]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        // monotone additions: new clause, new variable, then a clause
        // over both — each solve continues the live solver
        solver.add_clause(&[1, -2]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        let model = solver.skolem_model().expect("satisfiable");
        for u in [1, -1] {
            assert_eq!(model.evaluate(&[u])[&2], u > 0);
        }
        solver.declare_existential(3);
        solver.add_clause(&[-2, 3]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        assert_eq!(solver.extension_count(), 2, "the live solver was continued in place");
        // tighten to unsatisfiable, then the unsat shortcut
        solver.add_clause(&[-1, -2]);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.universal_witness(), Some(vec![1]));
        solver.add_clause(&[3]);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn queries_and_scoped_pops_keep_the_continuation() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        solver.add_clause(&[-1, 2]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        // a temporary query runs beside the base and serves the model
        assert_eq!(solver.solve_with_assumptions(&[-2]), SolverResult::Unsatisfiable);
        assert_eq!(solver.universal_witness(), Some(vec![1]));
        assert_eq!(solver.solve_with_assumptions(&[2]), SolverResult::Satisfiable);
        assert!(solver.verify());
        // a pushed-and-popped scope without a solve inside is invisible
        solver.push();
        solver.add_clause(&[-2]);
        assert!(solver.pop());
        // both left the base intact: the next solve continues in place
        solver.add_clause(&[1, -2]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.extension_count(), 1, "the base was continued, not rebuilt");
        assert!(solver.verify());
        // popping a frame the base integrated forces a rebuild
        solver.push();
        solver.add_clause(&[1]);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert!(solver.pop());
        assert_eq!(solver.last_result(), None, "models are stale after a pop");
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.extension_count(), 0, "the base was rebuilt");
    }

    #[test]
    fn in_place_assumption_queries() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        solver.declare_existential(3);
        solver.add_clause(&[-1, 2, 3]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        // a satisfiable query on the live solver: models and certificate
        // reflect the assumed state
        assert_eq!(solver.solve_with_assumptions(&[-2]), SolverResult::Satisfiable);
        assert!(solver.verify());
        let model = solver.skolem_model().expect("satisfiable");
        assert!(!model.evaluate(&[1])[&2], "assumption holds in the model");
        assert!(model.evaluate(&[1])[&3], "the clause is satisfied via e3");
        // an unsatisfiable query: no response for u1 = true
        assert_eq!(solver.solve_with_assumptions(&[-2, -3]), SolverResult::Unsatisfiable);
        assert_eq!(solver.universal_witness(), Some(vec![1]));
        // the base recovers for plain solves and further queries
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        assert_eq!(solver.solve_with_assumptions(&[2, 3]), SolverResult::Satisfiable);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
    }

    #[test]
    fn universal_assumption_queries() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        // e2 must equal u1
        solver.add_clause(&[-1, 2]);
        solver.add_clause(&[1, -2]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        // restricting the domain keeps satisfiability; the model and
        // certificate are scoped to the restriction
        assert_eq!(solver.solve_with_assumptions(&[1]), SolverResult::Satisfiable);
        assert!(solver.verify());
        let model = solver.skolem_model().expect("satisfiable");
        assert!(model.evaluate(&[1])[&2]);
        // mixed: inside u1 the requirement e2 = false is unsatisfiable...
        assert_eq!(solver.solve_with_assumptions(&[1, -2]), SolverResult::Unsatisfiable);
        assert_eq!(solver.universal_witness(), Some(vec![1]));
        // ...but outside the restriction it is satisfiable
        assert_eq!(solver.solve_with_assumptions(&[-1, -2]), SolverResult::Satisfiable);
        // an unsatisfiable stack can still be winnable on a sub-domain
        solver.add_clause(&[1]);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.solve_with_assumptions(&[1]), SolverResult::Satisfiable);
        // contradictory restrictions: an empty domain, vacuously sat
        assert_eq!(solver.solve_with_assumptions(&[1, -1]), SolverResult::Satisfiable);
    }

    #[test]
    fn pop_retention_of_solved_frames() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_existential(2);
        solver.declare_existential(3);
        solver.add_clause(&[-1, 2, 3]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        // a clause-only frame whose clause keeps two unassigned
        // existentials is retractable in place
        solver.push();
        solver.add_clause(&[1, -2, -3]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.extension_count(), 1);
        assert!(solver.pop());
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        assert!(solver.extension_count() >= 2, "the base survived the pop");
        // a popped frame with declarations discards the base
        solver.push();
        solver.declare_existential(4);
        solver.add_clause(&[-1, 4]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.pop());
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        assert_eq!(solver.extension_count(), 0, "declarations forced a rebuild");
    }

    #[test]
    fn terms_keep_their_encoding_to_themselves() {
        // ∀u ∃c. (u xor c) xor u  — the controller has to answer `true`
        // whatever the environment plays, and the xor tree the solver
        // Tseitin-encodes to get there is none of the caller's business
        let mut solver = IncrementalSolver::default();
        let (u, c) = (solver.fresh_var(), solver.fresh_var());
        solver.declare_universal(u);
        solver.declare_existential(c);
        let (nu, nc) = (IncrementalSolver::node(u), IncrementalSolver::node(c));
        let inner = solver.xor(nu, nc);
        let outer = solver.xor(inner, nu);
        solver.assert_node(outer);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);

        // the caller declared two variables; everything else in the
        // instance is the solver's own
        assert!(!solver.is_auxiliary(u));
        assert!(!solver.is_auxiliary(c));
        let auxiliaries = (1..=solver.fresh_var()).filter(|&v| solver.is_auxiliary(v)).count();
        assert!(auxiliaries > 0, "the xor tree needs gates");

        // and a caller asking for the witness of the dual gets literals
        // over its own variables only
        let mut refuting = IncrementalSolver::default();
        let u = refuting.fresh_var();
        let c = refuting.fresh_var();
        refuting.declare_universal(u);
        refuting.declare_existential(c);
        let (nu, nc) = (IncrementalSolver::node(u), IncrementalSolver::node(c));
        let both = refuting.and(nu, nc);
        refuting.assert_node(both);
        refuting.assert_node(!nu);
        assert_eq!(refuting.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn naming_a_term_gives_it_a_variable() {
        let mut solver = IncrementalSolver::default();
        let (a, b) = (solver.fresh_var(), solver.fresh_var());
        solver.declare_existential(a);
        solver.declare_existential(b);
        let (na, nb) = (IncrementalSolver::node(a), IncrementalSolver::node(b));
        let term = solver.and(na, nb);
        let name = solver.named(term);
        assert_ne!(name, term, "a name is its own variable");
        assert!(solver.is_auxiliary(name.0.unsigned_abs()));

        // and it means the same thing: asserting the name forces both
        // conjuncts, asserting its negation forbids their conjunction
        solver.assert_node(name);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        solver.assert_node(!na);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn wide_conjunctions_cost_one_variable() {
        let mut solver = IncrementalSolver::default();
        let vars: Vec<u32> = (0..8).map(|_| solver.fresh_var()).collect();
        for &v in &vars {
            solver.declare_existential(v);
        }
        let nodes: Vec<Node> = vars.iter().map(|&v| IncrementalSolver::node(v)).collect();
        let before = solver.fresh_var();
        let wide = solver.and_all(&nodes);
        let after = solver.fresh_var();
        // one gate, not seven: folding a k-ary conjunction into binary
        // pairs would hand the solver k-1 existentials to determinize
        assert_eq!(after - before, 2, "one auxiliary variable plus the probe");
        assert!(solver.is_auxiliary(wide.0.unsigned_abs()));

        // the same conjunction in another order is the same gate
        let mut reversed: Vec<Node> = nodes.clone();
        reversed.reverse();
        assert_eq!(solver.and_all(&reversed), wide);
        // and the folds still apply
        let truth = solver.constant(true);
        assert_eq!(solver.and_all(&[nodes[0], truth, nodes[0]]), nodes[0]);
        let falsehood = solver.constant(false);
        assert_eq!(solver.and_all(&[nodes[0], !nodes[0], nodes[1]]), falsehood);
    }

    #[test]
    fn a_core_answers_about_the_question_it_was_given() {
        // Two universals, and a question that mentions only one of
        // them: `u & c`, with `c` a free existential. Under `!u` no
        // response satisfies it, and `s` had nothing to do with that.
        let mut solver = IncrementalSolver::default();
        let (u, s2, c) = (solver.fresh_var(), solver.fresh_var(), solver.fresh_var());
        solver.declare_universal(u);
        solver.declare_universal(s2);
        solver.declare_existential(c);
        let (nu, nc) = (IncrementalSolver::node(u), IncrementalSolver::node(c));
        let question = solver.and(nu, nc);
        let (u, s2) = (i32::try_from(u).unwrap(), i32::try_from(s2).unwrap());

        let core = solver.unanswerable_core(0, &[-u, s2], question).expect("no response under !u");
        assert_eq!(core, vec![-u], "the core is what the refutation needed, not what was assumed");

        // under `u` the controller answers, and there is nothing to
        // generalise
        assert!(solver.unanswerable_core(0, &[u, s2], question).is_none());
    }

    #[test]
    fn terms_share_and_fold() {
        let mut solver = IncrementalSolver::default();
        let (a, b) = (solver.fresh_var(), solver.fresh_var());
        solver.declare_existential(a);
        solver.declare_existential(b);
        let (na, nb) = (IncrementalSolver::node(a), IncrementalSolver::node(b));
        let first = solver.and(na, nb);
        let second = solver.and(nb, na);
        assert_eq!(first, second, "the same term is encoded once");
        assert_eq!(solver.and(na, na), na, "x & x is x");
        let false_node = solver.constant(false);
        assert_eq!(solver.and(na, !na), false_node, "x & !x is false");
        let true_node = solver.constant(true);
        assert_eq!(solver.and(na, true_node), na, "x & true is x");
        assert_eq!(solver.and(na, false_node), false_node, "x & false is false");
    }

    #[test]
    fn define_and_gates() {
        let mut solver = IncrementalSolver::default();
        solver.declare_universal(1);
        solver.declare_universal(2);
        let g = solver.fresh_var();
        assert!(g >= 3);
        solver.define_and(g, &[1, 2]);
        let e = solver.fresh_var();
        solver.declare_existential(e);
        let (g, e) = (i32::try_from(g).unwrap(), i32::try_from(e).unwrap());
        // e ↔ g = u1 ∧ u2
        solver.add_clause(&[-g, e]);
        solver.add_clause(&[g, -e]);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert!(solver.verify());
        let model = solver.skolem_model().expect("satisfiable");
        for (u1, u2) in [(1, 2), (-1, 2), (1, -2), (-1, -2)] {
            let values = model.evaluate(&[u1, u2]);
            assert_eq!(values[&e], u1 > 0 && u2 > 0);
        }
    }

    /// A random assertion-stack session: interleaved pushes, pops, clause
    /// additions, and solves, where every solve is checked against the
    /// brute-force oracle on the current stack, satisfiable results are
    /// certified, and the Skolem model is evaluated on every universal
    /// point against the matrix. The aggressive case-split threshold
    /// exercises the closed-case regions of the model.
    fn session(
        universals: u32,
        existentials: u32,
        script: &[(u8, Vec<i32>)],
        threshold: u32,
        continuation: bool,
    ) {
        let options = Options { case_split_threshold: threshold, ..Options::default() };
        let mut solver = IncrementalSolver::new(options);
        solver.set_continuation(continuation);
        for v in 1..=universals {
            solver.declare_universal(v);
        }
        for v in (universals + 1)..=(universals + existentials) {
            solver.declare_existential(v);
        }
        let mut depth = 0usize;
        for (action, clause) in script {
            match action % 5 {
                0 => {
                    solver.push();
                    depth += 1;
                }
                1 => {
                    if solver.pop() {
                        depth -= 1;
                    }
                    assert_eq!(solver.depth(), depth);
                }
                2 => solver.add_clause(clause),
                3 => {
                    let result = solver.solve();
                    let expected = solver.qcnf().brute_force();
                    assert_eq!(result, expected, "verdict differs from the oracle");
                    if result == SolverResult::Satisfiable {
                        assert!(solver.verify(), "certificate invalid");
                        check_model(&solver, universals, &[]);
                    } else {
                        check_universal_move(&solver, universals);
                    }
                }
                _ => {
                    // a temporary query: the clause literals as assumptions
                    // (universal literals restrict the domain)
                    let assumptions = clause.clone();
                    let result = solver.solve_with_assumptions(&assumptions);
                    let universal_part: Vec<i32> = assumptions
                        .iter()
                        .filter(|l| l.unsigned_abs() <= universals)
                        .copied()
                        .collect();
                    if universal_part.iter().any(|&l| universal_part.contains(&-l)) {
                        // an empty restricted domain is vacuously satisfiable
                        assert_eq!(result, SolverResult::Satisfiable);
                        continue;
                    }
                    let mut qcnf = solver.qcnf();
                    for &lit in &assumptions {
                        if lit.unsigned_abs() > universals {
                            qcnf.matrix.push(vec![crate::literal::Lit::from_dimacs(lit)]);
                        }
                    }
                    restrict_universals(&mut qcnf, &universal_part);
                    let expected = qcnf.brute_force();
                    assert_eq!(result, expected, "query verdict differs from the oracle");
                    if result == SolverResult::Satisfiable {
                        assert!(solver.verify(), "query certificate invalid");
                        check_model(&solver, universals, &assumptions);
                    }
                }
            }
        }
    }

    /// An unsatisfiable stack must yield a *complete* winning move for
    /// the universal player, and the move must really win: fixing it
    /// leaves the matrix unsatisfiable however the existentials are
    /// chosen. Checked against a brute-force replay, independent of the
    /// self-reduction that produced it.
    fn check_universal_move(solver: &IncrementalSolver, universals: u32) {
        let Some(move_) = solver.universal_witness_complete(&|_| false) else {
            panic!("an unsatisfiable stack has a winning universal move");
        };
        assert!(
            move_.iter().all(|l| l.unsigned_abs() <= universals),
            "the move assigns a non-universal variable: {move_:?}"
        );
        // replay: the instance restricted to the move must stay
        // unsatisfiable, i.e. no existential response exists
        let mut qcnf = solver.qcnf();
        for &raw in &move_ {
            let lit = crate::literal::Lit::from_dimacs(raw);
            qcnf.matrix.retain(|clause| !clause.contains(&lit));
            for clause in &mut qcnf.matrix {
                clause.retain(|&l| l != !lit);
            }
            for (_, vars) in &mut qcnf.prefix {
                vars.retain(|&v| v != lit.var());
            }
        }
        assert_eq!(
            qcnf.brute_force(),
            SolverResult::Unsatisfiable,
            "the reported winning move {move_:?} is answerable"
        );
    }

    fn check_model(solver: &IncrementalSolver, universals: u32, assumptions: &[i32]) {
        let model = solver.skolem_model().expect("satisfiable");
        let qcnf = solver.qcnf();
        for point in 0..(1u32 << universals) {
            let assignment: Vec<i32> = (1..=universals)
                .map(|v| {
                    let val = point & (1 << (v - 1)) != 0;
                    let v = i32::try_from(v).unwrap();
                    if val {
                        v
                    } else {
                        -v
                    }
                })
                .collect();
            // universal assumptions restrict the domain: the model only
            // covers points extending them
            if assumptions
                .iter()
                .any(|&l| l.unsigned_abs() <= universals && !assignment.contains(&l))
            {
                continue;
            }
            let values = model.evaluate(&assignment);
            let truth = |l: i32| -> bool {
                let var = l.unsigned_abs();
                let value = if var <= universals {
                    assignment.contains(&i32::try_from(var).unwrap())
                } else {
                    values.get(&i32::try_from(var).unwrap()).copied().unwrap_or(false)
                };
                (l > 0) == value
            };
            for clause in &qcnf.matrix {
                assert!(
                    clause.iter().any(|l| truth(l.to_dimacs())),
                    "model falsifies a clause at {assignment:?}"
                );
            }
            for &lit in assumptions {
                assert!(truth(lit), "model violates assumption {lit} at {assignment:?}");
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]
        #[test]
        fn differential_incremental(
            universals in 1u32..=3,
            existentials in 1u32..=4,
            script in proptest::collection::vec(
                (0u8..8, proptest::collection::vec(-7i32..=7, 1..=4)),
                1..=24,
            ),
            threshold in prop_oneof![proptest::strategy::Just(2u32), proptest::strategy::Just(5000u32)],
            continuation in proptest::bool::ANY,
        ) {
            let bound = i32::try_from(universals + existentials).unwrap();
            let script: Vec<(u8, Vec<i32>)> = script
                .into_iter()
                .map(|(a, clause)| {
                    let clause: Vec<i32> = clause
                        .into_iter()
                        .map(|l| {
                            let m = (l.unsigned_abs() % u32::try_from(bound).unwrap()) + 1;
                            let m = i32::try_from(m).unwrap();
                            if l < 0 { -m } else { m }
                        })
                        .collect();
                    (a, clause)
                })
                .collect();
            session(universals, existentials, &script, threshold, continuation);
        }
    }
}
