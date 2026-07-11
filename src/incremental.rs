//! An incremental 2QBF solving API.
//!
//! The solver maintains an *assertion stack* of frames holding variable
//! declarations and clauses ([`IncrementalSolver::push`] /
//! [`IncrementalSolver::pop`]), solves the conjunction of all frames under
//! a ∀∃ prefix, and extracts piecewise Skolem functions from satisfiable
//! results.
//!
//! Incrementality (this is the correctness-first baseline; see
//! `RESEARCH.md` for the planned in-place variant): every solve runs a
//! fresh core solver over the current stack, but the clauses *learnt*
//! during a solve are carried to future solves. Learnt clauses are
//! resolvents of the matrix they were learnt under, so they remain valid
//! for every extension of that matrix; each carried clause is therefore
//! tagged with the stack depth at which it was learnt and dropped as soon
//! as that depth is popped. Assumption-based solving
//! ([`IncrementalSolver::solve_with_assumptions`]) is sugar for a push /
//! unit clauses / solve / pop sequence, so clauses learnt under
//! assumptions are dropped when the assumptions are retracted.

use crate::{
    incdet::{model::SkolemModel, IncDet, Options},
    qcnf::QCNF,
    QuantTy, SolverResult,
};

/// One frame of the assertion stack.
#[derive(Debug, Default, Clone)]
struct Frame {
    universals: Vec<u32>,
    existentials: Vec<u32>,
    clauses: Vec<Vec<i32>>,
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
    /// the solver and result of the most recent solve, for model queries
    last: Option<(SolverResult, IncDet)>,
    /// the next fresh variable for [`IncrementalSolver::fresh_var`]
    next_var: u32,
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
            last: None,
            next_var: 1,
        }
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
        if self.frames.len() <= 1 {
            return false;
        }
        self.frames.pop();
        let depth = self.frames.len() - 1;
        self.learnt.retain(|(d, _)| *d <= depth);
        self.last = None;
        true
    }

    /// The current stack depth (0 for the base frame).
    #[must_use]
    pub fn depth(&self) -> usize {
        self.frames.len() - 1
    }

    /// Builds the 2QBF instance for the current stack, including the
    /// carried learnt clauses.
    fn qcnf(&self) -> QCNF {
        let universals: Vec<u32> =
            self.frames.iter().flat_map(|f| f.universals.iter().copied()).collect();
        let existentials: Vec<u32> =
            self.frames.iter().flat_map(|f| f.existentials.iter().copied()).collect();
        let clauses: Vec<&[i32]> = self
            .frames
            .iter()
            .flat_map(|f| f.clauses.iter().map(Vec::as_slice))
            .chain(self.learnt.iter().map(|(_, c)| c.as_slice()))
            .collect();
        let mut prefix: Vec<(QuantTy, &[u32])> = Vec::new();
        if !universals.is_empty() {
            prefix.push((QuantTy::Forall, &universals[..]));
        }
        prefix.push((QuantTy::Exists, &existentials[..]));
        QCNF::new(&prefix, &clauses)
    }

    /// Solves the conjunction of the assertion stack.
    pub fn solve(&mut self) -> SolverResult {
        let qcnf = self.qcnf();
        let mut solver = IncDet::from_qcnf_with_options(&qcnf, self.options);
        let result = solver.solve();
        let depth = self.depth();
        self.learnt.extend(solver.learnt_clauses().into_iter().map(|c| (depth, c)));
        self.last = Some((result, solver));
        result
    }

    /// Solves the assertion stack under the given assumption literals
    /// (temporary unit clauses, retracted afterwards together with
    /// everything learnt from them).
    pub fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> SolverResult {
        let clauses: Vec<Vec<i32>> = assumptions.iter().map(|&lit| vec![lit]).collect();
        self.solve_with_clauses(&clauses)
    }

    /// Solves the assertion stack under temporary clauses, retracted
    /// afterwards together with everything learnt from them. Unlike
    /// [`IncrementalSolver::add_clause`], this supports clauses that do
    /// not stay implied when the ambient formula changes (a later solve
    /// must not resolve against them).
    pub fn solve_with_clauses(&mut self, clauses: &[Vec<i32>]) -> SolverResult {
        self.push();
        for clause in clauses {
            self.add_clause(clause);
        }
        let result = self.solve();
        let last = self.last.take();
        self.pop();
        self.last = last;
        result
    }

    /// The result of the most recent solve, if the stack has not changed
    /// since.
    #[must_use]
    pub fn last_result(&self) -> Option<SolverResult> {
        self.last.as_ref().map(|(r, _)| *r)
    }

    /// The piecewise Skolem model of the most recent solve. Only valid if
    /// the last result was [`SolverResult::Satisfiable`].
    #[must_use]
    pub fn skolem_model(&self) -> Option<SkolemModel> {
        match &self.last {
            Some((SolverResult::Satisfiable, solver)) => Some(solver.skolem_model()),
            _ => None,
        }
    }

    /// Verifies the Skolem functions of the most recent satisfiable solve.
    #[must_use]
    pub fn verify(&self) -> bool {
        matches!(&self.last, Some((SolverResult::Satisfiable, solver)) if solver.verify_skolem_functions())
    }

    /// The verified winning move of the universal player for the most
    /// recent unsatisfiable solve: a (partial) assignment of the
    /// universal variables (DIMACS literals) such that no extension
    /// admits an existential response. `None` if the last result was not
    /// unsatisfiable or the recorded candidate did not pass verification
    /// (see [`IncDet::unsat_witness`]).
    #[must_use]
    pub fn universal_witness(&self) -> Option<Vec<i32>> {
        match &self.last {
            Some((SolverResult::Unsatisfiable, solver)) => solver.unsat_witness(),
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
    fn session(universals: u32, existentials: u32, script: &[(u8, Vec<i32>)], threshold: u32) {
        let options = Options { case_split_threshold: threshold, ..Options::default() };
        let mut solver = IncrementalSolver::new(options);
        for v in 1..=universals {
            solver.declare_universal(v);
        }
        for v in (universals + 1)..=(universals + existentials) {
            solver.declare_existential(v);
        }
        let mut depth = 0usize;
        for (action, clause) in script {
            match action % 4 {
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
                _ => {
                    let result = solver.solve();
                    let expected = solver.qcnf().brute_force();
                    assert_eq!(result, expected, "verdict differs from the oracle");
                    if result == SolverResult::Satisfiable {
                        assert!(solver.verify(), "certificate invalid");
                        check_model(&solver, universals);
                    }
                }
            }
        }
    }

    fn check_model(solver: &IncrementalSolver, universals: u32) {
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
            session(universals, existentials, &script, threshold);
        }
    }
}
