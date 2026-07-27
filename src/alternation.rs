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
//! succeeds once every candidate is answered), and a leaf the core's
//! certified Skolem model. Inverting ∀-expansion is not implemented,
//! so an instance that needed one answers `None`.
//!
//! Before either loop runs, a *small innermost universal block* is
//! enumerated away instead ([`expand_universal_block`]): ∀-expansion
//! removes an alternation outright, and at the innermost block only the
//! final existential block is copied — a three-block prefix collapses
//! to plain SAT. Only small blocks qualify, because CEGAR enumerates
//! just the relevant assignments while expansion pays for all of them.

use crate::{
    incdet::{IncDet, Options},
    incremental::IncrementalSolver,
    literal::{Lit, Var},
    qcnf::QCNF,
    QuantTy, SolverResult,
};
use std::collections::{HashMap, HashSet};

#[cfg(feature = "probe")]
pub static LEAF_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static LEAF_VARS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(feature = "probe")]
pub static LEAF_CLAUSES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
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

/// Budget for a *speculative* expansion — one that leaves more than two
/// blocks, so the result still goes through the per-level simplification
/// and the candidate loops rather than straight to the core. Those pay
/// per clause many times over, so they get far less room than an
/// expansion that collapses the prefix outright (measured: expanding
/// the depth-6 arbiter to 1.5M clauses left the loops unable to reach a
/// single leaf solve, while `BLOCKS4iii` happily hands 1.45M clauses to
/// the core because its expansion leaves one block).
const SPECULATIVE_EXPANSION_BUDGET: usize = 50_000;

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
    Fixed { assignments: Vec<Lit>, rest: Box<Strategy> },
    /// the constants an outermost existential block committed to
    Choose { constants: Vec<Lit>, rest: Box<Strategy> },
    /// one sub-strategy per enumerated cube of a universal block
    Split { cases: Vec<(Vec<Lit>, Strategy)> },
    /// the certified Skolem functions of a 2QBF leaf
    Leaf(Box<crate::incdet::model::SkolemModel>),
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
}

/// The result of an internal solve: the verdict, the refuting
/// assignment of an outermost universal block (for the ∃-loop above),
/// and a composed winning strategy when one is available.
struct Outcome {
    verdict: SolverResult,
    witness: Option<Vec<Lit>>,
    strategy: Option<Strategy>,
}

impl Outcome {
    fn verdict(verdict: SolverResult) -> Self {
        Self { verdict, witness: None, strategy: None }
    }

    fn sat(strategy: Option<Strategy>) -> Self {
        Self { verdict: SolverResult::Satisfiable, witness: None, strategy }
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
) -> (SolverResult, Option<Strategy>) {
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
    let mut expanded = false;
    loop {
        if current.prefix.len() <= 2 {
            break;
        }
        let Some((reduced, assigned)) = simplify(&current) else {
            return (SolverResult::Unsatisfiable, None);
        };
        forced.extend(assigned);
        if reduced.matrix.is_empty() {
            let strategy = (!expanded).then(|| Strategy::Fixed {
                assignments: forced.clone(),
                rest: Box::new(Strategy::Done),
            });
            return (SolverResult::Satisfiable, strategy);
        }
        current = normalized(&reduced);
        let Some(block) = expandable_block(&current, budget) else {
            break;
        };
        expanded = true;
        current = normalized(&expand_universal_block(&current, block));
    }
    let outcome = solve_normalized(&current, options);
    let strategy = outcome
        .strategy
        .filter(|_| !expanded)
        .map(|rest| Strategy::Fixed { assignments: forced.clone(), rest: Box::new(rest) });
    (outcome.verdict, strategy)
}

/// The internal solve additionally returns, on an unsatisfiable
/// verdict whose outermost block is universal, the refuting assignment
/// of that block — the expansion witness of the ∃-loop one level up
/// (already computed by the ∀-loop and by the 2QBF core; threading it
/// upgrades deep recursion from blocking-only to strong refinements).
fn solve_normalized(qcnf: &QCNF, options: Options) -> Outcome {
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
            return Outcome::sat(Some(Strategy::Fixed {
                assignments: forced,
                rest: Box::new(Strategy::Done),
            }));
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
            .then(|| Strategy::Leaf(Box::new(solver.skolem_model())));
        return Outcome { verdict, witness, strategy: wrap(forced, strategy) };
    }
    let inner = match qcnf.prefix[0].0 {
        QuantTy::Exists => expansion_loop(qcnf, options),
        QuantTy::Forall => forall_loop(qcnf, options),
    };
    Outcome { strategy: wrap(forced, inner.strategy), ..inner }
}

/// Prefixes a strategy with the literals a simplification pass forced.
fn wrap(forced: Vec<Lit>, strategy: Option<Strategy>) -> Option<Strategy> {
    let strategy = strategy?;
    if forced.is_empty() {
        return Some(strategy);
    }
    Some(Strategy::Fixed { assignments: forced, rest: Box::new(strategy) })
}

/// The dual candidate loop at a ∀-outermost block: search for a
/// refuting outer assignment; every answered candidate is blocked.
/// (Negating the matrix instead would cascade Tseitin gates through the
/// recursion and blow up; the dual loop keeps the matrix fixed. Strong
/// dual refinements would need regions of answered candidates — future
/// work, the weak blocking clause keeps the loop total.)
fn forall_loop(qcnf: &QCNF, options: Options) -> Outcome {
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
    let mut cases: Vec<(Vec<Lit>, Strategy)> = Vec::new();
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
            return Outcome::sat(composable.then_some(Strategy::Split { cases }));
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
        let outcome = solve_normalized(&restricted, options);
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
    let copies = 1usize << vars.len();
    let copied_vars: usize =
        qcnf.prefix[block + 1..].iter().map(|(_, vars)| vars.len()).sum::<usize>();
    let clauses = copies.checked_mul(qcnf.matrix.len())?;
    let fresh = copies.checked_mul(copied_vars)?;
    // expanding the innermost block removes one alternation; only when
    // at most two remain does the instance go straight to the core
    let collapses = qcnf.prefix.len() <= 3;
    let limit = if collapses { budget } else { budget.min(SPECULATIVE_EXPANSION_BUDGET) };
    (clauses <= limit && fresh <= limit).then_some(block)
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
fn expand_universal_block(qcnf: &QCNF, block: usize) -> QCNF {
    let ys: Vec<Var> = qcnf.prefix[block].1.clone();
    let after: Vec<(QuantTy, Vec<Var>)> = qcnf.prefix[block + 1..].to_vec();
    let after_set: HashSet<Var> = after.iter().flat_map(|(_, vars)| vars.iter().copied()).collect();
    let y_set: HashSet<Var> = ys.iter().copied().collect();
    let declared = qcnf.prefix.iter().flat_map(|(_, vars)| vars.iter()).map(|v| v.to_dimacs());
    let mentioned = qcnf.matrix.iter().flatten().map(|l| l.var().to_dimacs());
    let mut next = declared.chain(mentioned).max().unwrap_or(0) + 1;

    let mut copied_blocks: Vec<Vec<Var>> = vec![Vec::new(); after.len()];
    let mut matrix: Vec<Vec<Lit>> = Vec::new();
    for point in 0..1u64 << ys.len() {
        // the assignment of this copy, and fresh names for everything
        // bound after the expanded block
        let assigned: HashSet<Lit> = ys
            .iter()
            .enumerate()
            .map(|(i, &v)| if point >> i & 1 == 1 { Lit::positive(v) } else { Lit::negative(v) })
            .collect();
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
    }

    let mut prefix: Vec<(QuantTy, Vec<Var>)> = qcnf.prefix[..block].to_vec();
    for ((quant, _), vars) in after.iter().zip(copied_blocks) {
        prefix.push((*quant, vars));
    }
    QCNF { prefix, matrix }
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
fn expansion_loop(qcnf: &QCNF, options: Options) -> Outcome {
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
                    .then(|| solver.skolem_model().map(|m| Strategy::Leaf(Box::new(m))))
                    .flatten();
                (verdict, witness, strategy)
            }
            None => {
                // the recursion hands back the refuting assignment of the
                // block below, which is exactly this loop's expansion
                // witness
                let restricted = restrict(qcnf, &candidate, 1);
                let outcome = solve_normalized(&normalized(&restricted), options);
                (outcome.verdict, outcome.witness, outcome.strategy)
            }
        };
        match verdict {
            SolverResult::Satisfiable => {
                // this candidate wins: it commits the outer block to
                // constants, the sub-strategy handles the rest
                return Outcome::sat(
                    sub_strategy.map(|rest| Strategy::Choose {
                        constants: candidate,
                        rest: Box::new(rest),
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
                }
            } else {
                prop_assert!(
                    strategy.is_none(),
                    "a strategy was produced for an unsatisfiable instance:\n{}",
                    qcnf
                );
            }
        }
        Ok(())
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
