//! Implementation of the incremental determinization algorithm.

use self::{
    conflict::{analysis::ConflictAnalysis, check::ConflictCheck},
    graph::ImplGraph,
    skolem::Skolem,
    stats::Statistics,
    vsids::Vsids,
    watch::{Watch, WatchList},
};
use crate::{
    clause::alloc::{Allocator, ClauseId},
    datastructure::{heap::VarHeap, VarVec},
    incdet::graph::Impl,
    literal::{filter_lit, filter_var, Lit, LitSlice, Var},
    qcdcl::propagation::{
        assignment::{Assignment, Value},
        trail::{DecLvl, Trail},
    },
    qdimacs::FromQdimacs,
    sat::varisat::Varisat,
    QuantTy, SolverResult,
};
use std::{
    collections::{HashSet, VecDeque},
    mem,
    time::Instant,
};
use tracing::{debug, error, info, trace};
use varisat::{ExtendFormula, Solver};

pub(crate) mod conflict;
pub(crate) mod graph;
pub(crate) mod skolem;
pub(crate) mod stats;
pub(crate) mod vsids;
pub(crate) mod watch;

#[cfg(test)]
mod test;

const ENABLE_CONSTANT_PROPAGATION: bool = false;

#[derive(Debug, Default)]
pub struct IncDet {
    vars: VarVec<VarData>,
    prefix: Vec<Scope>,
    clauses: Vec<ClauseId>,
    allocator: Allocator,
    skolem: Skolem,
    // queue for next propagation tests
    propagation: VarHeap<usize>,
    constant_propagation: VecDeque<Lit>,
    assignment: Assignment,
    trail: Trail,
    watches: WatchList,
    graph: ImplGraph,
    conflict_analysis: ConflictAnalysis,
    conflict_check: ConflictCheck<Varisat>,
    dec_lvls: VarVec<Option<DecLvl>>,
    vsids: Vsids,
    /// set to true if the empty clause was added
    conflicted: bool,
    stats: Statistics,
}

#[derive(Debug, Clone, Default)]
struct VarData {
    scope: Option<ScopeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ScopeId(usize);

#[derive(Debug, Clone)]
struct Scope {
    id: ScopeId,
    quantifier: QuantTy,
    variables: Vec<Var>,
}

#[derive(Debug, Clone)]
pub(crate) struct Conflict {
    var: Var,
    assignment: HashSet<Lit>,
}

#[derive(Debug, Copy, Clone)]
enum Propagation {
    Constant(Lit),
    Function(Var),
}

impl FromQdimacs for IncDet {
    fn set_num_variables(&mut self, variables: u32) {
        self.set_var_count(variables.try_into().unwrap());
    }

    fn set_num_clauses(&mut self, _clauses: u32) {}

    fn quantify(&mut self, quant: QuantTy, vars: &[Var]) {
        self._quantify(quant, vars);
    }

    fn add_clause(&mut self, lits: &[Lit]) {
        self._add_clause(lits);
    }
}

impl IncDet {
    #[cfg(test)]
    fn from_qcnf(qcnf: &crate::qcnf::QCNF) -> Self {
        let mut solver = Self::default();
        for (qty, vars) in &qcnf.prefix {
            solver._quantify(*qty, vars);
        }
        for clause in &qcnf.matrix {
            solver._add_clause(clause);
        }
        solver
    }

    fn set_var_count(&mut self, count: usize) {
        self.vars.set_var_count(count);
        self.skolem.set_var_count(count);
        self.assignment.set_var_count(count);
        self.watches.set_var_count(count);
        self.graph.set_var_count(count);
        self.dec_lvls.set_var_count(count);
        self.vsids.set_var_count(count);
        self.conflict_check.set_var_count(count);
        self.propagation.set_var_count(count);
    }

    fn _quantify(&mut self, quant: QuantTy, vars: &[Var]) {
        let id = match self.prefix.last_mut() {
            Some(scope) if scope.quantifier == quant => {
                scope.variables.extend_from_slice(vars);
                scope.id
            }
            _ => {
                let id = ScopeId(self.prefix.len());
                let scope = Scope { id, quantifier: quant, variables: vars.into() };
                self.prefix.push(scope);
                id
            }
        };
        for &var in vars {
            if var.as_index() >= self.vars.get_var_count() {
                self.set_var_count(var.as_index() + 1);
            }
            // let var_data = self.vars.get_or_default(var);
            let var_data = &mut self.vars[var];
            let other = var_data.scope.get_or_insert(id);
            if *other != id {
                // variable is bound twice, remove it from outer scope
                self.prefix[other.0].variables.retain(|&other| other != var);
                *other = id;
            }
        }
    }

    fn _add_clause(&mut self, lits: &[Lit]) {
        debug!("Add clause: {}", LitSlice::from(lits));
        assert!(
            lits.iter().all(|&l| self.vars.get(l.var()).map_or(false, |data| data.scope.is_some())),
            "unbound variables are not supported"
        );
        let mut lits = Vec::from(lits);
        lits.sort_unstable();
        lits.dedup();
        if lits.iter().zip(lits.iter().skip(1)).any(|(&left, &right)| left == !right) {
            // Detected tautology clause, do not add to matrix.
            // Note: as literals are deduplicated and sorted by variable index,
            // literals of opposing signs have to be consecutive in the clause.
            return;
        }

        // universal reduction
        if let Some(max_scope) = lits
            .iter()
            .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
            .map(|lit| self.vars[lit.var()].scope())
            .max()
        {
            // remove universal literals that are bound after every existential variable
            lits.retain(|lit| self.vars[lit.var()].scope() <= max_scope);
        } else {
            // no existential variables
            tracing::warn!("empty clause was added, instance is unsatisfiable");
            self.conflicted = true;
        }

        let clause_id = self.allocator.add(&lits);

        // check if there is only one existential variable
        let mut singleton = None;
        let mut no_universals = true;
        for lit in &lits {
            if self.vars[lit.var()].is_existential(&self.prefix) {
                match singleton {
                    None => singleton = Some(lit),
                    Some(_) => {
                        // there are two existential variables
                        singleton = None;
                        break;
                    }
                }
            } else {
                no_universals = false;
            }
        }
        if let Some(&lit) = singleton {
            self.skolem[lit].add_implication(clause_id, DecLvl::ROOT);
            if ENABLE_CONSTANT_PROPAGATION && no_universals {
                self.constant_propagation.push_back(lit);
            } else {
                self.propagation
                    .add_and_set(lit.var(), self.skolem[lit].len() + self.skolem[!lit].len());
            }
            for univ in lits.iter().filter(|l| self.vars[l.var()].is_universal(&self.prefix)) {
                self.graph[lit].push(Impl {
                    lit: univ.negated(),
                    clause: clause_id,
                    dec_lvl: DecLvl::ROOT,
                });
            }
        } else {
            // TODO: handle constant functions
            self.clauses.push(clause_id);
            if self.watches.enabled() {
                let mut unassigned = lits
                    .iter()
                    .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
                    .filter(|l| !self.assignment.is_assigned(l.var()));
                let watch1 = *unassigned.next().expect("there is at least one unassigned lit");
                self.watches.add_watch(watch1, Watch { clause: clause_id });
                if let Some(&watch2) = unassigned.next() {
                    self.watches.add_watch(watch2, Watch { clause: clause_id });
                } else {
                    // select an arbitrary existential literal from largest decision level
                    let max_lvl = lits
                        .iter()
                        .filter(filter_var(watch1.var()))
                        .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
                        .filter_map(|l| self.dec_lvls[l.var()])
                        .max()
                        .expect("there is at least one assigned existential literal");
                    let watch2 = *lits
                        .iter()
                        .find(|l| self.dec_lvls[l.var()] == Some(max_lvl))
                        .expect("There is a literal with the provided decision level");
                    self.watches.add_watch(watch2, Watch { clause: clause_id });
                    self.skolem[watch1].add_implication(clause_id, max_lvl);
                    self.propagation.add_and_set(
                        watch1.var(),
                        self.skolem[watch1].len() + self.skolem[!watch1].len(),
                    );
                    self.graph[watch1].push(Impl {
                        lit: watch2.negated(),
                        clause: clause_id,
                        dec_lvl: max_lvl,
                    });
                }
            }
        }
    }

    /// Solves the QBF using incremental determinization.
    pub fn solve(&mut self) -> SolverResult {
        let instant = Instant::now();
        let result = self._solve();
        self.stats.global.solve_time = instant.elapsed();
        info!("\n{:#?}", self.stats);
        result
    }

    fn _solve(&mut self) -> SolverResult {
        if self.prefix.len() > 2 {
            error!("Only 2QBF is currently supported");
            return SolverResult::Unknown;
        }
        if self.conflicted {
            return SolverResult::Unsatisfiable;
        }
        self.build_watchlist();
        self.build_vsids_heap();
        let mut initial = Some(());
        loop {
            if let Some(conflict) = self.propagate() {
                debug!("{conflict:?}");
                if let Some(result) = self.handle_conflict(conflict) {
                    return result;
                }
                continue;
            }
            if let Some(_) = initial.take() {
                info!("number of initial deterministic vars: {}", self.trail.len());
            }
            let Some(var) = self.next_decision_variable() else {
                break;
            };
            self.stats.global.decisions += 1;
            assert!(!self.assignment.is_assigned(var));
            let neg_count = self.skolem[Lit::negative(var)].lit_count(&self.allocator);
            let pos_count = self.skolem[Lit::positive(var)].lit_count(&self.allocator);
            let decision =
                if neg_count <= pos_count { Lit::negative(var) } else { Lit::positive(var) };
            trace!(
                "decide {decision} (neg: {}/{}, pos: {}/{})",
                neg_count,
                self.skolem[Lit::negative(var)].len(),
                pos_count,
                self.skolem[Lit::positive(var)].len()
            );
            // check if the decision leads to a conflict
            if let Some(assignment) = self.is_conflicted(var, Some(decision)) {
                trace!("{} is conflicted", var);
                if let Some(result) = self.handle_conflict(Conflict { var, assignment }) {
                    return result;
                }
                continue;
            }
            // TODO: is_constant
            self.assign_and_propagate(decision, true, false);
        }
        SolverResult::Satisfiable
    }

    fn build_watchlist(&mut self) {
        self.watches.clear();
        self.watches.set_enabled();
        for &cid in &self.clauses {
            let clause = &self.allocator[cid];
            let mut iter = clause
                .lits()
                .iter()
                .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix));
            let watch1 = *iter.next().expect("every clause has at least 2 existential variables");
            let watch2 = *iter.next().expect("every clause has at least 2 existential variables");
            self.watches.add_watch(watch1, Watch { clause: cid });
            self.watches.add_watch(watch2, Watch { clause: cid });
        }
    }

    fn build_vsids_heap(&mut self) {
        self.vars
            .iter()
            .filter(|(_, data)| data.is_existential(&self.prefix))
            .for_each(|(var, _)| self.vsids.add(var));
    }

    pub(crate) fn next_decision_variable(&self) -> Option<Var> {
        self.vsids.peek()
    }

    /// The next entry to propagate.
    /// We're always propagating constants first.
    fn next_propagation(&mut self) -> Option<Propagation> {
        if let Some(lit) = self.constant_propagation.pop_front() {
            Some(Propagation::Constant(lit))
        } else if let Some(var) = self.propagation.pop() {
            self.propagation.update_value(var, |_| 0);
            Some(Propagation::Function(var))
        } else {
            None
        }
    }

    fn propagate(&mut self) -> Option<Conflict> {
        while let Some(entry) = self.next_propagation() {
            match entry {
                Propagation::Constant(lit) => {
                    let var = lit.var();
                    if let Some(value) = self.assignment[var] {
                        match value {
                            Value::True => {
                                if lit.is_positive() {
                                    continue;
                                } else {
                                    todo!("{value:?} {lit}");
                                }
                            }
                            Value::False => {
                                if lit.is_negative() {
                                    continue;
                                } else {
                                    todo!("{value:?} {lit}");
                                }
                            }
                            _ => todo!("{value:?} {lit}"),
                        }
                    }
                    for imp in self.skolem[!lit].implications() {
                        let clause = &self.allocator[imp];
                        println!("{lit} {clause}");
                        let mut assignment = HashSet::new();
                        for &l in clause.lits().iter().filter(filter_lit(!lit)) {
                            assert!(self.vars[l.var()].is_universal(&self.prefix));
                            assignment.insert(!l);
                        }
                        return Some(Conflict { var: lit.var(), assignment });
                    }
                    if self.assignment.is_assigned(var) {
                        continue;
                    }
                    self.assign_and_propagate(lit, false, true);
                }
                Propagation::Function(var) => {
                    if self.assignment.is_assigned(var) {
                        continue;
                    }
                    if !self.has_unique_consequence(var) {
                        debug_assert!(!self.propagation.contained(var));
                        continue;
                    }
                    trace!("{} has unique consquence", var);
                    if let Some(assignment) = self.is_conflicted(var, None) {
                        trace!("{} is conflicted", var);
                        return Some(Conflict { var, assignment });
                    }
                    trace!("{} is deterministic", var);
                    let lit = if self.skolem[Lit::positive(var)].len()
                        <= self.skolem[Lit::negative(var)].len()
                    {
                        Lit::positive(var)
                    } else {
                        Lit::negative(var)
                    };
                    self.assign_and_propagate(lit, false, false);
                }
            }
        }
        None
    }

    // update internal representation to reflect that `lit` is assigned.
    pub(crate) fn assign_and_propagate(&mut self, lit: Lit, is_decision: bool, is_constant: bool) {
        if is_decision {
            self.trail.add_decision(lit);
        } else {
            self.trail.push(lit);
        }
        if is_constant {
            self.assignment.assign_constant(lit);
        } else {
            self.assignment.assign_function(lit);
        }
        self.vsids.remove(lit.var());
        self.add_definition_to_conflict_check(lit, is_decision);
        if is_constant {
            self.propagate_constant(lit);
        } else {
            self.propagate_function(lit.var());
        }
    }

    fn propagate_constant(&mut self, lit: Lit) {
        debug!("propagate constant {lit}");
        self.stats.skolem.constant_propagations += 1;
        self.dec_lvls[lit.var()] = Some(self.trail.decision_level());
        let mut watches = mem::take(&mut self.watches[!lit]);
        watches.retain(|watch: &Watch| {
            let clause = &self.allocator[watch.clause];
            trace!("Propagate {lit} in clause {clause}");
            let has_universals = clause
                .lits()
                .iter()
                .find(|&&l| self.vars[l.var()].is_universal(&self.prefix))
                .is_some();

            todo!();
        });
        self.watches[lit] = watches;
    }

    /// Use watchlist to determine more implications
    fn propagate_function(&mut self, var: Var) {
        debug!("propagate function {var}");
        self.stats.skolem.function_propagations += 1;
        self.dec_lvls[var] = Some(self.trail.decision_level());
        for lit in [Lit::positive(var), Lit::negative(var)] {
            let mut watches = mem::take(&mut self.watches[lit]);
            watches.retain(|watch: &Watch| {
                let clause = &self.allocator[watch.clause];
                trace!("Propagate {var} in clause {clause}");
                // iterate over existential literals that are not watched
                let mut iter = clause
                    .lits()
                    .iter()
                    .filter(|l| self.vars[l.var()].is_existential(&self.prefix))
                    .filter(|l| !self.assignment.is_assigned(l.var()))
                    .filter(|l| l.var() != var)
                    .filter(|&&l| self.watches[l].iter().all(|w| w.clause != watch.clause));
                if let Some(&l) = iter.next() {
                    // new watched literal
                    self.watches[l].push(Watch { clause: watch.clause });
                    trace!("New watched lit {l} in clause {}", clause);
                    return false;
                }
                let propagated_lit = *clause
                    .lits()
                    .iter()
                    .find(|lit| lit.var() == var)
                    .expect("this is the propagated literal");
                // there is no other existential literal to watch for,
                // thus, this is an implication clause for the remaining variable
                let Some(&lit) = clause
                .lits()
                .iter()
                .filter(|l| self.vars[l.var()].is_existential(&self.prefix))
                .filter(|l| !self.assignment.is_assigned(l.var()))
                .filter(|l| l.var() != var)
                .find(|&&l| self.watches[l].iter().any(|w| w.clause == watch.clause))
                else {
                    // all literals are assigned
                    return true;
                };
                trace!("New implication clause for {}: {}", lit, clause);

                self.skolem[lit].add_implication(watch.clause, self.trail.decision_level());
                self.propagation
                    .add_and_set(lit.var(), self.skolem[lit].len() + self.skolem[!lit].len());
                // add the propagation reason to implication graph
                self.graph[lit].push(Impl {
                    lit: propagated_lit.negated(),
                    clause: watch.clause,
                    dec_lvl: self.trail.decision_level(),
                });
                true
            });
            self.watches[lit] = watches;
        }
    }

    fn has_unique_consequence(&mut self, var: Var) -> bool {
        self.stats.skolem.local_det_checks += 1;
        let mut solver = Solver::new();
        for cid in self.skolem[Lit::positive(var)]
            .implications()
            .chain(self.skolem[Lit::negative(var)].implications())
        {
            let clause = &self.allocator[cid];
            // todo
            // assert!(clause.lits().len() > 1);
            solver.add_clause(
                &clause
                    .iter()
                    .filter(|l| l.var() != var)
                    .map(|l| varisat::Lit::from_dimacs(l.to_dimacs().try_into().unwrap()))
                    .collect::<Vec<_>>(),
            );
        }
        let result = solver.solve().unwrap();
        !result
    }

    fn iter_implication_clauses(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.trail.iter().flat_map(|&lit| {
            [lit, lit.negated()].into_iter().flat_map(|lit| self.skolem[lit].implications())
        })
    }

    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        self.trail.backtrack_to(lvl, |assigned_lit| {
            self.assignment.unassign(assigned_lit.var());
            self.dec_lvls[assigned_lit.var()] = None;
            self.vsids.add(assigned_lit.var());
            self.conflict_check.forget(assigned_lit.var());
        });
        self.skolem.backtrack_to(lvl);
        self.propagation.clear();
        self.graph.backtrack_to(lvl);
        self.conflict_check.backtrack_to(lvl);
    }

    pub(crate) fn handle_conflict(&mut self, conflict: Conflict) -> Option<SolverResult> {
        if self.trail.decision_level().is_root() {
            return Some(SolverResult::Unsatisfiable);
        }
        let Ok(backtrack_to) = self.analyze(conflict) else {
                    return Some( SolverResult::Unsatisfiable);
                };
        debug!("conflict analysis: backtrack to {backtrack_to:?}");
        self.backtrack_to(backtrack_to);
        let clause = self.conflict_analysis.clause().to_owned();
        self._add_clause(&clause);
        self.stats.global.added_clauses += 1;
        assert!(!self.conflicted, "empty clause cannot be added through conflict analysis");
        None
    }
}

impl From<Lit> for varisat::Lit {
    fn from(lit: Lit) -> Self {
        varisat::Lit::from_dimacs(lit.to_dimacs().try_into().unwrap())
    }
}

impl From<varisat::Lit> for Lit {
    fn from(vlit: varisat::Lit) -> Self {
        Lit::from_dimacs(vlit.to_dimacs().try_into().unwrap())
    }
}

impl VarData {
    fn scope(&self) -> ScopeId {
        self.scope.expect("all variables are bound")
    }

    fn is_existential(&self, prefix: &[Scope]) -> bool {
        let scope = &prefix[self.scope().0];
        scope.quantifier == QuantTy::Exists
    }

    fn is_universal(&self, prefix: &[Scope]) -> bool {
        !self.is_existential(prefix)
    }
}
