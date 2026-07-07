use crate::{
    datastructure::VarVec,
    incdet::propagation::trail::{DecLvl, Trail},
    incdet::{vsids::Vsids, Conflict, IncDet, Scope, VarData},
    literal::{filter_lit, filter_var, Lit, LitSlice},
};
use tracing::{debug, trace};

#[derive(Debug, Clone, Default)]
pub(crate) struct ConflictAnalysis {
    clause: Vec<Lit>,
    current_level_count: usize,
}

impl ConflictAnalysis {
    pub(crate) fn clause(&self) -> &[Lit] {
        &self.clause
    }

    fn reset(&mut self) {
        self.clause.clear();
        self.current_level_count = 0;
    }

    fn add_literal(
        &mut self,
        vars: &VarVec<VarData>,
        prefix: &[Scope],
        dec_lvls: &VarVec<Option<DecLvl>>,
        trail: &Trail,
        vsids: &mut Vsids,
        lit: Lit,
    ) {
        if self.clause.contains(&lit) {
            return;
        }
        self.clause.push(lit);
        if vars[lit.var()].is_universal(prefix) {
            return;
        }
        let dec_lvl = dec_lvls[lit.var()].expect(
            "there has to be at least one implication graph entry for deterministic existentials",
        );
        if dec_lvl == trail.decision_level() {
            self.current_level_count += 1;
        }
        vsids.bump(lit.var());
    }

    fn get_backtrack_level(
        &self,
        dec_lvls: &VarVec<Option<DecLvl>>,
        current_lvl: DecLvl,
    ) -> DecLvl {
        self.clause
            .iter()
            .map(|&l| dec_lvls[l.var()].unwrap_or(DecLvl::ROOT))
            .filter(|&lvl| lvl != current_lvl)
            .max()
            .unwrap_or(DecLvl::ROOT)
    }

    /// The deepest decision level of an existential literal of the clause.
    /// Universal literals are ignored: case assumptions carry decision
    /// levels, but the clause must assert its deepest existential literal,
    /// not a case assumption.
    fn clause_max_existential_lvl(
        &self,
        vars: &VarVec<VarData>,
        prefix: &[Scope],
        dec_lvls: &VarVec<Option<DecLvl>>,
    ) -> DecLvl {
        assert_eq!(self.current_level_count, 0);
        self.clause
            .iter()
            .filter(|l| vars[l.var()].is_existential(prefix))
            .map(|&l| dec_lvls[l.var()].unwrap_or(DecLvl::ROOT))
            .max()
            .unwrap_or(DecLvl::ROOT)
    }

    /// The deepest decision level among the clause literals that lies
    /// strictly below `below`. Backtracking there unassigns every literal
    /// at level `below` while keeping the remaining premises (including
    /// case assumptions) intact.
    fn get_backtrack_level_below(
        &self,
        dec_lvls: &VarVec<Option<DecLvl>>,
        below: DecLvl,
    ) -> DecLvl {
        self.clause
            .iter()
            .map(|&l| dec_lvls[l.var()].unwrap_or(DecLvl::ROOT))
            .filter(|&lvl| lvl < below)
            .max()
            .unwrap_or(DecLvl::ROOT)
    }
}

impl IncDet {
    pub(crate) fn analyze(&mut self, conflict: &Conflict) -> Result<DecLvl, ()> {
        self.conflict_analysis.reset();
        self.vsids.bump(conflict.var);
        self.clause_activity.decay();

        // start with the nucleus (-l, l)
        for implication in &self.graph[conflict.var.negative()] {
            let other = &self.allocator[implication.clause];
            if other.iter().any(|l| conflict.assignment.contains(l)) {
                continue;
            }
            self.clause_activity.bump(implication.clause);
            for &lit in other.iter().filter(filter_lit(conflict.var.negative())) {
                self.conflict_analysis.add_literal(
                    &self.vars,
                    &self.prefix,
                    &self.dec_lvls,
                    &self.trail,
                    &mut self.vsids,
                    lit,
                );
            }
            break;
        }
        for implication in &self.graph[conflict.var.positive()] {
            let other = &self.allocator[implication.clause];
            if other.iter().any(|l| conflict.assignment.contains(l)) {
                continue;
            }
            self.clause_activity.bump(implication.clause);
            for &lit in other.iter().filter(filter_lit(conflict.var.positive())) {
                self.conflict_analysis.add_literal(
                    &self.vars,
                    &self.prefix,
                    &self.dec_lvls,
                    &self.trail,
                    &mut self.vsids,
                    lit,
                );
            }
            break;
        }
        tracing::debug!(
            "conflict clause before analysis: {}",
            LitSlice::from(self.conflict_analysis.clause.as_slice())
        );
        if self.conflict_analysis.current_level_count == 0 {
            return self.analyze_below_conflict_level();
        } else if self.conflict_analysis.current_level_count <= 1 {
            self.minimize_learnt_clause(conflict);
            let backtrack_to = self
                .conflict_analysis
                .get_backtrack_level(&self.dec_lvls, self.trail.decision_level());
            self.vsids.decay();
            tracing::debug!("Backtrack to level {backtrack_to}");
            return Ok(backtrack_to);
        }
        for &lit in self.trail.iter().rev() {
            trace!("Rev trail lit: {lit}");
            if !self.conflict_analysis.clause.iter().any(|&l| l.var() == lit.var()) {
                // trail literal is not contained in clause
                continue;
            }
            let lit =
                if self.conflict_analysis.clause.contains(&lit) { lit.negated() } else { lit };
            for implication in &self.graph[lit] {
                let reason = implication.reason(&self.allocator);

                if !reason.is_implied(lit, &conflict.assignment) {
                    continue;
                }
                trace!("{lit} reason {reason}");
                self.clause_activity.bump(implication.clause);
                self.conflict_analysis.current_level_count -= 1;
                self.conflict_analysis.clause.retain(|l| l.var() != lit.var());
                for l in reason.iter().filter(filter_var(lit.var())) {
                    self.conflict_analysis.add_literal(
                        &self.vars,
                        &self.prefix,
                        &self.dec_lvls,
                        &self.trail,
                        &mut self.vsids,
                        *l,
                    );
                }
                break;
            }
            debug!("derived clause: {}", LitSlice::from(self.conflict_analysis.clause.as_slice()));
            if self.conflict_analysis.current_level_count <= 1 {
                break;
            }
        }

        self.minimize_learnt_clause(conflict);

        assert_eq!(self.conflict_analysis.current_level_count, 1);
        let backtrack_to =
            self.conflict_analysis.get_backtrack_level(&self.dec_lvls, self.trail.decision_level());

        self.vsids.decay();

        debug!("Backtrack to level {backtrack_to}");
        Ok(backtrack_to)
    }

    /// Resolves a conflict clause with no existential literal at the
    /// conflict level: the backtrack must go strictly below the deepest
    /// existential literal so the clause asserts it (case assumptions may
    /// sit at higher levels). A clause without existential literals above
    /// the root level refutes the instance.
    fn analyze_below_conflict_level(&mut self) -> Result<DecLvl, ()> {
        let max_lvl = self.conflict_analysis.clause_max_existential_lvl(
            &self.vars,
            &self.prefix,
            &self.dec_lvls,
        );
        if max_lvl == DecLvl::ROOT {
            tracing::trace!("Conflict: max-lvl == root level");
            return Err(());
        }
        let backtrack_to =
            self.conflict_analysis.get_backtrack_level_below(&self.dec_lvls, max_lvl);
        self.vsids.decay();
        tracing::debug!("Backtrack to level {backtrack_to}");
        Ok(backtrack_to)
    }

    fn minimize_learnt_clause(&mut self, conflict: &Conflict) {
        trace!(
            "clause minimization for clause {}",
            LitSlice::from(self.conflict_analysis.clause.as_slice())
        );
        let mut cache = std::collections::HashMap::new();
        let mut redundant = Vec::new();
        for &lit in &self.conflict_analysis.clause {
            trace!("{lit}");
            let dec_lvl = self.dec_lvls[lit.var()].unwrap_or(DecLvl::ROOT);
            if dec_lvl == self.trail.decision_level() {
                // We keep the single literal at the current decision level
                continue;
            }
            if self.is_literal_redundant(lit, conflict, &mut cache) {
                redundant.push(lit);
            }
        }
        trace!("Redundant literals: {}", LitSlice::from(redundant.as_slice()));

        self.conflict_analysis.clause.retain(|l| !redundant.contains(l));

        debug!(
            "learnt clause after minimization: {}",
            LitSlice::from(self.conflict_analysis.clause.as_slice())
        );
    }

    /// Checks whether `lit` is implied by the remaining literals of the
    /// learnt clause and can therefore be removed.
    ///
    /// The check recurses along the implication graph, whose edges always
    /// point to strictly earlier trail positions, so the recursion is
    /// well-founded. Results are memoized in `cache` to avoid re-exploring
    /// shared sub-graphs.
    fn is_literal_redundant(
        &self,
        lit: Lit,
        conflict: &Conflict,
        cache: &mut std::collections::HashMap<Lit, bool>,
    ) -> bool {
        trace!("check if {lit} is redundant");

        if let Some(&redundant) = cache.get(&lit) {
            return redundant;
        }
        let redundant = self.is_literal_redundant_uncached(lit, conflict, cache);
        cache.insert(lit, redundant);
        redundant
    }

    fn is_literal_redundant_uncached(
        &self,
        lit: Lit,
        conflict: &Conflict,
        cache: &mut std::collections::HashMap<Lit, bool>,
    ) -> bool {
        if self.vars[lit.var()].is_universal(&self.prefix) {
            return false;
        }
        if self.trail.is_decision(lit) {
            return false;
        }
        // assert!(!self.graph[!lit].is_empty()); // doesn't hold if variable is in singleton clause
        for implication in &self.graph[!lit] {
            let reason = implication.reason(&self.allocator);
            trace!("{reason}");

            if !reason.is_implied(!lit, &conflict.assignment) {
                continue;
            }

            for &premise in reason.iter().filter(filter_lit(!lit)) {
                if !self.is_literal_redundant(premise, conflict, cache) {
                    return false;
                }
            }
        }
        true
    }
}
