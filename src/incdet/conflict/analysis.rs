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

    fn clause_max_dec_lvl(&self, dec_lvls: &VarVec<Option<DecLvl>>) -> DecLvl {
        assert_eq!(self.current_level_count, 0);
        self.clause
            .iter()
            .map(|&l| dec_lvls[l.var()].unwrap_or(DecLvl::ROOT))
            .max()
            .unwrap_or(DecLvl::ROOT)
    }
}

impl IncDet {
    pub(crate) fn analyze(&mut self, conflict: &Conflict) -> Result<DecLvl, ()> {
        self.conflict_analysis.reset();
        self.vsids.bump(conflict.var);

        // start with the nucleus (-l, l)
        for implication in &self.graph[conflict.var.negative()] {
            let other = &self.allocator[implication.clause];
            if other.iter().any(|l| conflict.assignment.contains(l)) {
                continue;
            }
            // dbg!(implication);
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
            // dbg!(implication);
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
            let max_lvl = self.conflict_analysis.clause_max_dec_lvl(&self.dec_lvls);
            if max_lvl == DecLvl::ROOT {
                tracing::trace!("Conflict: max-lvl == root level");
                return Err(());
            }
            let backtrack_to = self.conflict_analysis.get_backtrack_level(&self.dec_lvls, max_lvl);
            self.vsids.decay();

            tracing::debug!("Backtrack to level {backtrack_to}");
            return Ok(backtrack_to);
        } else if self.conflict_analysis.current_level_count <= 1 {
            let backtrack_to = self
                .conflict_analysis
                .get_backtrack_level(&self.dec_lvls, self.trail.decision_level());
            self.vsids.decay();
            tracing::debug!("Backtrack to level {backtrack_to}");
            return Ok(backtrack_to);
        }
        for &lit in self.trail.iter().rev() {
            trace!("Rev trail lit: {lit}");
            let lit =
                if self.conflict_analysis.clause.contains(&lit) { lit.negated() } else { lit };
            for implication in &self.graph[lit] {
                let other = &self.allocator[implication.clause];
                trace!("{other}");
                if other
                    .iter()
                    .filter(filter_var(lit.var()))
                    .any(|l| conflict.assignment.contains(l))
                {
                    continue;
                }
                // dbg!(implication);
                self.conflict_analysis.current_level_count -= 1;
                self.conflict_analysis.clause.retain(|l| l.var() != lit.var());
                for l in other.iter().filter(filter_var(lit.var())) {
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
        assert_eq!(self.conflict_analysis.current_level_count, 1);
        let backtrack_to =
            self.conflict_analysis.get_backtrack_level(&self.dec_lvls, self.trail.decision_level());

        self.vsids.decay();

        tracing::debug!("Backtrack to level {backtrack_to}");
        Ok(backtrack_to)
    }
}
