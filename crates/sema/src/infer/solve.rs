//! The checks a binding's solution is held to at its end ([`Gen::solve`]),
//! and the opacity test its decisions read ([`Gen::touches_opaque`]).

use super::*;

impl<'a> Gen<'a> {
    /// Close the binding's solve at its end. Every equality the binding
    /// generated is already in the table ([`Self::eq`]), and every relation
    /// to an expected type was decided where FCS decides it
    /// ([`Self::decide`]), and every member access at its dot
    /// ([`Self::decide_data_access`]). What is left is the checks the
    /// solution is held to: the declared variables' rigidity, the loosening,
    /// and the constrained instantiations.
    pub(super) fn solve(&mut self, scope: &mut Scope) {
        if !scope.rigid_typars.is_empty() {
            scope.rigid_rejected |= !self.rigid_stays_rigid(scope);
        }
        // The loosening invariant holds of the solution: an annotation can
        // give a use its structure (`let f (g: obj -> 'a) = g`).
        if !self.loosening_holds(scope) {
            scope.poison.extend(scope.bounded_flex.iter().copied());
            if scope.complete {
                scope.mark_incomplete(Incomplete::LoosenedUse);
            }
        }
        self.check_constraints(scope);
    }

    /// Whether the current binding's declared variables ([`Scope::rigid_typars`])
    /// stay distinct and unbound, no equality having failed. FCS tries the
    /// equality first, so a relation that would fix a declared variable is an
    /// error there (FS0670), and one that fails is an error too: in either
    /// case the declaration may be rejected whole.
    fn rigid_stays_rigid(&mut self, scope: &Scope) -> bool {
        if scope.eq_failures > 0 {
            return false;
        }
        let tys = self.solver.tys;
        let mut roots = Vec::new();
        scope.rigid_typars.clone().into_iter().all(|v| {
            match *tys.kind(self.solver.table.resolve(tys.var(v))) {
                TyKind::Var(r) if !roots.contains(&r) => {
                    roots.push(r);
                    true
                }
                _ => false,
            }
        })
    }

    /// Record in the census what the binding just solved did to its
    /// constrained instantiations ([`Scope::constraints`]): their verdict
    /// now.
    ///
    /// The check is over a whole substitution, so the order FCS meets the uses
    /// in cannot matter to it. A violation, or a type not known either way,
    /// marks the binding incomplete — it is not the program FCS accepts, or not
    /// one known to be. A variable left open needs nothing here: it was
    /// poisoned when it was made, so it does not generalise.
    fn check_constraints(&mut self, scope: &mut Scope) {
        match self
            .solver
            .constraint_verdict(self.facts.env, scope.constraints)
        {
            Verdict::Holds | Verdict::Open => {}
            Verdict::Fails => {
                scope.mark_incomplete(Incomplete::Constraint(ConstraintGap::Violated))
            }
            Verdict::Undecided => {
                scope.mark_incomplete(Incomplete::Constraint(ConstraintGap::Undecided))
            }
        }
    }

    /// Whether, in the solution, every bounded loosened variable
    /// ([`Scope::bounded_flex`]) is still unbound: fixed to a type, it is a
    /// subtype constraint nothing checks.
    fn loosening_holds(&mut self, scope: &Scope) -> bool {
        let tys = self.solver.tys;
        scope.bounded_flex.clone().into_iter().all(|v| {
            matches!(
                tys.kind(self.solver.table.resolve(tys.var(v))),
                TyKind::Var(_)
            )
        })
    }

    /// Whether relating `a` to `b` could bind a variable whose type FCS
    /// decides by something inference does not see: one older than this
    /// binding (no union-find class member older than [`Scope::mark`]), whose
    /// type FCS fixed at its own binding, or one [tainted](Self::taint) by a
    /// relation FCS took and inference did not. Grounding an earlier binder's
    /// open variable through a later use would retype it (`g : int -> int`
    /// for `let g = id` under a later `g 1`, where FCS keeps `'a -> 'a`); the
    /// [taint](Self::taint) covers what is not older but still FCS's to fix,
    /// as an earlier binder's open variable given a structure of this
    /// binding's variables by applying it.
    pub(super) fn touches_opaque(&mut self, scope: &Scope, a: TyVid, b: TyVid) -> bool {
        let tys = self.solver.tys;
        if self.solver.table.touches_taint(tys.var(a))
            || self.solver.table.touches_taint(tys.var(b))
        {
            return true;
        }
        let roots = self.solver.relation_roots(a, b);
        roots
            .into_iter()
            .any(|v| self.solver.table.any_older_unioned(v, scope.mark))
    }
}
