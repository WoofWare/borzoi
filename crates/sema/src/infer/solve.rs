//! The solve of a binding's suspended member accesses, where each is
//! generated ([`Gen::settle_access`]) and at the binding's end
//! ([`Gen::solve`]): the worklist, and the checks a solve is held to.

use super::*;

/// A pending member access inside [`Gen::solve`] — the suspended form of
/// [`Constraint::HasMember`], threaded through the solver's fixpoint.
#[derive(Debug, Clone)]
pub(super) struct SuspendedMember {
    recv: TyVid,
    pub(super) name: String,
    pub(super) result: TyVid,
    pub(super) use_range: TextRange,
    pub(super) kind: MemberAccessKind,
}

impl<'a> Gen<'a> {
    /// Close the binding's solve at its end. Every equality the binding
    /// generated is already in the table ([`Self::eq`]), and every relation
    /// to an expected type was decided where FCS decides it
    /// ([`Self::decide`]); what is left is the member accesses still
    /// suspended, which a settle wakes to a fixpoint ([`Self::settle`]) and
    /// which, never woken, are dropped. Then the checks the solution is held
    /// to: the declared variables' rigidity, the loosening, and the
    /// constrained instantiations.
    pub(super) fn solve(&mut self, scope: &mut Scope) {
        // Members that never woke are dropped.
        self.run_worklist(scope);
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

    /// Settle the constraints generated **so far** in the current binding,
    /// mid-walk (CE-1): wake members to a fixpoint, then put every suspension
    /// still pending back on the constraint list. Used to ask whether a local
    /// binder or a statement is ground *at that point in the walk*.
    ///
    /// A member wake reads nothing but its receiver's type (and a method's
    /// argument types), so waking it early is what the final solve would do
    /// anyway.
    pub(super) fn settle(&mut self, scope: &mut Scope) {
        for m in self.run_worklist(scope) {
            self.solver.constraints.push(Constraint::HasMember {
                recv: m.recv,
                name: m.name,
                result: m.result,
                use_range: m.use_range,
                kind: m.kind,
            });
        }
    }

    /// Settle at a member access, where FCS decides it: wake what can wake,
    /// and **decline** every access still suspended — its receiver is not
    /// known at the access (a variable, a generic receiver, an overload whose
    /// arguments are not known), which FCS rejects or decides by what
    /// inference does not see. A declined access records nothing, its result
    /// is [tainted](Self::taint), and the binding's prefix ends
    /// ([`Incomplete::UndecidedAccess`]); it never wakes later, since a later
    /// wake is one FCS did not make at the access.
    ///
    /// Every access settles where it is generated, so what is still suspended
    /// after the settle is this access's.
    pub(super) fn settle_access(&mut self, scope: &mut Scope) {
        self.settle(scope);
        let mut declined = false;
        for c in std::mem::take(&mut self.solver.constraints) {
            let Constraint::HasMember { result, .. } = c;
            self.taint(scope, self.solver.tys.var(result));
            declined = true;
        }
        if declined {
            scope.mark_incomplete(Incomplete::UndecidedAccess);
        }
    }

    /// The worklist behind [`Self::solve`] and [`Self::settle`]: wake every
    /// pending member access to a fixpoint, and return those that never woke.
    fn run_worklist(&mut self, scope: &mut Scope) -> Vec<SuspendedMember> {
        let mut suspended: Vec<SuspendedMember> = std::mem::take(&mut self.solver.constraints)
            .into_iter()
            .map(|c| {
                let Constraint::HasMember {
                    recv,
                    name,
                    result,
                    use_range,
                    kind,
                } = c;
                SuspendedMember {
                    recv,
                    name,
                    result,
                    use_range,
                    kind,
                }
            })
            .collect();

        // Fixpoint: scan the parked members; wake each whose receiver is now
        // concrete; a wake unifies at once, which may make a later member's
        // receiver concrete (a chained member `s.A.B`). Repeat while anything
        // fires. Each suspension fires at most once (a woken one is not
        // re-parked), so the loop runs at most `suspended.len()` times.
        loop {
            let mut still_pending: Vec<SuspendedMember> = Vec::new();
            let mut woke = false;
            for m in std::mem::take(&mut suspended) {
                let head = self.solver.table.resolve(self.solver.tys.var(m.recv));
                match self.solver.tys.kind(head) {
                    // Unresolved receiver — keep it parked for a later wake.
                    TyKind::Var(_) => still_pending.push(m),
                    // A concrete named receiver — attempt the member lookup (a data
                    // member or a method, per `m.kind`), which may unify
                    // `result` with the member's type and record the resolved member's
                    // identity at `use_range` (Stage 3.3b). A retry request (an
                    // overload whose argument is not yet ground) re-parks without
                    // counting as progress, so a later wake that grounds the
                    // argument re-triggers this one. Termination holds — a retry
                    // sets no `woke`, and the number of progress passes is bounded
                    // by the (finite) suspension count.
                    // `wake_member` looks the head up at arity 0, so a GENERIC
                    // receiver must not reach it: with both `N.C` and `N.C<'T>`
                    // in the env it would resolve the nullary one and commit a
                    // member of a type the receiver is not. Making the lookup
                    // arity-aware is what lets these wake; until then they stay
                    // parked.
                    TyKind::Named { args, .. } if !args.is_empty() => {
                        still_pending.push(m);
                    }
                    TyKind::Named { path, .. } => {
                        let path = path.spelled(self.facts.env.names());
                        match self.wake_member(
                            scope,
                            &path,
                            &m.name,
                            m.result,
                            m.use_range,
                            &m.kind,
                        ) {
                            Wake::Retry => still_pending.push(m),
                            wake => {
                                woke = true;
                                // A result the wake did not bind (a `void`
                                // return, a type the bridge does not carry) is
                                // one FCS knows; an access no member answers
                                // is declined.
                                if !self.solver.tys.is_ground(
                                    self.solver.table.resolve(self.solver.tys.var(m.result)),
                                ) {
                                    self.taint(scope, self.solver.tys.var(m.result));
                                }
                                if wake == Wake::Declined {
                                    scope.mark_incomplete(Incomplete::UndecidedAccess);
                                }
                            }
                        }
                    }
                    // A field of a project record, read off its declaration.
                    TyKind::Project { .. } if self.wake_record_field(scope, head, &m) => {
                        woke = true;
                    }
                    // Any other concrete head (array / tuple / function / a
                    // quantified param) has no assembly entity to look a member up
                    // on: the access is declined where FCS decides it, so its
                    // result is tainted and the prefix ends. Arrays' `.Length` is
                    // an intrinsic, out of scope.
                    TyKind::Array { .. }
                    | TyKind::Tuple(_)
                    | TyKind::Fun { .. }
                    | TyKind::Param(_) => {
                        woke = true;
                        self.taint(scope, self.solver.tys.var(m.result));
                        scope.mark_incomplete(Incomplete::UndecidedAccess);
                    }
                    // Any other member of a project type is not modelled: drop
                    // the constraint, leaving the access's (poisoned) result
                    // open and tainted, and say so in the census.
                    TyKind::Project { .. } => {
                        woke = true;
                        self.taint(scope, self.solver.tys.var(m.result));
                        scope.mark_incomplete(Incomplete::ProjectTypeMember);
                    }
                }
            }
            suspended = still_pending;
            debug_assert!(
                self.solver.constraints.is_empty(),
                "a wake suspends nothing"
            );
            // Nothing fired this pass ⇒ no receiver can become more concrete ⇒
            // fixpoint.
            if !woke {
                break;
            }
        }
        suspended
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
