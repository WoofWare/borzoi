//! What a file's walk publishes once it is over ([`Gen::finish`]).

use super::*;

/// What a file's walk inferred ([`Gen::finish`]): an [`InferredFile`] but for
/// what the file declares, which its [`FileFacts`] hold
/// ([`FileFacts::into_inferred`]).
pub(super) struct Walked {
    pub(super) types: HashMap<TextRange, Ty>,
    pub(super) def_types: HashMap<DefId, Ty>,
    pub(super) member_resolutions: HashMap<TextRange, Resolution>,
    pub(super) incompleteness: Vec<Vec<Incomplete>>,
    pub(super) receiver_types: HashMap<TextRange, Ty>,
    pub(super) annotated_params: HashSet<DefId>,
    pub(super) module_values: HashMap<DefId, ModuleValue>,
    pub(super) deepest_expr_depth: usize,
    pub(super) type_budget_exceeded: Option<TypeBudgetExceeded>,
    pub(super) type_walks: TypeWalks,
    pub(super) refused_equalities: usize,
}

/// The declaration holding the file's first recovery, when that is a member
/// access whose member is not written (`s.`,
/// [`SyntaxRecovery::first_is_trailing_dot`](crate::SyntaxRecovery::first_is_trailing_dot)):
/// walked by [`Gen::finish`] once everything else is read off, for the
/// receiver types up to that dot alone.
///
/// Keeping the receivers up to the dot is sound only while no receiver
/// there takes its type from context after the dot. None does. A lambda's
/// parameter takes its type from context only as an application's or a
/// pipe's argument ([`Gen::infer_lambda`]), whose domain FCS fixes from the
/// callee and the expected type before it checks the lambda: what follows
/// the lambda reaches it only through a variable the lambda's walk sees
/// open, which records no receiver type. A record field's value and a
/// computation expression's body are not walked, and a method call with a
/// lambda argument is declined before its arguments are walked, which are
/// then walked against an unknown type ([`Gen::infer_method_call`]): the
/// lambda's parameters are tainted, or fixed by their own annotations, which
/// nothing after the dot can change. Those last are where context after the
/// dot decides, since FCS picks a lambda's overload or a record's type from what
/// follows: with `M(f: string -> int)` and `M(f: int -> int, n: int)`,
/// `C.M((fun s -> s.), 1)` gives `s : int` and `C.M(fun s -> s.)` gives
/// `s : string`, and `{ F = (fun s -> s.); G = 1 }` picks a different
/// record from `{ F = (fun s -> s.) }`. Typing those from context inside
/// a damaged declaration needs a recovered-input family graded against
/// FCS's completion sink first (#706).
pub(super) struct Damaged {
    pub(super) decl: LetDecl,
    /// The recovered dot. Everything before it parsed as it would with a
    /// member after it; a receiver after it is past what the parse can be
    /// shown to share with FCS's.
    pub(super) dot: TextRange,
}

impl<'a> Gen<'a> {
    /// Read each recorded expression's and binder's type back from its (now
    /// solved) variable, emitting only fully-[`ground`](TyTable::is_ground) types — an
    /// unsolved variable becomes silence (D5), never a wrong or meaningless
    /// answer.
    ///
    /// Under an **incomplete projection** the member resolutions are sealed
    /// here ([`Resolution::sealed_under_incomplete_projection`]); an
    /// assembly-derived *type* is sealed at its door instead, so by here it has
    /// simply never been unified in — see the seal's comment below.
    ///
    /// A `damaged` declaration is walked only after everything the file
    /// publishes is read off, into emissions of its own, and only its receiver
    /// types up to its recovered dot are kept: nothing it binds, emits or
    /// counts can reach what was read before it.
    pub(super) fn finish(mut self, damaged: Option<Damaged>) -> Walked {
        let emitted = std::mem::replace(&mut self.out, Emissions::new()).into_emitted();
        // Past the budget the table's answers are not answers, so nothing is
        // read from it. The check repeats below, after the last read: the
        // read-off resolves every recorded variable, and one of those can be
        // the first walk to pass the budget.
        if let Some(why) = self.solver.table.over_budget() {
            return Self::finish_over_budget(
                self.facts,
                &self.binders,
                &self.solver,
                emitted.incompleteness,
                emitted.deepest_expr_depth,
                why,
            );
        }
        let Gen {
            facts,
            solver,
            binders,
            ..
        } = &mut self;
        let facts = *facts;
        let tys = solver.tys;
        let mut types = HashMap::default();
        for (range, var) in emitted.exprs {
            let ty = solver.table.resolve(tys.var(var));
            if tys.is_ground(ty) {
                types.insert(range, ty);
            }
        }
        let mut def_types = HashMap::default();
        for (def, var) in binders.vars() {
            // A **parameter** is published below, from what fixes it, never
            // from its binder variable: on an incomplete binding that variable
            // is decoupled from the function type's slot, and can be grounded
            // by a use the binding's unmodelled constraints contradict.
            if binders.is_param(def) || binders.is_withheld(def) {
                continue;
            }
            // A local binder is published only if no emission barrier discarded
            // it (CE-1).
            if emitted.local_defs.contains(&def) && !emitted.published_locals.contains(&def) {
                continue;
            }
            // A **generalised** binder publishes its scheme (its table variable
            // stays open, since `Param`s are never bound into the table). The
            // scheme was computed at the binding's finalisation, in document order.
            if let Some(scheme) = binders.scheme(def) {
                def_types.insert(def, scheme);
                continue;
            }
            // Otherwise a value / function binder is emitted only when ground
            // (3.2b-1 values via their RHS, 3.2c-2b monomorphic functions via
            // `TyKind::Fun`); an open variable stays silent (D5).
            let ty = solver.table.resolve(tys.var(var));
            if tys.is_ground(ty) {
                def_types.insert(def, ty);
            }
        }
        // A parameter's type, where it is known for certain:
        //
        // - its annotation, exact in F# — subsumption applies at a call, never
        //   at the binder — and kept on the binder even where FCS rejects the
        //   body (`let f (c: int) = if c then …` leaves `c : int`);
        // - otherwise its slot in a function type published above, whose
        //   domains are the parameters' types, when the slot is ground. A
        //   slot is the type itself, or an element of a tuple parameter's.
        //
        // A generic parameter is not published: FCS renders a parameter's type
        // renumbered on its own (`'a` for the second of `'a -> 'b -> 'a`),
        // where hover would name it as its function does.
        let mut annotated_params = HashSet::default();
        for def in binders.params() {
            if binders.is_withheld(def) {
                continue;
            }
            if let Some(ann) = binders.param_annotation(def) {
                def_types.insert(def, ann);
                annotated_params.insert(def);
                continue;
            }
            let (Some(owner), Some(slot)) = (binders.param_owner(def), binders.param_slot(def))
            else {
                continue;
            };
            if !def_types.contains_key(&owner) {
                continue;
            }
            let ty = solver.table.resolve(tys.var(slot));
            if tys.is_ground(ty) {
                def_types.insert(def, ty);
            }
        }
        let mut member_resolutions = emitted.member_resolutions;
        // Inference's half of the incomplete-projection seal (the resolver seals
        // its own two maps): a member identified on a referenced-assembly type is
        // an assembly reading like any other, and a DLL the env could not read
        // could declare a type that shadows the receiver's. Swept once over the
        // finished map for the same reason the resolver sweeps — see
        // `Resolver::seal_assembly_readings`.
        //
        // The **types** are sealed too, but not here — by the time a type
        // reaches this map it is a `TyKind::Named` like any other, with nothing to
        // say where it came from. So the type side of the seal is drawn at each
        // door an assembly-supplied type enters through instead. Two of them
        // read the resolver's own map ([`FileFacts::entity_annotation_ty`] for an
        // annotation head, [`Gen::static_callee`] for a static call's rooting
        // type) and so are sealed already, since that map holds no `Entity`
        // under an incomplete projection; [`Gen::wake_member`] is the one that
        // reaches the env directly, and declines there. Every door leaves its
        // variable open, and the ground-only read-off above turns open into
        // silence — while a literal's type, owing the assemblies nothing, is
        // untouched.
        if facts.env.identities_incomplete() {
            for res in member_resolutions.values_mut() {
                *res = res.sealed_under_incomplete_projection();
            }
        }
        let mut receiver_types = HashMap::default();
        for receiver in emitted.receivers {
            record_receiver(solver, &mut receiver_types, receiver);
        }
        // What each module-level binder publishes to later files. A rejected
        // use or an `inline` binding declines whatever its type; otherwise the
        // binder's published type is exactly its hover type above.
        let module_values: Vec<(DefId, ModuleValue)> = binders
            .module_binders()
            .map(|(def, binder)| {
                let verdict = if facts.use_may_be_rejected(def) || binder.header_rejects {
                    ModuleValue::Declined(PrecedingGap::RejectedUse)
                } else if binder.inline {
                    ModuleValue::Declined(PrecedingGap::Inline)
                } else if let Some(&ty) = def_types.get(&def) {
                    ModuleValue::Typed(ty)
                } else if binders.was_walked(def) {
                    ModuleValue::Declined(PrecedingGap::Untyped)
                } else {
                    ModuleValue::Declined(PrecedingGap::NotWalked)
                };
                (def, verdict)
            })
            .collect();
        if let Some(why) = solver.table.over_budget() {
            return Self::finish_over_budget(
                facts,
                binders,
                solver,
                emitted.incompleteness,
                emitted.deepest_expr_depth,
                why,
            );
        }
        // Everything the file publishes is read; the damaged declaration's walk
        // can add receiver types and nothing else.
        if let Some(damaged) = damaged {
            self.damaged_receivers(&damaged, &mut receiver_types);
        }
        let Gen { facts, solver, .. } = self;
        let tys = solver.tys;
        // What the file publishes is the env's: each type is copied out of
        // the session's table, which ends with the inference.
        let mut memo = HashMap::default();
        let types: HashMap<TextRange, Ty> = types
            .into_iter()
            .map(|(range, ty)| (range, facts.publish(tys, ty, &mut memo)))
            .collect();
        let def_types: HashMap<DefId, Ty> = def_types
            .into_iter()
            .map(|(def, ty)| (def, facts.publish(tys, ty, &mut memo)))
            .collect();
        let receiver_types: HashMap<TextRange, Ty> = receiver_types
            .into_iter()
            .map(|(range, ty)| (range, facts.publish(tys, ty, &mut memo)))
            .collect();
        let module_values = module_values
            .into_iter()
            .map(|(def, verdict)| {
                let verdict = match verdict {
                    ModuleValue::Typed(ty) => ModuleValue::Typed(facts.publish(tys, ty, &mut memo)),
                    declined => declined,
                };
                (def, verdict)
            })
            .collect();
        Walked {
            types,
            def_types,
            member_resolutions,
            incompleteness: emitted.incompleteness,
            receiver_types,
            annotated_params,
            module_values,
            deepest_expr_depth: emitted.deepest_expr_depth,
            type_budget_exceeded: None,
            type_walks: solver.table.walks(),
            refused_equalities: solver.refused_equalities,
        }
    }

    /// Walk `damaged` for its receiver types up to its recovered dot, adding
    /// them to `receiver_types`. The walk writes to emissions of its own, of
    /// which only those receivers are read. A walk that passes the type
    /// budget adds none. The cut at the dot assumes no receiver before it is
    /// typed from context after it ([`Damaged`]).
    fn damaged_receivers(
        &mut self,
        damaged: &Damaged,
        receiver_types: &mut HashMap<TextRange, Ty>,
    ) {
        self.type_let_decl(&damaged.decl);
        let emitted = std::mem::replace(&mut self.out, Emissions::new()).into_emitted();
        if self.solver.table.over_budget().is_some() {
            return;
        }
        for receiver in emitted.receivers {
            if receiver.dot.start() <= damaged.dot.start() {
                record_receiver(&mut self.solver, receiver_types, receiver);
            }
        }
    }

    /// [`Self::finish`] for a file whose inference reached the type budget
    /// ([`InferredFile::type_budget_exceeded`]): nothing the table answered
    /// is read, since past the budget its answers are not answers
    /// ([`InferTable`]), and before it they may lean on a type it never
    /// finished. What the file declares is kept.
    fn finish_over_budget(
        facts: &FileFacts<'_>,
        binders: &BinderEnv,
        solver: &Solver<'_>,
        incompleteness: Vec<Vec<Incomplete>>,
        deepest_expr_depth: usize,
        why: TypeBudgetExceeded,
    ) -> Walked {
        let module_values = binders
            .module_binders()
            .map(|(def, binder)| {
                let verdict = if facts.use_may_be_rejected(def) || binder.header_rejects {
                    PrecedingGap::RejectedUse
                } else if binder.inline {
                    PrecedingGap::Inline
                } else {
                    PrecedingGap::TypeBudget
                };
                (def, ModuleValue::Declined(verdict))
            })
            .collect();
        Walked {
            types: HashMap::default(),
            def_types: HashMap::default(),
            member_resolutions: HashMap::default(),
            incompleteness,
            receiver_types: HashMap::default(),
            annotated_params: HashSet::default(),
            module_values,
            deepest_expr_depth,
            type_budget_exceeded: Some(why),
            type_walks: solver.table.walks(),
            refused_equalities: solver.refused_equalities,
        }
    }
}

/// Add `receiver` to `receiver_types`. Its type was ground at the access, so
/// the final table has it too; the assertion is the invariant that makes a
/// type read at the access the one FCS has there.
fn record_receiver(
    solver: &mut Solver<'_>,
    receiver_types: &mut HashMap<TextRange, Ty>,
    receiver: Receiver,
) {
    // Past the budget the table's answers are not answers, and the caller
    // publishes nothing.
    debug_assert!(
        solver.table.over_budget().is_some()
            || solver.table.resolve(solver.tys.var(receiver.var)) == receiver.ty,
        "a receiver's type at its access is its final one"
    );
    let previous = receiver_types.insert(receiver.dot, receiver.ty);
    debug_assert!(
        previous.is_none_or(|p| p == receiver.ty),
        "one dot, one receiver type"
    );
}
