//! The decisions a walk takes where FCS takes them: an expression's relation
//! to the type its context expects ([`Expected`]), taken at the point in
//! FCS's checking order where FCS relates the two, under the binding's
//! faithful prefix ([`Scope::complete`]) and its taint.

use super::*;

/// What an expression's context expects of its type, as FCS knows it at the
/// expression's entry.
///
/// FCS checks an expression against an *overall type*, and relates the two
/// at a point fixed by the expression's form: an application relates its
/// result before its arguments are checked (`Propagate`), a tuple splits an
/// expected tuple before its elements are checked, a branch is checked
/// against the overall type itself, a leaf is related as it is checked. So
/// the expected type is handed down the walk, and each form relates it where
/// FCS does ([`Gen::relate`]), rather than once the expression has been
/// walked: a relation taken late lets the walk decide inside the expression
/// against a table that is not FCS's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Expected {
    /// No expected type: a coercion-free position (a `let`'s right-hand
    /// side, a tuple element in one, an `if`'s first branch in one), whose
    /// node is recorded as synthesized.
    Synth,
    /// The expected type is this variable's, and the relation FCS takes
    /// against it is one inference models: equality first, undone when it
    /// fails ([`Gen::decide`]).
    Known(TyVid),
    /// The expected type is this variable's, related by equality alone
    /// (`MustEqual`: a `let` pattern's type against its right-hand side), so
    /// no coercion can make the node's type another, and the node is recorded
    /// as in a synth position. Decided as [`Self::Known`] is.
    Equal(TyVid),
    /// FCS relates the expression to a type inference does not know: a
    /// method argument (the parameter of the overload FCS resolves), or the
    /// expected type of something inside one. Every relation FCS would take
    /// against it [taints](Gen::taint) what it touches, at the point FCS
    /// takes it.
    Unknown,
}

/// What becomes of a tuple's expected type when its elements' are split from
/// it ([`Gen::tuple_element_expectations`]).
#[derive(Debug)]
pub(super) enum TupleSplit {
    /// Discharged by the split itself: there was nothing to relate, or the
    /// expected variable was decided against a tuple of the elements' types.
    Split(Discharged),
    /// Discharged through the elements: each is checked against its part of
    /// the expected type, so the tuple holds their proofs.
    ByElements,
    /// Related to the tuple once its elements are walked, each against a
    /// fresh type ([`Gen::relate`]).
    AtEnd,
}

/// What a lambda's parameter is checked against, and what the rest of the
/// lambda is, when the lambda is checked against an expected type
/// ([`Gen::function_split`]).
#[derive(Debug, Clone, Copy)]
pub(super) enum FunctionSplit {
    /// The expected type is a function type, or was made one: the parameter
    /// is checked against `domain`, and the rest of the lambda — its next
    /// parameter, or its body — against `rest`, whose type is `result`.
    /// `fresh` says the split made `domain` itself, with no expected type to
    /// relate it to, so that nothing but the parameter binds it.
    Split {
        domain: TyVid,
        result: TyVid,
        rest: Expected,
        fresh: bool,
    },
    /// The expected type is not a function type, nor can be made one: FCS
    /// reports it (`UnifyFunctionType`) and abandons the lambda, checking
    /// nothing inside it.
    NotAFunction,
}

/// What [`Gen::decide`] did with a relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Decision {
    /// Unified, as FCS unifies it.
    Taken,
    /// Not applied, its sides tainted: inference does not know what FCS did.
    Declined,
    /// The equality failed. Between two ground types FCS binds nothing either;
    /// otherwise the prefix has ended.
    Failed,
}

impl Expected {
    /// Whether the position is coercion-free, so that its node is recorded.
    pub(super) fn is_synth(self) -> bool {
        self == Expected::Synth
    }

    /// Whether the node is recorded: no coercion can make its type another.
    pub(super) fn records(self) -> bool {
        matches!(self, Expected::Synth | Expected::Equal(_))
    }

    /// The expected type's variable, where it is known.
    pub(super) fn target(self) -> Option<TyVid> {
        match self {
            Expected::Known(d) | Expected::Equal(d) => Some(d),
            Expected::Synth | Expected::Unknown => None,
        }
    }
}

/// Proof that a form discharged what its context expects of it
/// ([`Expected`]): every form the walk meets must say what became of the
/// relation FCS takes against its expected type, and this is how it says so.
///
/// Its field is private to this module, so outside it the proof is had only
/// from the functions here that discharge an expected type, each one of the
/// ways a form may:
///
/// - **relating** it, where FCS relates it ([`Gen::relate`]);
/// - **tainting** it, where FCS relates it by what inference does not model
///   ([`Gen::taint_expected`]);
/// - **handing it to a child**, whose walk returns the proof
///   ([`Inferred`]), or splitting it among the children
///   ([`Gen::tuple_element_expectations`], [`Discharged::and`]);
/// - **ending the prefix**, after which nothing is decided and nothing
///   generalises ([`Gen::decline_expected`] and its kin).
///
/// So a form that forgets its expected type does not compile, and one that
/// lets a child's proof stand for its own says so where it does. It is a
/// zero-sized type: the proof costs nothing at run time.
#[must_use = "a form's expected type is discharged only when its proof reaches the form's caller"]
#[derive(Debug)]
pub(super) struct Discharged(());

impl Discharged {
    /// Both proofs, as one: a form that discharged its expected type twice
    /// (tainted at its entry and related at its exit), or through each of
    /// its children.
    pub(super) fn and(self, other: Discharged) -> Discharged {
        let Discharged(()) = other;
        self
    }
}

/// What a walk of an expression gives back: the type variable it
/// synthesized, where it did, and the proof that the expected type it was
/// handed is discharged ([`Discharged`]).
#[must_use = "an expression's walk carries the proof that its expected type is discharged"]
#[derive(Debug)]
pub(super) struct Inferred {
    /// The expression's type variable; `None` where it is not modelled,
    /// which has ended the prefix.
    pub(super) var: Option<TyVid>,
    /// The proof.
    pub(super) discharged: Discharged,
}

impl Inferred {
    /// A walk that synthesized `var`.
    pub(super) fn typed(var: TyVid, discharged: Discharged) -> Inferred {
        Inferred {
            var: Some(var),
            discharged,
        }
    }

    /// A walk that synthesized nothing.
    pub(super) fn untyped(discharged: Discharged) -> Inferred {
        Inferred {
            var: None,
            discharged,
        }
    }

    /// The variable alone, the proof dropped: for a walk handed an expected
    /// type of the caller's own making (a domain, a fresh statement type, a
    /// synth position), which the walk itself discharged.
    pub(super) fn var(self) -> Option<TyVid> {
        let Discharged(()) = self.discharged;
        self.var
    }
}

impl<'a> Gen<'a> {
    /// Relate `actual`, the type of an expression, to what its context
    /// expects, at the point FCS relates them: nothing in a synth position;
    /// FCS's equality-first relation against a known expected type
    /// ([`Self::decide`]); and against an unknown one, a relation FCS takes
    /// and inference cannot, so `actual`'s open variables are
    /// [tainted](Self::taint). The decision, where one was taken.
    pub(super) fn relate(
        &mut self,
        scope: &mut Scope,
        actual: TyVid,
        expected: Expected,
    ) -> (Option<Decision>, Discharged) {
        let decision = match expected {
            Expected::Synth => None,
            Expected::Known(d) => Some(self.decide(scope, actual, d)),
            Expected::Equal(d) => Some(self.decide_equal(scope, actual, d)),
            Expected::Unknown => {
                self.taint(scope, self.solver.tys.var(actual));
                None
            }
        };
        (decision, Discharged(()))
    }

    /// Discharge a form's expected type by ending the prefix for `why`
    /// ([`Scope::mark_incomplete`]): the form is not modelled, so no decision
    /// follows it and nothing in the binding generalises. The expected type's
    /// variable is poisoned where the form returns no variable
    /// ([`Self::infer_expr`]).
    pub(super) fn decline_expected(&mut self, scope: &mut Scope, why: Incomplete) -> Discharged {
        scope.mark_incomplete(why);
        Discharged(())
    }

    /// [`Self::decline_expected`] where a sub-walk has recorded why already
    /// ([`Scope::mark_incomplete_propagated`]).
    pub(super) fn decline_expected_propagated(&mut self, scope: &mut Scope) -> Discharged {
        scope.mark_incomplete_propagated();
        Discharged(())
    }

    /// [`Self::decline_expected`] for a reason that may be only the
    /// consequence of the sub-walk begun at `recorded`
    /// ([`Scope::mark_consequence`]).
    pub(super) fn decline_expected_consequence(
        &mut self,
        scope: &mut Scope,
        recorded: usize,
        why: Incomplete,
    ) -> Discharged {
        scope.mark_consequence(recorded, why);
        Discharged(())
    }

    /// FCS's relation between an expression's type `actual` and its expected
    /// type `expected` (`UnifyOverallType`, CheckExpressions.fs): an
    /// equality, undone if it fails, then a conversion that binds nothing
    /// inference models. Subsumption enters only through the flexible
    /// variables of a loosened use ([`Self::loosened`]) and of a union case's
    /// fields, which the types already carry.
    ///
    /// Taken only while the binding's prefix is faithful
    /// ([`Scope::complete`]) — the table is then FCS's, but for its tainted
    /// classes — and only when the relation touches no tainted class and no
    /// variable an earlier binding owns ([`Self::touches_opaque`]): otherwise
    /// it is **declined** ([`Self::decline`]). Taken, it is unified:
    ///
    /// - a success binds what FCS binds, unless it fixes a loosened variable
    ///   that stands for a subtype of a type other than `obj`, a constraint
    ///   nothing checks: then it is undone, and the prefix ends
    ///   ([`Incomplete::BoundedFlex`]);
    /// - a failure between two ground types binds nothing, in FCS too (it
    ///   converts, or reports): the prefix stays;
    /// - a failure with an open variable on either side ends the prefix
    ///   ([`Incomplete::OpenUnifyFailure`]): FCS's error path is not
    ///   atomic, and its conversion may bind.
    pub(super) fn decide(&mut self, scope: &mut Scope, actual: TyVid, expected: TyVid) -> Decision {
        if !scope.complete || self.touches_opaque(scope, actual, expected) {
            self.decline(scope, actual, expected);
            return Decision::Declined;
        }
        let tys = self.solver.tys;
        let snapshot = self.solver.table.snapshot();
        let unified = self.solver.unify_checked(
            self.facts.env,
            tys.var(actual),
            tys.var(expected),
            scope.constraints,
        );
        match unified {
            Ok(()) if self.fixes_bounded_flex(scope) => {
                self.solver.table.rollback_to(snapshot);
                self.decline(scope, actual, expected);
                scope.mark_incomplete(Incomplete::BoundedFlex);
                Decision::Declined
            }
            Ok(()) => {
                self.solver.table.commit(snapshot);
                Decision::Taken
            }
            // FCS solves the constraint inside the same unification and
            // undoes the equality when it fails (`UnifyOverallType`), then
            // reports the error: what it does next is not modelled.
            Err(Refusal::Constraint(gap)) => {
                self.solver.table.commit(snapshot);
                self.decline(scope, actual, expected);
                scope.mark_incomplete(Incomplete::Constraint(gap));
                Decision::Declined
            }
            Err(Refusal::Mismatch | Refusal::Tainted) => {
                self.solver.table.commit(snapshot);
                if !self.is_ground_var(actual) || !self.is_ground_var(expected) {
                    self.decline(scope, actual, expected);
                    scope.mark_incomplete(Incomplete::OpenUnifyFailure);
                }
                Decision::Failed
            }
        }
    }

    /// What each element of a tuple of `arity` elements is checked against,
    /// when the tuple is checked against `expected`, and what becomes of
    /// `expected` itself ([`TupleSplit`]).
    ///
    /// FCS (`TcExprTuple`) splits an expected type that is a tuple or a
    /// variable before it checks the elements, so each element is checked
    /// against its element type: a variable is first equated with a tuple of
    /// fresh element types, a decision like any other. Against any other
    /// expected type it checks the tuple on its own, each element against a
    /// fresh type, and relates the tuple at the end. Under an unknown
    /// expected type every element's is unknown.
    pub(super) fn tuple_element_expectations(
        &mut self,
        scope: &mut Scope,
        expected: Expected,
        arity: usize,
    ) -> (Vec<Expected>, TupleSplit) {
        let (d, wrap): (TyVid, fn(TyVid) -> Expected) = match expected {
            Expected::Synth => return (vec![expected; arity], TupleSplit::Split(Discharged(()))),
            Expected::Unknown => return (vec![expected; arity], TupleSplit::ByElements),
            Expected::Known(d) => (d, Expected::Known),
            Expected::Equal(d) => (d, Expected::Equal),
        };
        let tys = self.solver.tys;
        let resolved = self.solver.table.resolve(tys.var(d));
        match tys.kind(resolved) {
            TyKind::Tuple(elems) if elems.len() == arity => {
                let elems = elems.to_vec();
                // An element type that is a variable is the element's expected
                // type itself, not an alias of it: a `let` pattern's own
                // variable stays a class of its own variables alone, which
                // its equality may still bind once the prefix has ended
                // ([`Self::eq`]).
                let known = elems
                    .into_iter()
                    .map(|e| match *tys.kind(e) {
                        TyKind::Var(v) => wrap(v),
                        _ => wrap(self.fresh_equal(scope, e)),
                    })
                    .collect();
                (known, TupleSplit::ByElements)
            }
            TyKind::Var(_) => {
                let vars: Vec<TyVid> = (0..arity).map(|_| self.solver.table.fresh()).collect();
                let tuple = tys.tuple(vars.iter().map(|&v| tys.var(v)).collect::<Vec<Ty>>());
                let tv = self.fresh_equal(scope, tuple);
                let decision = if matches!(expected, Expected::Equal(_)) {
                    self.decide_equal(scope, tv, d)
                } else {
                    self.decide(scope, tv, d)
                };
                let split = TupleSplit::Split(Discharged(()));
                match decision {
                    Decision::Taken => (vars.into_iter().map(wrap).collect(), split),
                    Decision::Declined | Decision::Failed => {
                        (vec![Expected::Unknown; arity], split)
                    }
                }
            }
            _ => {
                let fresh = (0..arity)
                    .map(|_| Expected::Known(self.solver.table.fresh()))
                    .collect();
                (fresh, TupleSplit::AtEnd)
            }
        }
    }

    /// What a lambda's parameter is checked against, and the rest of the
    /// lambda, when the lambda is checked against `expected`
    /// ([`FunctionSplit`]).
    ///
    /// FCS (`TcIteratedLambdas`) takes the expected type apart before it
    /// checks the parameter (`UnifyFunctionType`, on the expected type
    /// committed as it is: a lambda is never converted): a function type is
    /// split into its domain and result; a variable is first equated with a
    /// function type of fresh parts, a decision like any other; anything else
    /// is an error, after which FCS checks nothing inside the lambda. With no
    /// expected type the parts are fresh and the rest is synthesized. Under
    /// an unknown expected type FCS splits a type inference does not know, so
    /// both parts are [tainted](Self::taint) and the rest is unknown too.
    pub(super) fn function_split(
        &mut self,
        scope: &mut Scope,
        expected: Expected,
    ) -> (FunctionSplit, Discharged) {
        let tys = self.solver.tys;
        let (k, equal) = match expected {
            Expected::Synth => {
                let domain = self.solver.table.fresh();
                let result = self.solver.table.fresh();
                let rest = Expected::Synth;
                let split = FunctionSplit::Split {
                    domain,
                    result,
                    rest,
                    fresh: true,
                };
                return (split, Discharged(()));
            }
            Expected::Unknown => {
                let domain = self.solver.table.fresh();
                let result = self.solver.table.fresh();
                self.taint(scope, tys.var(domain));
                self.taint(scope, tys.var(result));
                let rest = Expected::Unknown;
                let split = FunctionSplit::Split {
                    domain,
                    result,
                    rest,
                    fresh: false,
                };
                return (split, Discharged(()));
            }
            Expected::Known(k) => (k, false),
            Expected::Equal(k) => (k, true),
        };
        let resolved = self.solver.table.resolve(tys.var(k));
        let split = match *tys.kind(resolved) {
            TyKind::Fun { arg, ret } => {
                // A part that is a variable is the part itself, as for a
                // tuple's elements ([`Self::tuple_element_expectations`]).
                let mut part = |t: Ty| match *tys.kind(t) {
                    TyKind::Var(v) => v,
                    _ => self.fresh_equal(scope, t),
                };
                let domain = part(arg);
                let result = part(ret);
                FunctionSplit::Split {
                    domain,
                    result,
                    rest: Expected::Known(result),
                    fresh: false,
                }
            }
            TyKind::Var(_) => {
                let domain = self.solver.table.fresh();
                let result = self.solver.table.fresh();
                let fun = self.fresh_equal(scope, tys.fun(tys.var(domain), tys.var(result)));
                let decision = if equal {
                    self.decide_equal(scope, fun, k)
                } else {
                    self.decide(scope, fun, k)
                };
                match decision {
                    Decision::Taken => FunctionSplit::Split {
                        domain,
                        result,
                        rest: Expected::Known(result),
                        fresh: false,
                    },
                    // Not applied: FCS's parts are what it bound them to,
                    // which a declined decision has tainted.
                    Decision::Declined => FunctionSplit::Split {
                        domain,
                        result,
                        rest: Expected::Unknown,
                        fresh: false,
                    },
                    Decision::Failed => FunctionSplit::NotAFunction,
                }
            }
            TyKind::Named { .. }
            | TyKind::Project { .. }
            | TyKind::Tuple(_)
            | TyKind::Array { .. }
            | TyKind::Param(_) => FunctionSplit::NotAFunction,
        };
        (split, Discharged(()))
    }

    /// [`Self::decide`] for a relation that is an equality alone
    /// ([`Expected::Equal`]): a `let` pattern's against its right-hand side.
    /// Once the prefix has ended nothing is decided here, and nothing is
    /// tainted: the pattern's own equality relates the whole right-hand side
    /// afterwards ([`Self::pattern_rhs`]), binding only the pattern's own
    /// variables ([`Self::eq`]).
    pub(super) fn decide_equal(
        &mut self,
        scope: &mut Scope,
        actual: TyVid,
        expected: TyVid,
    ) -> Decision {
        if scope.complete {
            self.decide(scope, actual, expected)
        } else {
            Decision::Declined
        }
    }

    /// Taint what `expected` holds open, where FCS relates a form's result to
    /// it at the form's entry by a relation inference does not model (a
    /// method's return through its one overload, an operator's result
    /// through its signature): the form's sub-expressions are then walked
    /// against a table that may lack what FCS bound there. A `let` pattern's
    /// type still unbound ([`Expected::Equal`]) needs nothing: it is the
    /// pattern's own fresh variables, which nothing in the right-hand side
    /// can mention, so no check inside can observe what FCS bound them to.
    pub(super) fn taint_expected(&mut self, scope: &mut Scope, expected: Expected) -> Discharged {
        let tys = self.solver.tys;
        match expected {
            Expected::Known(d) => self.taint(scope, tys.var(d)),
            Expected::Equal(d) => {
                let resolved = self.solver.table.resolve(tys.var(d));
                if !matches!(tys.kind(resolved), TyKind::Var(_)) {
                    self.taint(scope, resolved);
                }
            }
            Expected::Synth | Expected::Unknown => {}
        }
        Discharged(())
    }

    /// Decline a relation FCS takes and inference does not: neither side may
    /// generalise, and every open variable of both is
    /// [tainted](Self::taint).
    pub(super) fn decline(&mut self, scope: &mut Scope, a: TyVid, b: TyVid) {
        self.taint(scope, self.solver.tys.var(a));
        self.taint(scope, self.solver.tys.var(b));
    }

    /// Mark every open variable of `ty` as one whose type FCS may know and
    /// inference does not ([`InferTable::taint`]), and poison it, so it does
    /// not generalise. A decision touching one declines
    /// ([`Self::touches_opaque`]), an equality that would bind one is not
    /// applied ([`Self::eq`]), and a use of one is not loosened
    /// ([`Self::value_use`]).
    ///
    /// In a binding that declares type variables, a tainted variable unioned
    /// with one of them may be one FCS fixes, which rejects the declaration
    /// (FS0670): the binding is then [rejected](Scope::rigid_rejected).
    pub(super) fn taint(&mut self, scope: &mut Scope, ty: Ty) {
        let resolved = self.solver.table.resolve(ty);
        let mut roots = HashSet::default();
        collect_var_roots(self.solver.tys, resolved, &mut roots);
        if roots.is_empty() {
            return;
        }
        self.solver.table.taint(ty);
        for &r in &roots {
            scope.poison.push(r);
        }
        if !scope.rigid_typars.is_empty() {
            let rigid = scope.rigid_typars.clone();
            if roots
                .iter()
                .any(|&r| rigid.iter().any(|&t| self.solver.table.unioned(t, r)))
            {
                scope.rigid_rejected = true;
            }
        }
    }

    /// Whether `v` resolves to a type with no variable.
    fn is_ground_var(&mut self, v: TyVid) -> bool {
        let t = self.solver.table.resolve(self.solver.tys.var(v));
        self.solver.tys.is_ground(t)
    }

    /// Whether some loosened variable standing for a subtype of a type other
    /// than `obj` ([`Scope::bounded_flex`]) is bound to a term.
    fn fixes_bounded_flex(&mut self, scope: &Scope) -> bool {
        let tys = self.solver.tys;
        scope.bounded_flex.iter().any(|&v| {
            !matches!(
                tys.kind(self.solver.table.resolve(tys.var(v))),
                TyKind::Var(_)
            )
        })
    }
}
