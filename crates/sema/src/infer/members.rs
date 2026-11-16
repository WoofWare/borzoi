//! Member accesses and method calls: what the walk generates for them, the
//! wakes that resolve a data member, and the regime a method call's
//! arguments are checked under.

use super::*;
use crate::FcsRange as _;

/// What a data member's lookup ([`Gen::wake_member`]) made of the access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Wake {
    /// The member was identified and its resolution recorded; its result is
    /// bound to the member's type where that type is read. `stands` says
    /// whether what the receiver emitted stands ([`Gen::record_member`]).
    Resolved { stands: bool },
    /// No member is identified: the access is declined, for the reason it
    /// carries.
    Declined(Incomplete),
}

/// A method call's argument list, read before anything in it is walked: FCS
/// chooses the regime the arguments are checked under from the call's shape
/// before it checks any of them ([`Gen::call_regime`]).
pub(super) struct CallArgs {
    /// The positional arguments, in order. `M()` has none; `M(())` has one.
    elements: Vec<Expr>,
    /// Whether the call is the direct unit call `M()`, which FCS passes to
    /// a single method of one parameter as that argument.
    unit: bool,
    /// Why the list is not a plain positional one, if it is not: a recovery
    /// hole ([`Incomplete::Recovery`]), or a named argument or a malformed
    /// list ([`Incomplete::MethodArgShape`]).
    not_positional: Option<Incomplete>,
}

impl CallArgs {
    /// Read the argument list of a call `recv.M ARG`. Only the call's own
    /// parentheses are peeled: `M((a, b))` is one argument, a tuple, which FCS
    /// elaborates as a method-value application.
    pub(super) fn of(arg: &Expr) -> CallArgs {
        let positional = |elements| CallArgs {
            elements,
            unit: false,
            not_positional: None,
        };
        if is_unit_literal(arg) {
            return CallArgs {
                elements: Vec::new(),
                unit: true,
                not_positional: None,
            };
        }
        let inner = match arg {
            Expr::Paren(p) => match p.inner() {
                Some(inner) => inner,
                None => {
                    return CallArgs {
                        elements: Vec::new(),
                        unit: false,
                        not_positional: Some(Incomplete::Recovery),
                    };
                }
            },
            other => other.clone(),
        };
        if is_unit_literal(&inner) {
            return positional(vec![inner]);
        }
        match &inner {
            Expr::Tuple(t) if !t.is_struct() => {
                let elements: Vec<Expr> = t.elements().collect();
                // A well-formed positional tuple has one more element than
                // commas; a trailing or doubled comma is a recovery FCS types
                // as `obj`.
                let commas = t
                    .syntax()
                    .children_with_tokens()
                    .filter(|c| c.kind() == SyntaxKind::COMMA_TOK)
                    .count();
                let malformed = elements.iter().any(is_named_arg) || elements.len() != commas + 1;
                CallArgs {
                    elements,
                    unit: false,
                    not_positional: malformed.then_some(Incomplete::MethodArgShape),
                }
            }
            _ => CallArgs {
                not_positional: is_named_arg(&inner).then_some(Incomplete::MethodArgShape),
                elements: vec![inner],
                unit: false,
            },
        }
    }
}

/// The regime FCS checks a method call's arguments under, chosen from the
/// call's shape before any argument is checked (`TcMethodApplication`).
pub(super) enum CallRegime<'e> {
    /// Exactly one candidate of the group has the call's shape, and it is one
    /// inference reads ([`Gen::unique_candidate`]): FCS relates its parameters
    /// to the arguments' types and its return to the call's expected type
    /// before it checks any argument (`UnifyUniqueOverloading`).
    Unique {
        decl: EntityHandle,
        idx: MemberIndex,
        method: &'e MethodLike,
        /// The candidate's form ([`call_forms`]): its trailing
        /// `[<ParamArray>]` parameter takes the surplus arguments when
        /// [`CallForm::Expanded`], each related to its element type.
        form: CallForm,
    },
    /// Several candidates have it: FCS checks each argument against a fresh
    /// type, and resolves the call once they are checked.
    Several(Vec<(EntityHandle, MemberIndex, &'e MethodLike)>),
    /// The call is not one inference decides, for this reason: the receiver is
    /// not known at the dot, no member of the name is identified, the group
    /// is not provably FCS's, no candidate has the call's shape, or the call
    /// is of a shape inference does not read (a named argument, a shaped
    /// argument such as a lambda).
    Otherwise(Incomplete),
}

impl<'a> Gen<'a> {
    /// Decide a **data-member** access chain over a receiver variable `recv`,
    /// segment by segment, each where FCS decides it: at its dot, on what the
    /// receiver's type is there ([`Self::decide_data_access`]). The `segments`
    /// are the member idents after the receiver (`["Length"]` for `s.Length`;
    /// `["A", "B"]` for `s.A.B`), segment *i*'s receiver the result of segment
    /// *i − 1*. Returns the variable standing for each member's type, in order
    /// — the last is the type of the whole access, and each is the receiver of
    /// the segment after it — and whether what the receiver emitted stands:
    /// only where every segment resolves to a member FCS reads as a member get
    /// (FCS drops the receiver of `s.Length.Foo`, `Foo` rejected).
    ///
    /// A segment whose label the resolver answers through FCS's record-label
    /// table ([`Self::decide_receiver_by_label`]) has its receiver decided
    /// first, after the segments before it.
    ///
    /// Every receiver and result variable is poisoned: an undecided access must
    /// never let either generalise (the same rule as application's
    /// `r`-poison); a ground one is unaffected.
    fn gen_member_access(
        &mut self,
        scope: &mut Scope,
        recv: TyVid,
        segments: &[SyntaxToken],
    ) -> (Vec<TyVid>, bool) {
        let mut results: Vec<TyVid> = Vec::with_capacity(segments.len());
        let mut stands = true;
        let mut cur = recv;
        // The segments before `decided` have been decided.
        let mut decided = 0;
        for seg in segments {
            if let Some(field) = self.facts.resolved.field_label_under(
                seg.fcs_range(),
                self.facts.env,
                &self.facts.ext_scope,
            ) {
                // FCS resolved the segments before this one at their dots: one
                // it did not resolve there is declined, which ends the prefix,
                // so the receiver is not mistaken for one FCS knows nothing
                // about.
                stands &= self.decide_data_segments(scope, recv, segments, &results, decided);
                decided = results.len();
                self.decide_receiver_by_label(scope, cur, field);
            }
            let result = self.solver.table.fresh();
            scope.poison.push(cur);
            scope.poison.push(result);
            results.push(result);
            cur = result;
        }
        stands &= self.decide_data_segments(scope, recv, segments, &results, decided);
        (results, stands)
    }

    /// Decide the segments of the chain `recv.segments` from `from` up to
    /// `results.len()` ([`Self::decide_data_access`]), segment *i*'s type
    /// `results[i]` and its receiver `results[i − 1]` (`recv` for the first).
    /// Returns whether what the receiver emitted still stands.
    fn decide_data_segments(
        &mut self,
        scope: &mut Scope,
        recv: TyVid,
        segments: &[SyntaxToken],
        results: &[TyVid],
        from: usize,
    ) -> bool {
        let mut stands = true;
        for i in from..results.len() {
            let cur = if i == 0 { recv } else { results[i - 1] };
            stands &= self.decide_data_access(scope, cur, &segments[i], results[i]);
        }
        stands
    }

    /// Decide the data-member access `recv.member`, whose type is `result`, at
    /// its dot, on what `recv`'s type is there:
    ///
    /// - a non-generic named type: its field or property ([`Self::wake_member`]);
    /// - a record the project declares: its field ([`Self::wake_record_field`]);
    /// - a variable ([`Incomplete::IndeterminateReceiver`]: FCS reports FS0072, or
    ///   looks the name up on `obj`), a generic type ([`Incomplete::GenericReceiver`]:
    ///   the lookup is by name at arity 0), any other member of a project type
    ///   ([`Incomplete::ProjectTypeMember`]), or an array, tuple, function or
    ///   type parameter ([`Incomplete::ReceiverShape`]): declined.
    ///
    /// A declined access records nothing, its result is [tainted](Self::taint),
    /// and the binding's prefix ends. Returns whether what the receiver emitted
    /// stands ([`Self::record_member`]).
    fn decide_data_access(
        &mut self,
        scope: &mut Scope,
        recv: TyVid,
        member: &SyntaxToken,
        result: TyVid,
    ) -> bool {
        let tys = self.solver.tys;
        let head = self.solver.table.resolve(tys.var(recv));
        let name = ident_text(member);
        let use_range = member.fcs_range();
        let declined = match tys.kind(head) {
            TyKind::Named { args, .. } if !args.is_empty() => Incomplete::GenericReceiver,
            TyKind::Named { path, .. } => {
                let path = path.spelled(self.facts.env.names());
                let wake = self.wake_member(scope, &path, &name, result, use_range);
                // A result the wake did not bind (a type the bridge does not
                // carry) is one FCS knows.
                if !tys.is_ground(self.solver.table.resolve(tys.var(result))) {
                    self.taint(scope, tys.var(result));
                }
                match wake {
                    Wake::Resolved { stands } => return stands,
                    Wake::Declined(why) => {
                        scope.mark_incomplete(why);
                        return false;
                    }
                }
            }
            // A field of a project record, read off its declaration; FCS reads
            // it as a field get, which keeps no node at the receiver.
            TyKind::Project { .. }
                if self.wake_record_field(scope, head, &name, result, use_range) =>
            {
                return false;
            }
            TyKind::Project { .. } => Incomplete::ProjectTypeMember,
            TyKind::Var(_) => Incomplete::IndeterminateReceiver,
            TyKind::Array { .. } | TyKind::Tuple(_) | TyKind::Fun { .. } | TyKind::Param(_) => {
                Incomplete::ReceiverShape
            }
        };
        self.taint(scope, tys.var(result));
        scope.mark_incomplete(declined);
        false
    }

    /// Decide the receiver `recv` of the label `label` by FCS's record-label
    /// table, where the receiver's type is not known at the access: FCS's
    /// member lookup on a type variable finds nothing, so it resolves the
    /// label to the table's latest record and fixes the receiver to that
    /// record, freshly instantiated (`ResolveExprDotLongIdent`,
    /// `FreshenRecdFieldRef`). The resolver answers which record
    /// ([`ResolvedFile::field_label_under`]); binding the receiver to it is a
    /// decision ([`Self::decide`]), taken only on a faithful prefix and an
    /// untainted receiver. The access then wakes on the record like any
    /// other ([`Self::wake_record_field`]). The caller asks the resolver
    /// ([`Self::gen_member_access`]).
    ///
    /// Nothing is done where the receiver is known (FCS looks the label up in
    /// that type), or where the record has no path inference names it by: the
    /// access is then decided on the receiver as it stands.
    fn decide_receiver_by_label(
        &mut self,
        scope: &mut Scope,
        recv: TyVid,
        field: crate::FieldLabel,
    ) {
        let tys = self.solver.tys;
        if !matches!(
            tys.kind(self.solver.table.resolve(tys.var(recv))),
            TyKind::Var(_)
        ) {
            return;
        }
        let Some((path, arity)) = self.facts.project_types.get(&field.record).cloned() else {
            return;
        };
        if arity != field.arity {
            return;
        }
        let args: Vec<Ty> = (0..arity)
            .map(|_| tys.var(self.solver.table.fresh()))
            .collect();
        let record = self.fresh_equal(scope, tys.project(path, args));
        self.decide(scope, record, recv);
    }

    /// Type a **method call** `recv.Method(args)` or `Type.Method(args)`,
    /// returning the call's type variable — the chosen member's return type.
    /// The whole-call node is emitted by [`Self::infer_app`]'s callers at the
    /// `APP_EXPR` range, read back only when ground.
    ///
    /// FCS takes a method call in this order (`TcMethodApplication`), and so
    /// does the walk:
    ///
    /// 1. the receiver, and any data member before the method (`s.Field.M(…)`),
    ///    decided at its dot;
    /// 2. the method group, looked up on the receiver's type at the dot;
    /// 3. the regime the arguments are checked under ([`CallRegime`]), from
    ///    how many candidates of the group have the call's shape, before any
    ///    argument is checked;
    /// 4. the arguments, in source order, under that regime;
    /// 5. the resolution.
    ///
    /// **A method call emits no node inside itself** — not its receiver, not its
    /// argument's sub-expressions. FCS keeps nothing inside a call it rejects,
    /// and inference does not know whether FCS accepted the call, so every
    /// emission the receiver and the arguments make is discarded (#795): the
    /// receiver's *type* still flows to the lookup, only its node is dropped.
    ///
    /// A **static** call `Type.Method(args)` (stage OV-7) — a callee whose
    /// second-to-last segment the resolver resolved to a referenced-assembly
    /// *type* entity ([`Self::static_callee`]) — takes the same path through the
    /// static group, its receiver unified with the entity's [`TyKind::Named`]
    /// at once; no receiver node is emitted (FCS emits none on the qualified
    /// path).
    ///
    /// A callee that is neither a modelled member access nor an entity-rooted
    /// static path — a module's function, a project type, an unresolved head —
    /// is declined before anything is walked.
    pub(super) fn infer_method_call(
        &mut self,
        scope: &mut Scope,
        callee: &Expr,
        arg: &Expr,
        expected: Expected,
    ) -> Inferred {
        // Snapshot the emissions: everything the receiver and the argument
        // walks record inside the call is discarded below (see the doc).
        let emit_mark = self.out.mark();
        let (recv, method_tok, is_static) =
            if let Some((path, method_tok)) = self.static_callee(callee) {
                // The static receiver's type is the rooting entity itself, ground
                // at generation time.
                let recv = self.fresh_equal(
                    scope,
                    self.solver.tys.named_path(self.facts.env.names(), &path),
                );
                (recv, method_tok, true)
            } else {
                let recorded = scope.reasons_recorded();
                let Some((receivers, method_tok, path)) = self.method_callee(scope, callee) else {
                    self.out.discard_since(emit_mark);
                    return Inferred::untyped(self.decline_expected_consequence(
                        scope,
                        recorded,
                        Incomplete::MethodCallee(callee.syntax().kind()),
                    ));
                };
                // The data-member prefix of the callee (`s.Field.M(…)`) is
                // decided at its dots, before the arguments.
                let recv = *receivers.last().expect("a method call has a receiver");
                self.record_receivers(AccessPath {
                    path: &path,
                    receivers,
                });
                (recv, method_tok, false)
            };
        let args = CallArgs::of(arg);
        let result = self.solver.table.fresh();
        // An undecided call must not let its receiver or result generalise;
        // a ground one is unaffected.
        scope.poison.push(recv);
        scope.poison.push(result);
        let discharged = match self.call_regime(recv, &method_tok, is_static, &args) {
            CallRegime::Unique {
                decl,
                idx,
                method,
                form,
            } => self.unique_call(
                scope,
                (decl, idx, method, form),
                method_tok.fcs_range(),
                &args,
                result,
                expected,
            ),
            CallRegime::Several(group) => self.several_call(
                scope,
                &group,
                method_tok.fcs_range(),
                &args,
                result,
                expected,
            ),
            CallRegime::Otherwise(why) => self.undecided_call(scope, why, &args, result, expected),
        };
        self.out.discard_since(emit_mark);
        // Under an equality (a `let` pattern's type) FCS checks the call
        // against that type itself — `TcMethodApplicationThen` passes the
        // overall type down when nothing follows the call — and its node has
        // that type even where the call fails to resolve or to fit it.
        let var = match expected {
            Expected::Equal(d) => d,
            _ => result,
        };
        Inferred::typed(var, discharged)
    }

    /// The regime FCS checks a call's arguments under ([`CallRegime`]),
    /// read from the receiver's type at the dot, the method group of the
    /// name on it, and the argument list's shape — before any argument is
    /// walked. Anything inference cannot be certain of is
    /// [`CallRegime::Otherwise`].
    fn call_regime(
        &mut self,
        recv: TyVid,
        method: &SyntaxToken,
        is_static: bool,
        args: &CallArgs,
    ) -> CallRegime<'a> {
        if let Some(why) = args.not_positional {
            return CallRegime::Otherwise(why);
        }
        // FCS gives a lambda, a `function`, a `_.X`, an `&x` or a quotation
        // argument a type of its syntax's shape before it relates the one
        // candidate's parameters (`GetNewInferenceTypeForMethodArg`), and
        // stops relating at the first that fails: which of the candidate's
        // relations it took is not modelled.
        if args.elements.iter().any(is_shaped_argument) {
            return CallRegime::Otherwise(Incomplete::OverloadUnresolved);
        }
        let tys = self.solver.tys;
        let head = self.solver.table.resolve(tys.var(recv));
        let path = match tys.kind(head) {
            // FCS looks the method up on the receiver at the dot: on a
            // variable it reports FS0072, or looks it up on `obj`.
            TyKind::Var(_) => return CallRegime::Otherwise(Incomplete::IndeterminateReceiver),
            // The lookup is by name at arity 0, which cannot tell a generic
            // receiver from a non-generic type of the same name.
            TyKind::Named { args, .. } if !args.is_empty() => {
                return CallRegime::Otherwise(Incomplete::GenericReceiver);
            }
            TyKind::Named { path, .. } => path.spelled(self.facts.env.names()),
            TyKind::Project { .. } => {
                return CallRegime::Otherwise(Incomplete::ProjectTypeMember);
            }
            TyKind::Array { .. } | TyKind::Tuple(_) | TyKind::Fun { .. } | TyKind::Param(_) => {
                return CallRegime::Otherwise(Incomplete::ReceiverShape);
            }
        };
        let env = self.facts.env;
        let name = ident_text(method);
        let Some((type_name, namespace)) = path.split_last() else {
            return CallRegime::Otherwise(Incomplete::NoSuchMember);
        };
        // This is the one place inference itself names an assembly type — a
        // literal's receiver type (`"hi".Length`) is a path this phase writes
        // down, vetted by nothing — so it reads through the drop-marker pairing
        // ([`AssemblyEnv::lookup_type_if_certain`]): a dropped same-FQN sibling
        // would leave the survivor's members read where FCS binds the dropped
        // type's.
        let Some(handle) = env.lookup_type_if_certain(namespace, type_name, 0) else {
            return CallRegime::Otherwise(Incomplete::NoSuchMember);
        };
        // An in-scope extension member of the name would join FCS's method
        // group and could win (§4.1(4)), for a static call too: an F#
        // augmentation `type T with static member …` joins a type-qualified
        // static group the same way.
        if !self
            .facts
            .ext_scope
            .absent(env.extension_view(), &name, is_static)
        {
            return CallRegime::Otherwise(Incomplete::ExtensionInScope);
        }
        // The provably complete intrinsic group, instance or static per the
        // call's shape: an instance and a static member of one name never
        // share a candidate set (`HasCorrectObjArgs`).
        let group = if is_static {
            env.static_method_group(handle, &name)
        } else {
            env.instance_method_group(handle, &name)
        };
        let Some(group) = group else {
            return CallRegime::Otherwise(Incomplete::NoSuchMember);
        };
        // An F# member with several argument groups (`member x.M a b`) compiles
        // to a parameter list a tupled member's is indistinguishable from, and
        // FCS takes a curried member as a first-class use (FS0816 beside an
        // overload): a group holding a possibly curried member is not read
        // (`docs/completed/ov-6.1-curry-detection-plan.md`).
        if group
            .iter()
            .any(|(_, _, m)| m.signature.parameters.len() >= 2 && m.arg_group_count != Some(1))
        {
            return CallRegime::Otherwise(Incomplete::OverloadUnresolved);
        }
        let n = args.elements.len();
        // The candidates FCS forms of the group at `n` arguments (`IsCandidate`),
        // a `[<ParamArray>]` method being two at exactly its declared count.
        let forms: usize = group.iter().map(|(_, _, m)| call_forms(m, n).len()).sum();
        match forms {
            0 => {
                // `M()` on a group of one method of one plain parameter: FCS
                // passes the unit as that argument (the "single named item"
                // rule), and commits that method whatever it takes.
                if args.unit
                    && let [(decl, idx, m)] = group.as_slice()
                    && let [only] = m.signature.parameters.as_slice()
                    && !only.is_param_array
                    && !only.is_out
                    && matches!(only.default, ParamDefault::None)
                    && self.unique_candidate(m, 0, CallForm::Normal)
                {
                    return CallRegime::Unique {
                        decl: *decl,
                        idx: *idx,
                        method: m,
                        form: CallForm::Normal,
                    };
                }
                // FCS reports a call no candidate has the shape of
                // (FS0501, FS0505).
                CallRegime::Otherwise(Incomplete::OverloadUnresolved)
            }
            1 => {
                let (decl, idx, m) = *group
                    .iter()
                    .find(|(_, _, m)| !call_forms(m, n).is_empty())
                    .expect("one candidate has the call's shape");
                match call_forms(m, n).as_slice() {
                    &[form] if self.unique_candidate(m, n, form) => CallRegime::Unique {
                        decl,
                        idx,
                        method: m,
                        form,
                    },
                    _ => CallRegime::Otherwise(Incomplete::OverloadUnresolved),
                }
            }
            // The resolution reads each candidate's parameter types, and an
            // IL parameter type whose unit of measure was erased admits an
            // argument FCS rejects (`O(float<m>)` reads as `O(float64)`).
            _ if group
                .iter()
                .all(|(level, _, _)| env.member_types_keep_their_measures(*level)) =>
            {
                CallRegime::Several(group)
            }
            _ => CallRegime::Otherwise(Incomplete::OverloadUnresolved),
        }
    }

    /// Whether the one candidate of a call of `n` arguments, in `form`, is
    /// one whose relations to the call inference reads: not generic, not a
    /// constructor, and no `byref`, `out`, `[<ParamArray>]` or F# optional
    /// (`?x`, of an option type the argument is not) parameter among those
    /// the arguments are supplied to, and no `out` parameter among those
    /// omitted, which FCS folds into the return. A .NET optional parameter
    /// supplied an argument takes it as a required one does. In its expanded
    /// form the trailing `[<ParamArray>]` parameter takes the arguments past
    /// the others, and nothing is omitted.
    fn unique_candidate(&self, m: &MethodLike, n: usize, form: CallForm) -> bool {
        let params = &m.signature.parameters;
        let plain = |p: &&borzoi_assembly::Parameter| {
            !p.is_byref
                && !p.is_out
                && !p.is_param_array
                && matches!(p.default, ParamDefault::None | ParamDefault::Optional(_))
        };
        m.generic_parameters.is_empty()
            && !m.is_constructor
            && match form {
                CallForm::Normal => {
                    params.iter().take(n).all(|p| plain(&p))
                        && params.iter().skip(n).all(|p| !p.is_out)
                }
                CallForm::Expanded => params
                    .split_last()
                    .is_some_and(|(_, rest)| rest.iter().all(|p| plain(&p))),
            }
    }

    /// The parameter type the `i`-th argument of a call to `method` in `form`
    /// is related to: its own parameter's, or, past the others in the expanded
    /// form, the element type of the trailing `[<ParamArray>]` vector.
    fn argument_parameter(method: &MethodLike, form: CallForm, i: usize) -> Option<&TypeRef> {
        let params = &method.signature.parameters;
        match form {
            CallForm::Normal => params.get(i).map(|p| &p.ty),
            CallForm::Expanded => {
                let (array, rest) = params.split_last()?;
                if i < rest.len() {
                    return Some(&rest[i].ty);
                }
                match &array.ty {
                    TypeRef::Array { element, .. } => Some(&element.ty),
                    _ => None,
                }
            }
        }
    }

    /// A call with exactly one candidate (`UnifyUniqueOverloading`): FCS
    /// relates each of its parameters to its argument's type, then its return
    /// to the call's expected type, then checks each argument against its
    /// parameter. A parameter `obj` takes any argument, a sealed one is the
    /// argument's type, and any other is a type the argument's is a subtype of
    /// ([`Self::flexible`]). A parameter or return whose type inference does
    /// not read ([`Self::readable_member_type`]) is not related: its argument
    /// is checked against an unknown type, and the call's expected type is
    /// tainted where FCS relates the return. The member is committed whatever
    /// the arguments are, as FCS commits it.
    fn unique_call(
        &mut self,
        scope: &mut Scope,
        (decl, idx, method, form): (EntityHandle, MemberIndex, &'a MethodLike, CallForm),
        use_range: TextRange,
        args: &CallArgs,
        result: TyVid,
        expected: Expected,
    ) -> Discharged {
        let _ = self.record_member(decl, idx, use_range);
        let params: Vec<Option<TyVid>> = (0..args.elements.len())
            .map(|i| {
                let declared = Self::argument_parameter(method, form, i)?;
                let ty = self.readable_member_type(decl, declared)?;
                let flexible = self.flexible(scope, ty);
                Some(self.fresh_equal(scope, flexible))
            })
            .collect();
        let entry = match self.readable_member_type(decl, &method.signature.return_type) {
            Some(ret) => {
                self.eq(scope, self.solver.tys.var(result), ret, Own::var(result));
                self.relate(scope, result, expected).1
            }
            None => {
                self.taint(scope, self.solver.tys.var(result));
                self.taint_expected(scope, expected)
            }
        };
        for (el, param) in args.elements.iter().zip(params) {
            let expected = param.map_or(Expected::Unknown, Expected::Known);
            let _ = self.walk_method_arg(scope, el, expected);
        }
        entry
    }

    /// A call with several candidates: FCS checks each argument against a
    /// fresh type, then resolves the call on the arguments' types. Those
    /// inference resolves on only when every one is ground: FCS solves what
    /// it can of open ones first (`CanonicalizePartialInferenceProblem`) and
    /// may resolve on what is left open, fixing it (`s.Equals(p)` picks
    /// `Equals(string)`), so a call with an open argument is declined
    /// ([`Incomplete::OverloadUnresolved`]). The chosen member's return is then
    /// related to the call's expected type.
    fn several_call(
        &mut self,
        scope: &mut Scope,
        group: &[(EntityHandle, MemberIndex, &'a MethodLike)],
        use_range: TextRange,
        args: &CallArgs,
        result: TyVid,
        expected: Expected,
    ) -> Discharged {
        let vars: Vec<Option<TyVid>> = args
            .elements
            .iter()
            .map(|el| {
                let fresh = self.solver.table.fresh();
                self.walk_method_arg(scope, el, Expected::Known(fresh))
            })
            .collect();
        let tys = self.solver.tys;
        let mut arg_tys = Vec::with_capacity(vars.len());
        for v in vars {
            let Some(v) = v else { break };
            let ty = self.solver.table.resolve(tys.var(v));
            if !tys.is_ground(ty) {
                break;
            }
            arg_tys.push(ty);
        }
        let chosen = (arg_tys.len() == args.elements.len())
            .then(|| self.facts.env.resolve_overload(group, tys, &arg_tys))
            .flatten();
        match chosen {
            Some((decl, idx, m)) => {
                let _ = self.record_member(decl, idx, use_range);
                match self.readable_member_type(decl, &m.signature.return_type) {
                    Some(ret) => {
                        self.eq(scope, tys.var(result), ret, Own::var(result));
                    }
                    None => self.taint(scope, tys.var(result)),
                }
            }
            None => {
                self.taint(scope, tys.var(result));
                scope.mark_incomplete(Incomplete::OverloadUnresolved);
            }
        }
        self.relate(scope, result, expected).1
    }

    /// A call inference does not decide, for `why`. The prefix ends before
    /// the arguments are walked: FCS reports a member it does not find, or a
    /// receiver it does not know, before it checks any argument, so what an
    /// argument would decide is not what FCS has. The arguments are walked
    /// against an unknown type, the call's expected type tainted where FCS
    /// would relate the return, and the result tainted.
    fn undecided_call(
        &mut self,
        scope: &mut Scope,
        why: Incomplete,
        args: &CallArgs,
        result: TyVid,
        expected: Expected,
    ) -> Discharged {
        scope.mark_incomplete(why);
        let entry = self.taint_expected(scope, expected);
        for el in &args.elements {
            let _ = self.walk_method_arg(scope, el, Expected::Unknown);
        }
        self.taint(scope, self.solver.tys.var(result));
        let (_, exit) = self.relate(scope, result, expected);
        entry.and(exit)
    }

    /// Walk one method argument against `expected`, returning its type
    /// variable, or `None` where it is not modelled (which has ended the
    /// prefix).
    fn walk_method_arg(
        &mut self,
        scope: &mut Scope,
        el: &Expr,
        expected: Expected,
    ) -> Option<TyVid> {
        let var = self.infer_expr(scope, el, expected).var();
        if var.is_none() {
            scope.mark_incomplete_propagated();
        }
        var
    }

    /// Recognise a **static-call callee** `Type.Method` (stage OV-7): a
    /// `LONG_IDENT_EXPR` whose **second-to-last** segment carries the resolver's
    /// [`Resolution::Entity`] — the rooting referenced-assembly type — with the
    /// final segment as the method name. Returns the entity's canonical
    /// [`TyKind::Named`] path and the method token, or `None` when the callee is not
    /// that shape:
    ///
    /// - the rooting segment resolved to anything else — an in-file value/type, a
    ///   static *member* result (`System.Console.Out.WriteLine` — the segment
    ///   before the method carries no `Entity` record), or nothing;
    /// - the entity is a **module** — a module function is an F# *value*
    ///   (curried, possibly generic, applied with value semantics), not a .NET
    ///   method call, so the overload engine's commit rules do not transfer;
    /// - the entity does not **round-trip** through
    ///   [`AssemblyEnv::lookup_type`]`(namespace, name, 0)` — a nested or generic
    ///   type, whose wake-side lookup would miss or land elsewhere. The check
    ///   makes the generation-side handle and the wake-side lookup provably
    ///   agree, rather than assuming the path encoding.
    ///
    /// A **parenthesised** callee (`(System.String.Compare)(…)`) is deliberately
    /// *not* peeled (unlike [`Self::method_callee`]): FCS elaborates it as a
    /// first-class **method value**, whose semantics differ from a call —
    /// probed 2026-07-11 (review round 4): the overloaded
    /// `(String.Compare)("a", "b")` is `obj` (the method-group conversion
    /// fails) where the call form commits `Int32`, so peeling into the call
    /// engine would publish a type at a node FCS types `obj`.
    ///
    /// An active-pattern segment declines as in [`Self::method_callee`].
    fn static_callee(&self, callee: &Expr) -> Option<(Vec<String>, SyntaxToken)> {
        let Expr::LongIdent(li) = callee else {
            return None;
        };
        let long_ident = li.long_ident()?;
        if long_ident.active_pat_names().next().is_some() {
            return None;
        }
        let idents: Vec<SyntaxToken> = long_ident.idents().collect();
        let (method, prefix) = idents.split_last()?;
        let root = prefix.last()?;
        let Resolution::Entity(handle) = self.facts.resolved.resolution_at(root.fcs_range())?
        else {
            return None;
        };
        if self.facts.env.is_module(handle) {
            return None;
        }
        let entity = self.facts.env.entity(handle);
        if self
            .facts
            .env
            .lookup_type(&entity.namespace, &entity.name, 0)
            != Some(handle)
        {
            return None;
        }
        let mut path = entity.namespace.clone();
        path.push(entity.name.clone());
        Some((path, method.clone()))
    }

    /// Resolve a **method-call callee** (a member access in function position) into
    /// the variables of its receivers, the method-name token and the path they are
    /// in (Stage 3.3d), or `None` when the callee is not a modelled member access.
    /// The receivers are one per dot of the path ([`AccessPath`]): the head, then
    /// each member of a **data-member prefix** before the final method segment
    /// (`s.Field.M(…)` = a `Data` `HasMember` on `Field`, then a `Method` one on
    /// `M`), so the last is the method's own receiver. Emits the receiver's own
    /// node and chains the prefix with [`Self::gen_member_access`]:
    ///
    /// - **`LONG_IDENT_EXPR`** (`s.M`, `s.Field.M`): the head resolves to an in-file
    ///   value binder ([`Self::receiver_var`], emitting its value node); the trailing
    ///   idents split into a data-member prefix and the final method. A head that is
    ///   not an in-file value binder (a static path `System.Console.WriteLine`)
    ///   returns `None` **before** any emission, so the call defers cleanly.
    /// - **`DOT_GET_EXPR`** (`"hi".M`, `(expr).M`): the inner receiver *expression*
    ///   is synthesized (its own node emitted), then the member path splits the same
    ///   way. This also handles a method result feeding a further call
    ///   (`s.ToLower().M()`) — the inner `APP_EXPR` receiver grounds through the
    ///   fixpoint.
    /// - **`PAREN_EXPR`**: transparent — peel and recurse.
    ///
    /// An active-pattern name segment (`Foo.(|Bar|_|)`) is not a plain member token,
    /// so a path carrying one declines. So does a path whose last member is not
    /// written (a recovered trailing dot, `y.(0, p)`), which names no method:
    /// it is walked as the access it is, for its receivers
    /// ([`Self::infer_long_ident_member`], [`Self::infer_dot_get`]).
    fn method_callee(
        &mut self,
        scope: &mut Scope,
        callee: &Expr,
    ) -> Option<(Vec<TyVid>, SyntaxToken, LongIdent)> {
        match callee {
            Expr::LongIdent(li) => {
                let long_ident = li.long_ident()?;
                if has_trailing_dot(&long_ident) {
                    let _ = self.infer_expr(scope, callee, Expected::Synth).var();
                    return None;
                }
                if long_ident.active_pat_names().next().is_some() {
                    return None;
                }
                let idents: Vec<SyntaxToken> = long_ident.idents().collect();
                let (head, rest) = idents.split_first()?;
                // Need a head *and* at least one member segment (the method).
                let (method, prefix) = rest.split_last()?;
                let head_var = self.receiver_var(scope, head)?;
                // Emit the receiver's own value node (coercion-free — synth).
                self.emit(head.fcs_range(), head_var, Expected::Synth);
                let mut receivers = vec![head_var];
                receivers.extend(self.gen_member_access(scope, head_var, prefix).0);
                Some((receivers, method.clone(), long_ident))
            }
            Expr::DotGet(dg) => {
                let recv_expr = dg.expr()?;
                let long_ident = dg.long_ident()?;
                if has_trailing_dot(&long_ident) {
                    let _ = self.infer_expr(scope, callee, Expected::Synth).var();
                    return None;
                }
                if long_ident.active_pat_names().next().is_some() {
                    return None;
                }
                let segments: Vec<SyntaxToken> = long_ident.idents().collect();
                let (method, prefix) = segments.split_last()?;
                // The receiver is a coercion-free (synth) sub-position — a member
                // access never coerces its receiver — so synthesize it (emitting its
                // own node).
                let head_var = self.infer_expr(scope, &recv_expr, Expected::Synth).var()?;
                let mut receivers = vec![head_var];
                receivers.extend(self.gen_member_access(scope, head_var, prefix).0);
                Some((receivers, method.clone(), long_ident))
            }
            Expr::Paren(p) => self.method_callee(scope, &p.inner()?),
            _ => None,
        }
    }

    /// Type a **value-receiver** member access `s.Length` — a `LONG_IDENT_EXPR`
    /// whose head resolves to an in-file value binder, with trailing member
    /// segments (Stage 3.3a). Returns the whole access's type variable (the final
    /// member's), or `None` (deferred, incomplete) when the shape is one this stage
    /// does not model:
    ///
    /// - a **bare** long-ident (a single segment, no members) — that is a plain
    ///   value/type reference the resolver already handles, not a member access;
    /// - a head that does **not** resolve to an in-file value binder — a
    ///   fully-qualified static path (`System.Console.WriteLine`) or an unresolved
    ///   name, left for the catch-all so the static-member resolution is untouched;
    /// - an active-pattern segment in the path (`Foo.(|Bar|_|)`), which
    ///   [`LongIdent::idents`](borzoi_cst::syntax::LongIdent::idents) does not surface as a plain token.
    ///
    /// The receiver's own value node is emitted at the head token's range (FCS
    /// emits a value node there), coercion-free (synth) — a member access never
    /// coerces its receiver. The whole-access node is emitted at the
    /// `LONG_IDENT_EXPR` range in the access's own mode (`expected`).
    pub(super) fn infer_long_ident_member(
        &mut self,
        scope: &mut Scope,
        li: &LongIdentExpr,
        expected: Expected,
    ) -> Inferred {
        let Some(long_ident) = li.long_ident() else {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        };
        // A module-qualified value (`List.length`), whose node FCS keys at
        // the whole path.
        if let Some(whole) = self.module_value_path(li) {
            let Some(uv) = self.nonlocal_value_or_incomplete(scope, whole, Use::Value) else {
                return Inferred::untyped(self.decline_expected_propagated(scope));
            };
            if !self.facts.case_of_fields_at(whole) {
                self.emit(whole, uv, expected);
            }
            let (_, d) = self.relate(scope, uv, expected);
            return Inferred::typed(uv, d);
        }
        // An active-pattern name segment cannot be projected as a plain member
        // token, so a path carrying one is unmodelled here.
        if long_ident.active_pat_names().next().is_some() {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::MemberAccessShape));
        }
        let idents: Vec<SyntaxToken> = long_ident.idents().collect();
        // A path whose last member is not written (`s.`, `s.A.`) is a recovered
        // access, walked only in a damaged declaration, for its receivers.
        let trailing = has_trailing_dot(&long_ident);
        // Need a head *and* at least one member segment, or a dot after it.
        let (head, segments) = match idents.split_first() {
            Some((head, segments)) if !segments.is_empty() || trailing => (head, segments),
            _ => {
                return Inferred::untyped(
                    self.decline_expected(scope, Incomplete::MemberAccessShape),
                );
            }
        };
        // The head must resolve to a value binder, in this file or a preceding
        // one; otherwise this is a qualified static path (or unresolved) we do
        // not model here.
        let recorded = scope.reasons_recorded();
        let Some(recv) = self.receiver_var(scope, head) else {
            return Inferred::untyped(self.decline_expected_consequence(
                scope,
                recorded,
                Incomplete::QualifiedPath,
            ));
        };
        if trailing {
            // FCS looks up each written member in turn, and nothing after the
            // last dot: what precedes each dot is still a receiver it knew or
            // did not.
            let mut receivers = vec![recv];
            receivers.extend(self.gen_member_access(scope, recv, segments).0);
            self.record_receivers(AccessPath {
                path: &long_ident,
                receivers,
            });
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        }
        // Emit the receiver's own value node (coercion-free — synth), which
        // stands only where the access resolves: FCS keeps no receiver node for
        // a rejected one.
        let mark = self.out.mark();
        self.emit(head.fcs_range(), recv, Expected::Synth);
        let (results, stands) = self.gen_member_access(scope, recv, segments);
        if !stands {
            self.out.discard_since(mark);
        }
        let (&result, before_last) = results
            .split_last()
            .expect("a member access names a member");
        let mut receivers = vec![recv];
        receivers.extend(before_last);
        self.record_receivers(AccessPath {
            path: &long_ident,
            receivers,
        });
        self.emit(self.facts.node_span(li.syntax()), result, expected);
        // FCS relates a member access to what its context expects once the
        // access is resolved (`Propagate` stops at a dot).
        let (_, d) = self.relate(scope, result, expected);
        Inferred::typed(result, d)
    }

    /// Type a `(expr).Member` member access — a `DOT_GET_EXPR` (Stage 3.3a). The
    /// inner receiver *expression* is synthesized (its own node emitted where FCS
    /// has one — e.g. the `"hi"` literal in `"hi".Length`), and the member path
    /// chains from its variable. Returns the whole access's type, or `None` when
    /// the receiver does not synthesize or the member path is empty/unprojectable.
    pub(super) fn infer_dot_get(
        &mut self,
        scope: &mut Scope,
        dg: &DotGetExpr,
        expected: Expected,
    ) -> Inferred {
        let Some(recv_expr) = dg.expr() else {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        };
        let Some(long_ident) = dg.long_ident() else {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        };
        if long_ident.active_pat_names().next().is_some() {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::MemberAccessShape));
        }
        let segments: Vec<SyntaxToken> = long_ident.idents().collect();
        // A path whose last member is not written (`(e).`) is a recovered
        // access, walked only in a damaged declaration, for its receivers.
        let trailing = has_trailing_dot(&long_ident);
        if segments.is_empty() && !trailing {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        }
        // The receiver is a coercion-free (synth) sub-position — a member access
        // never coerces its receiver — so synthesize it, emitting its own node,
        // which stands only where every segment resolves: FCS keeps nothing
        // inside the receiver of a rejected one.
        let mark = self.out.mark();
        let recv = self.infer_expr(scope, &recv_expr, Expected::Synth).var();
        let Some(recv) = recv else {
            // The receiver's walk recorded why it is not typed.
            if !segments.is_empty() {
                self.out.discard_since(mark);
            }
            return Inferred::untyped(self.decline_expected_propagated(scope));
        };
        let (results, stands) = self.gen_member_access(scope, recv, &segments);
        if !stands {
            self.out.discard_since(mark);
        }
        let mut receivers = vec![recv];
        receivers.extend(&results);
        if !trailing {
            // The last member's type is the access's, not a receiver.
            receivers.pop();
        }
        self.record_receivers(AccessPath {
            path: &long_ident,
            receivers,
        });
        let Some(&result) = results.last().filter(|_| !trailing) else {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        };
        self.emit(self.facts.node_span(dg.syntax()), result, expected);
        let (_, d) = self.relate(scope, result, expected);
        Inferred::typed(result, d)
    }

    /// The inference variable for a member-access **receiver** whose head token
    /// resolves to an in-file value binder — mirroring [`Self::infer_callee`]'s
    /// ident resolution but for a receiver: a generalised binder instantiates its
    /// scheme afresh; a plain in-file binder contributes its variable (poisoned if
    /// it is an *environment* reference, so a still-open receiver blocks
    /// generalisation). A head the resolver resolved to a **preceding file's**
    /// top-level value takes the type that file published, instantiated as a
    /// scheme's is; one it published no type for records why. `None` if the
    /// head does not resolve to such a value either (a qualified static path,
    /// an assembly name, or unresolved) — the caller then defers, leaving any
    /// static-member resolution untouched.
    fn receiver_var(&mut self, scope: &mut Scope, head: &SyntaxToken) -> Option<TyVid> {
        let Some(def) = self.facts.def_at(head.fcs_range()) else {
            let Some(Resolution::Item(id)) = self.facts.resolved.resolution_at(head.fcs_range())
            else {
                return None;
            };
            if self.facts.resolved.owns_item(id) {
                return None;
            }
            let ty = match self.facts.preceding.get(id) {
                Ok(&ty) => ty,
                Err(gap) => {
                    scope.mark_incomplete(Incomplete::PrecedingValue(gap));
                    return None;
                }
            };
            let body = self.solver.instantiate(self.facts.env.types(), ty);
            return Some(self.fresh_equal(scope, body));
        };
        if self.binders.is_withheld(def) {
            scope.mark_incomplete(Incomplete::RigidTypeVariable);
            return None;
        }
        if let Some(scheme) = self.binders.scheme(def) {
            let body = self.solver.instantiate(self.solver.tys, scheme);
            return Some(self.fresh_equal(scope, body));
        }
        let dv = self.def_var(def);
        if !scope.is_param(def) {
            scope.poison.push(dv);
            self.taint(scope, self.solver.tys.var(dv));
        }
        Some(dv)
    }

    /// Decide the data-member access `name`, whose type is `result`, on the
    /// project type `head`, where `head` is a record the project declares
    /// with a field of that name that inference reads, accessible at the
    /// access: relate the access's result to the field's type, the record's
    /// parameters instantiated at `head`'s arguments. `false` for anything
    /// else (a member that is not a field, a record not read).
    ///
    /// FCS looks a field up by the receiver's type when it knows that type
    /// at the access. When it does not, it resolves the label through the
    /// record-label table and fixes the receiver to that record, which
    /// [`Self::decide_receiver_by_label`] decides before the access is
    /// generated, so the access then wakes here too.
    pub(super) fn wake_record_field(
        &mut self,
        scope: &mut Scope,
        head: Ty,
        name: &str,
        result: TyVid,
        use_range: TextRange,
    ) -> bool {
        let TyKind::Project { path, args } = self.solver.tys.kind(head) else {
            return false;
        };
        let record = self
            .facts
            .project_records
            .get(&(path.clone(), args.len()))
            .or_else(|| self.facts.preceding.record(path, args.len()));
        let Some(record) =
            record.filter(|r| r.scope.is_none_or(|scope| scope.contains_range(use_range)))
        else {
            return false;
        };
        let Some(&field) = record.fields.get(name) else {
            return false;
        };
        let declared = record.record;
        let env_tys = self.facts.env.types();
        let mut fresh: HashMap<u32, TyVid> = HashMap::default();
        let from = self.solver.table.mark();
        let receiver = self.solver.instantiate_rec(env_tys, declared, &mut fresh);
        let field = self.solver.instantiate_rec(env_tys, field, &mut fresh);
        // The record's instance is this wake's own; so is the access's
        // result, which the access made and settles at once.
        let own = self.own_since(from);
        self.eq(scope, receiver, head, own);
        self.eq(scope, self.solver.tys.var(result), field, Own::var(result));
        true
    }

    /// Decide a data-member access on a named type: look up the field or non-indexer
    /// property `name` on the receiver type `path`
    /// ([`AssemblyEnv::instance_data_member`], walking its base chain), record
    /// its identity at `use_range` ([`Self::record_member`]) and bind `result`
    /// to its type where inference reads it ([`Self::readable_member_type`]).
    /// Declined, recording nothing, when no member is identified.
    pub(super) fn wake_member(
        &mut self,
        scope: &mut Scope,
        path: &[String],
        name: &str,
        result: TyVid,
        use_range: TextRange,
    ) -> Wake {
        let env = self.facts.env;
        let Some((type_name, namespace)) = path.split_last() else {
            return Wake::Declined(Incomplete::NoSuchMember);
        };
        // The receiver's type is a path inference may have written itself (a
        // literal's), so it is read through the drop-marker pairing, as a
        // method call's is ([`Self::call_regime`]).
        let Some(handle) = env.lookup_type_if_certain(namespace, type_name, 0) else {
            return Wake::Declined(Incomplete::NoSuchMember);
        };
        let Some((decl, idx, member_ty)) = env.instance_data_member(handle, name) else {
            return Wake::Declined(Incomplete::NoSuchMember);
        };
        let stands = self.record_member(decl, idx, use_range);
        if let Some(ty) = self.readable_member_type(decl, member_ty) {
            self.eq(scope, self.solver.tys.var(result), ty, Own::var(result));
        }
        Wake::Resolved { stands }
    }

    /// Record that the member name at `use_range` resolves to the member
    /// `idx` of `decl` — the entity that *declares* it, a base type for an
    /// inherited one — in the resolver's own shape, for the LSP's hover and
    /// go-to-definition. Recorded even where the member's type is not read: its
    /// identity is known.
    ///
    /// Returns whether what the access's receiver emitted stands: the access
    /// is one FCS accepts, unless the receiver's nodes turn on an assembly
    /// reading the seal withholds (an incomplete projection publishes only
    /// what an empty env would), or the member is a field of an F# record,
    /// union or exception type, which FCS reads as a field get, under which
    /// the typed tree keeps no node at the receiver (`let f (v: R) = v.Q` has
    /// one at `v.Q` only).
    fn record_member(
        &mut self,
        decl: EntityHandle,
        idx: MemberIndex,
        use_range: TextRange,
    ) -> bool {
        let env = self.facts.env;
        self.out
            .member_resolution(use_range, Resolution::Member { parent: decl, idx });
        let fsharp_field_carrier = matches!(
            env.entity(decl).kind,
            EntityKind::Record | EntityKind::Union | EntityKind::Exception
        );
        !fsharp_field_carrier && !env.identities_incomplete()
    }

    /// A member's type `ty`, declared by `decl`, as inference reads it: F#'s
    /// `unit` for `void`, else its bridged type ([`type_ref_to_ty`]); `None`
    /// where the bridge does not carry it, where the declaring entity's pickle
    /// says a unit of measure was erased (IL reads `float<m>` as `float64`),
    /// or under an incomplete projection.
    ///
    /// **The seal, drawn at the door** (see [`Self::finish`]): under an
    /// incomplete projection an unread DLL could declare a colliding receiver
    /// type whose member of this name has another type, so this one is not
    /// provably the member's — and once it is unified into a variable nothing
    /// downstream can tell it apart from a type owing the assemblies nothing.
    fn readable_member_type(&self, decl: EntityHandle, ty: &TypeRef) -> Option<Ty> {
        let env = self.facts.env;
        if env.identities_incomplete() {
            return None;
        }
        if matches!(ty, TypeRef::Primitive(Primitive::Void)) {
            return Some(self.solver.tys.named(env.names(), UNIT));
        }
        let bridged = type_ref_to_ty(env.names(), self.solver.tys, ty)?;
        env.member_types_keep_their_measures(decl)
            .then_some(bridged)
    }
}

/// Whether a method argument is one FCS gives a type of its syntax's shape
/// before it relates the call's one candidate to the arguments
/// (`GetNewInferenceTypeForMethodArg`): a lambda (`fun …`), a `function`, a
/// `_.X`, an address-of (`&x`) or a quotation, under any parentheses. Relating
/// a candidate's non-function parameter to a lambda's function type fails,
/// and FCS relates the candidate's remaining parameters and its return only
/// up to that failure, so which of them it related is not modelled.
fn is_shaped_argument(el: &Expr) -> bool {
    matches!(
        unparenthesize(el.clone()),
        Some(
            Expr::Fun(_)
                | Expr::MatchLambda(_)
                | Expr::DotLambda(_)
                | Expr::AddressOf(_)
                | Expr::Quote(_)
        )
    )
}

/// Whether an argument element is a **named argument** `name = value` (Stage 3.3d).
/// F# parses it as `App[ InfixApp[name, "="], value ]` — an outer (non-infix)
/// application whose function is the infix `=` operator applied to the name. A
/// *positional* infix argument (`a + b`, itself an infix `App`) is **not** a named
/// argument (the outer `is_infix()` guard), and neither is a nested `=` inside a
/// record / lambda (which is not the element's own top-level operator). The wake
/// cannot validate the name against the method's parameters, so any named argument
/// defers the whole call (conservative — even correct names defer, but never wrong).
pub(super) fn is_named_arg(el: &Expr) -> bool {
    let Expr::App(outer) = el else {
        return false;
    };
    // A positional infix element (`a + b`) is the infix `App` itself, not an outer
    // application *of* an infix — so exclude it here.
    if outer.is_infix() {
        return false;
    }
    let Some(Expr::App(op_app)) = outer.func() else {
        return false;
    };
    op_app.is_infix()
        && op_app
            .func()
            .is_some_and(|op| op.syntax().text().to_string().trim() == "=")
}
