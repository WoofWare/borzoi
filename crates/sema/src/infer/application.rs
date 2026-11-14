//! Applications: a callee, its arguments, and infix operators.

use super::*;

/// What an application spine applies: an expression in function position, or
/// the operator of an infix application.
enum SpineHead {
    Callee(Expr),
    Operator(Expr),
}

impl<'a> Gen<'a> {
    /// Type a **modelled** (non-infix) function application `f x`, returning its
    /// **result** variable `r`. It generates the application's constraints but
    /// records **no** node — the caller decides emission, since whether the node
    /// is emitted depends on position: a top-level application in a synth
    /// position emits `r`, but an application in the **function position** of
    /// an outer application does not (FCS collapses a curried spine into one
    /// typed node at the whole application — confirmed by probing the `types`
    /// oracle).
    ///
    /// The application is checked in FCS's order (`TcExprThen`, `Propagate`):
    /// the curried spine `f a1 … an` is collected — through applications and
    /// an infix operator, not through parentheses, which FCS checks as an
    /// expression of their own — and its head synthesized ([`Self::infer_callee`],
    /// no node). Then, before any argument is checked, its type is split into
    /// `d1 -> … -> dn -> r` by genuine equalities (applying a value forces a
    /// function shape), and `r` is related to what the application's context
    /// expects ([`Self::relate`]); only then is each argument checked against
    /// its domain, left to right ([`Self::infer_arg`]). So an argument that is
    /// itself an application, `g (singleton y)`, has its result related to
    /// `g`'s domain before `y` is checked.
    ///
    /// Application does **not** mark the binding incomplete: the construct is
    /// modelled. An argument that fails to walk does, in its own arm.
    pub(super) fn infer_app(
        &mut self,
        scope: &mut Scope,
        app: &AppExpr,
        expected: Expected,
    ) -> Option<TyVid> {
        let Some(func) = app.func() else {
            scope.mark_incomplete(Incomplete::Recovery);
            return None;
        };
        let Some(arg) = app.arg() else {
            scope.mark_incomplete(Incomplete::Recovery);
            return None;
        };
        // Asked first: a prefix operator (`-a`) is a bare `LONG_IDENT_EXPR`
        // callee, which is otherwise read as a member access. The built-in
        // application relates its own result.
        if let Some(r) = self.builtin_application(scope, &func, &arg, expected) {
            return r;
        }
        // A **method call** `recv.Method(args)` is an application whose callee
        // is a member access. A module-qualified function (`List.map f`,
        // `(List.map) f`) is a value, applied with value semantics, not a
        // method call.
        if self.is_method_call(&func) {
            return self.infer_method_call(scope, &func, &arg, expected);
        }
        let mut args = vec![arg];
        let mut head = func;
        let head = loop {
            match head {
                Expr::App(ref inner) if inner.is_infix() => {
                    let (Some(op), Some(lhs)) = (inner.func(), inner.arg()) else {
                        scope.mark_incomplete(Incomplete::Recovery);
                        return None;
                    };
                    args.push(lhs);
                    break SpineHead::Operator(op);
                }
                Expr::App(ref inner) if self.continues_spine(inner) => {
                    let (Some(f), Some(a)) = (inner.func(), inner.arg()) else {
                        scope.mark_incomplete(Incomplete::Recovery);
                        return None;
                    };
                    args.push(a);
                    head = f;
                }
                _ => break SpineHead::Callee(head),
            }
        };
        args.reverse();
        // A union case applied to its one argument relates its result by an
        // equality FCS does not recover from (`UnifyOverallType` in
        // `TcUnionCaseOrExnCaseOrActivePatternResultItemThen`): when it fails,
        // the fields are never checked. A parenthesized case is an expression
        // applied as any other is.
        let case = matches!(&head, SpineHead::Callee(c) if args.len() == 1 && self.names_case(c));
        let tf = match head {
            SpineHead::Operator(op) => self.operator_value(scope, &op)?,
            SpineHead::Callee(callee) => self.infer_callee(scope, &callee)?,
        };
        Some(self.apply(scope, tf, &args, expected, case))
    }

    /// Whether the callee `e` is a bare union case, by name or by qualified
    /// path.
    fn names_case(&self, e: &Expr) -> bool {
        let at = match e {
            Expr::Ident(ident) => ident.ident().map(|t| t.text_range()),
            Expr::LongIdent(li) => self.module_value_path(li),
            _ => None,
        };
        at.is_some_and(|at| self.is_case_at(at))
    }

    /// Whether the application `inner`, in the function position of another,
    /// is a link of the same curried spine — a plain value application, as
    /// opposed to a bracket indexer, a method call or a built-in operator's
    /// application, which are checked as expressions of their own.
    fn continues_spine(&self, inner: &AppExpr) -> bool {
        if inner.is_infix() || inner.is_bracket_indexer() {
            return false;
        }
        let (Some(func), Some(arg)) = (inner.func(), inner.arg()) else {
            return false;
        };
        !self.is_method_call(&func) && !self.is_builtin_application(&func, &arg)
    }

    /// Whether an application whose function position is `func` is a method
    /// call: a member access that is not a module-qualified value.
    fn is_method_call(&self, func: &Expr) -> bool {
        let module_value = matches!(
            unparenthesize(func.clone()),
            Some(Expr::LongIdent(li)) if self.module_value_path(&li).is_some()
        );
        !module_value && is_member_access_callee(func)
    }

    /// Apply a synthesized function `tf` to `args` in FCS's order: split its
    /// type over every argument, relate the result to `expected`, then check
    /// each argument against its domain — unless `tf` is a union `case`
    /// whose result failed that relation, whose fields FCS then never checks.
    /// Returns the result variable.
    fn apply(
        &mut self,
        scope: &mut Scope,
        tf: TyVid,
        args: &[Expr],
        expected: Expected,
        case: bool,
    ) -> TyVid {
        let tys = self.solver.tys;
        let mut f = tf;
        let mut domains = Vec::with_capacity(args.len());
        for _ in args {
            let d = self.solver.table.fresh();
            let r = self.solver.table.fresh();
            // Genuinely true: applying `f` forces it to a function shape. But
            // a tainted unbound `f` (an earlier binding's open value, say) has
            // a type FCS may know: it is not given this shape, and what the
            // shape would relate is tainted with it. A tainted `f` that has
            // a function shape already splits by unions, which bind nothing
            // tainted.
            let fr = self.solver.table.resolve(tys.var(f));
            if scope.complete
                && matches!(tys.kind(fr), TyKind::Var(_))
                && self.solver.table.touches_taint(fr)
            {
                self.taint(scope, tys.var(d));
                self.taint(scope, tys.var(r));
            } else {
                self.eq(scope, tys.var(f), tys.fun(tys.var(d), tys.var(r)));
            }
            domains.push(d);
            f = r;
        }
        if self.relate(scope, f, expected) == Some(Decision::Failed) && case {
            return f;
        }
        for (arg, d) in args.iter().zip(domains) {
            self.infer_arg(scope, arg, d);
        }
        f
    }

    /// Check an application's argument against its domain `d`
    /// ([`Expected::Known`]): the relation is taken where FCS takes it inside
    /// the argument ([`Self::infer_expr`]).
    pub(super) fn infer_arg(&mut self, scope: &mut Scope, arg: &Expr, d: TyVid) -> Option<TyVid> {
        self.infer_expr(scope, arg, Expected::Known(d))
    }

    /// The type variable of an infix operator's value, as [`Self::infer_callee`]
    /// gives an applied name's: the resolver decides which definition the
    /// token names, so a shadowing one — in this file, in an opened module,
    /// spelled as the compiled name (`op_PipeRight`) — is the operator, and
    /// FSharp.Core's is reached only when nothing shadows it.
    ///
    /// - **An in-file binder** is an applied value like any other
    ///   ([`Self::value_use`]).
    /// - **An assembly's operator** — a member of one of its F# modules — is a
    ///   use of an assembly value ([`Self::nonlocal_value_use`]). Only a
    ///   signature with no constraint on any type parameter qualifies:
    ///   instantiating a constrained one as a plain variable would claim a
    ///   constraint is modelled that is not, which is what walk-completeness
    ///   rests on.
    /// - **A preceding file's operator** is a use of the type that file
    ///   published for it ([`Self::nonlocal_value_use`]).
    ///
    /// Anything else — a deferred lookup, a signature that does not carry
    /// over, a preceding file's operator it published no type for — declines,
    /// marking the binding incomplete with the reason.
    fn operator_value(&mut self, scope: &mut Scope, op: &Expr) -> Option<TyVid> {
        let tok = match op {
            Expr::LongIdent(li) => li.long_ident().and_then(|li| {
                let mut idents = li.idents();
                match (idents.next(), idents.next(), li.active_pat_names().next()) {
                    (Some(tok), None, None) => Some(tok),
                    _ => None,
                }
            }),
            _ => None,
        };
        let Some(tok) = tok else {
            scope.mark_incomplete(Incomplete::CalleeShape(op.syntax().kind()));
            return None;
        };
        if let Some(def) = self.facts.def_at(tok.text_range()) {
            if self.declines_use(scope, def) {
                return None;
            }
            return Some(self.value_use(scope, def));
        }
        match self.nonlocal_value_use(scope, tok.text_range(), Use::Applied) {
            Ok(v) => Some(v),
            Err(why) => {
                let why = match why {
                    Incomplete::AssemblyValue(FunctionTyGap::Constrained) => {
                        Incomplete::Operator(OperatorGap::Constrained)
                    }
                    Incomplete::AssemblyValue(_) => Incomplete::Operator(OperatorGap::Signature),
                    // A preceding file's operator, untyped there: its own reason.
                    preceding @ Incomplete::PrecedingValue(_) => preceding,
                    _ => Incomplete::Operator(OperatorGap::Unresolved),
                };
                scope.mark_incomplete(why);
                None
            }
        }
    }

    /// Synthesize the **function position** of an application, returning its type
    /// variable **without recording an expression node** (Stage 3.2c-3). FCS emits
    /// no typed node at a bare function-position use (`f` in `f x`, `add` in
    /// `add true false`) — only at the whole application — so emitting one would key
    /// a type at a range where FCS has no node and fail the differential. The callee
    /// spine is:
    ///
    /// - **A value/function reference** ([`Expr::Ident`]): resolve it; a
    ///   generalised binder instantiates its scheme afresh, a plain in-file binder
    ///   contributes its variable (poisoned if it is an *environment* reference, as
    ///   in [`Self::infer_construct`]'s ident arm). No node is emitted.
    /// - **Parentheses** ([`Expr::Paren`]): transparent — peel and recurse.
    /// - **A nested application** (curried `f x y` = `App(App(f, x), y)`): the inner
    ///   `App(f, x)` is itself a callee, so recurse through [`Self::infer_app`]-style
    ///   logic with its own node emission suppressed (an inner curried application
    ///   carries no FCS node either).
    ///
    /// Any other callee shape (an applied `DotGet`, a lambda, a literal) is
    /// unmodelled ⇒ incomplete, and the whole application defers.
    fn infer_callee(&mut self, scope: &mut Scope, e: &Expr) -> Option<TyVid> {
        self.out.enter_expression();
        let result = self.infer_callee_spine(scope, e);
        self.out.leave_expression();
        result
    }

    /// [`Self::infer_callee`] without the level count.
    fn infer_callee_spine(&mut self, scope: &mut Scope, e: &Expr) -> Option<TyVid> {
        match e {
            Expr::Paren(p) => {
                let Some(inner) = p.inner() else {
                    scope.mark_incomplete(Incomplete::Recovery);
                    return None;
                };
                self.infer_callee(scope, &inner)
            }
            // A nested (curried) application in function position: type it as an
            // application whose residual `r` is the callee type, recording **no**
            // node ([`Self::infer_app`] never emits — an inner curried application
            // carries no FCS node either). It still pushes its own
            // `Eq(tf, Fun(d, r))` and checks its argument. A bracket-indexer
            // `App` in the callee spine is unmodelled (⇒ the catch-all below
            // marks incomplete and the whole application defers).
            Expr::App(inner) if !inner.is_infix() && !inner.is_bracket_indexer() => {
                self.infer_app(scope, inner, Expected::Synth)
            }
            // A value/function reference: mirror the ident arm's resolution, but
            // *do not* emit a node.
            Expr::Ident(ident) => {
                let Some(tok) = ident.ident() else {
                    scope.mark_incomplete(Incomplete::Recovery);
                    return None;
                };
                let def = self
                    .facts
                    .def_at(tok.text_range())
                    .filter(|_| !self.facts.own_union_case_at(tok.text_range()));
                let Some(def) = def else {
                    return self.nonlocal_value_or_incomplete(
                        scope,
                        tok.text_range(),
                        Use::Applied,
                    );
                };
                if self.declines_use(scope, def) {
                    return None;
                }
                Some(self.value_use(scope, def))
            }
            // A module-qualified value (`List.map f`).
            Expr::LongIdent(li) => match self.module_value_path(li) {
                Some(whole) => self.nonlocal_value_or_incomplete(scope, whole, Use::Applied),
                None => {
                    scope.mark_incomplete(Incomplete::CalleeShape(e.syntax().kind()));
                    None
                }
            },
            _ => {
                scope.mark_incomplete(Incomplete::CalleeShape(e.syntax().kind()));
                None
            }
        }
    }
}

/// Whether an application's callee is a **member access** — the shape a method
/// call `recv.Method(args)` has in function position (Stage 3.3d). A dotted
/// `LONG_IDENT_EXPR` (`s.M`) or a `DOT_GET_EXPR` (`"hi".M`) callee routes to
/// method typing; parentheses are transparent. Any other callee (a bare value
/// `f`, `(+)` or `(|P|_|)`, a nested application) is an ordinary value
/// application. Pure classification (no
/// side effects), so [`Gen::infer_app`] can commit to the method path only when it
/// applies; [`Gen::method_callee`] then does the resolution and may still defer.
fn is_member_access_callee(e: &Expr) -> bool {
    match e {
        // A single segment — an operator or active-pattern name in
        // parentheses, `(+)` or `(|P|_|)` — names a value, and so does a path
        // through an active-pattern segment: neither is a member access.
        Expr::LongIdent(li) => li
            .long_ident()
            .is_some_and(|l| l.active_pat_names().next().is_none() && l.idents().nth(1).is_some()),
        Expr::DotGet(_) => true,
        Expr::Paren(p) => p
            .inner()
            .is_some_and(|inner| is_member_access_callee(&inner)),
        _ => false,
    }
}
