//! The walk over expressions ([`Gen::infer_expr`]): each construct,
//! expression-level `let`s, sequential expressions and conditions.

use super::*;

impl<'a> Gen<'a> {
    /// Synthesize the type variable of expression `e`, generating its
    /// constraints, in **bidirectional** style, against what its context
    /// expects ([`Expected`]):
    ///
    /// - [`Expected::Synth`] — a **coercion-free** position (the bare `let`
    ///   RHS, an unannotated tuple element, an `if` *then*-branch). No expected
    ///   type reaches the expression, so its elaborated type *is* its
    ///   synthesized type, and the node is **recorded** for emission.
    /// - [`Expected::Known`] / [`Expected::Unknown`] — a *check* position (a
    ///   function argument against the domain, an `else` branch against the
    ///   result, a method argument against the parameter). The node is **not**
    ///   recorded: its elaborated type may be a coercion of the synthesized one.
    ///   The relation to the expected type is taken where FCS takes it, by
    ///   each form ([`Self::relate`]).
    ///
    /// A check-position form that does not synthesize a variable (an
    /// unmodelled one, which ends the prefix where it is met) leaves its
    /// expected variable related by nothing FCS's derivation lacks, but poisoned
    /// so it does not generalise.
    pub(super) fn infer_expr(
        &mut self,
        scope: &mut Scope,
        e: &Expr,
        expected: Expected,
    ) -> Option<TyVid> {
        let result = self.infer_expr_inner(scope, e, expected);
        if result.is_none()
            && let Some(d) = expected.target()
        {
            scope.poison.push(d);
        }
        result
    }

    /// [`Self::infer_expr`] without its poison: the per-construct rules
    /// ([`Self::infer_construct`]), with a **check-mode subtree recording
    /// nothing**.
    ///
    /// Check mode already suppresses the node of the checked expression itself;
    /// this extends that to everything walked beneath it, which is what makes the
    /// rule hold for the few synth positions that can sit inside a check position
    /// — a member access's receiver, a local `let`'s RHS and its binder. FCS
    /// rejects in check positions: an application of a non-function, or a method
    /// call it cannot resolve, keeps no node and no binder anywhere inside its
    /// argument, so `k0 (s.Length)` has no node at `s`. Which check positions FCS
    /// will reject is not known while walking, so none of them emits. The walk
    /// itself still runs — its constraints and member wakes are true either way.
    pub(super) fn infer_expr_inner(
        &mut self,
        scope: &mut Scope,
        e: &Expr,
        expected: Expected,
    ) -> Option<TyVid> {
        self.out.enter_expression();
        self.note_lost_prefix(scope);
        let result = if expected.records() {
            self.infer_construct(scope, e, expected)
        } else {
            let mark = self.out.mark();
            let result = self.infer_construct(scope, e, expected);
            self.out.discard_since(mark);
            result
        };
        self.out.leave_expression();
        result
    }

    /// The per-construct generation rules (the body of [`Self::infer_expr`],
    /// without its poison or [`Self::infer_expr_inner`]'s check-mode
    /// barrier). Every arm that returns `None` because a sub-expression is
    /// unmodelled, and every unwalked child, marks the binding walk-incomplete
    /// ([`Scope::mark_incomplete`]), which ends its faithful prefix there:
    /// such an arm marks it *before* walking anything beneath it, so no
    /// decision below is taken against a relation FCS took and inference
    /// skipped. Each arm relates its type to `expected` where FCS does
    /// ([`Self::relate`]).
    fn infer_construct(
        &mut self,
        scope: &mut Scope,
        e: &Expr,
        expected: Expected,
    ) -> Option<TyVid> {
        match e {
            // A bare literal. A measure literal (`1.0<kg>`) is an
            // `Expr::MeasureLit`, not `Expr::Const`, so it is excluded
            // structurally — its inner numeric token is *not* the measured type.
            Expr::Const(c) => {
                let Some(ty) = literal_ty(self.facts.env.names(), self.solver.tys, c) else {
                    // A deferred literal (`USER_NUM_LIT`, a source-location
                    // identifier) is unmodelled — its type is not fixed even in
                    // isolation — so the binding must not generalise.
                    scope.mark_incomplete(Incomplete::DeferredLiteral);
                    return None;
                };
                let v = self.solver.table.fresh();
                self.eq(scope, self.solver.tys.var(v), ty);
                // The literal *token*'s range, not the `ConstExpr` node's: in a
                // tuple element (`(1, "hi")`) the node range swallows the leading
                // ` ` trivia after the comma, but FCS's node spans only the
                // literal. `()` is two tokens, and FCS spans both.
                if is_unit_literal(e) {
                    self.emit(self.facts.node_span(c.syntax()), v, expected);
                } else if let Some(lit) = c.literal() {
                    self.emit(lit.text_range(), v, expected);
                }
                self.relate(scope, v, expected);
                Some(v)
            }
            // A value use: its type is the referenced binder's. In synth mode the
            // use occurrence is emitted at its own range; a use resolving to a
            // non-in-file target, or to a binder we never typed, leaves its
            // variable unbound and so stays Deferred at read-off. A use resolving
            // to a **generalised** binder ([`BinderEnv::scheme`]) instantiates the
            // scheme with fresh variables per distinct [`TyKind::Param`] (Stage
            // 3.2c-2c) — checked *before* the plain `def_var` path.
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
                    // A referenced assembly's value, read off its signature, or
                    // a union case; anything else that is not an in-file binder
                    // (a preceding file's, a deferred name) is unmodelled.
                    let uv =
                        self.nonlocal_value_or_incomplete(scope, tok.text_range(), Use::Value)?;
                    if !self.facts.case_of_fields_at(tok.text_range()) {
                        self.emit(tok.text_range(), uv, expected);
                    }
                    self.relate(scope, uv, expected);
                    return Some(uv);
                };
                if self.declines_use(scope, def) {
                    return None;
                }
                let uv = self.value_use(scope, def);
                self.emit(tok.text_range(), uv, expected);
                self.relate(scope, uv, expected);
                Some(uv)
            }
            // Parentheses are transparent: the type, position (so `expected`
            // passes straight through), and emission are the inner expression's;
            // FCS's elaborated tree has no node at the parens. (3.2b-2) A `Paren`
            // wrapping a recovery hole (no inner expression) is unmodelled.
            Expr::Paren(p) => {
                let Some(inner) = p.inner() else {
                    scope.mark_incomplete(Incomplete::Recovery);
                    return None;
                };
                self.infer_expr(scope, &inner, expected)
            }
            // A reference tuple `(a, b, …)`: `TyKind::Tuple` of the element types. The
            // elements share the tuple's mode — coercion-free (emitted) only when
            // the tuple itself is synth; in check mode the elements are
            // coercion-possible (an expected tuple type could retarget them, e.g.
            // `(3, 4)` against `int64 * int64`), so they are checked, not emitted.
            // An element we can't type becomes a fresh unbound var, so the *tuple*
            // is omitted (not ground) while typeable synth-mode elements emit.
            // (3.2b-2, mode propagation 3.2c-1)
            //
            // Against a known expected type FCS splits it before checking the
            // elements (`TcExprTuple`) when it is a tuple or a variable, so
            // each element is checked against its element type; against any
            // other it checks the tuple on its own and relates it at the end
            // ([`Self::tuple_element_expectations`]). Under an unknown
            // expected type each element's is unknown too.
            Expr::Tuple(t) => {
                // Struct tuples (`struct (a, b)`) have a distinct runtime type
                // and canonical rendering; defer them (unmodelled).
                if t.is_struct() {
                    scope.mark_incomplete(Incomplete::StructTuple);
                    return None;
                }
                let arity = t.elements().count();
                let (elem_expected, relate_at_end) =
                    self.tuple_element_expectations(scope, expected, arity);
                let elems: Vec<Ty> = t
                    .elements()
                    .enumerate()
                    .map(|(i, el)| {
                        let elem_expected =
                            elem_expected.get(i).copied().unwrap_or(Expected::Unknown);
                        match self.infer_expr(scope, &el, elem_expected) {
                            Some(v) => self.solver.tys.var(v),
                            None => {
                                // An element we cannot type leaves the tuple
                                // un-ground; the element's own recursion already set
                                // incomplete, but this arm may also be reached for a
                                // recovery hole — be explicit.
                                scope.mark_incomplete_propagated();
                                self.solver.tys.var(self.solver.table.fresh())
                            }
                        }
                    })
                    .collect();
                // A well-formed tuple has ≥ 2 elements; anything less is a
                // degenerate parse, not a tuple type.
                if elems.len() < 2 {
                    scope.mark_incomplete(Incomplete::Recovery);
                    return None;
                }
                let tv = self.solver.table.fresh();
                self.eq(scope, self.solver.tys.var(tv), self.solver.tys.tuple(elems));
                self.emit(self.facts.node_span(t.syntax()), tv, expected);
                if relate_at_end {
                    self.relate(scope, tv, expected);
                }
                Some(tv)
            }
            // `if c then a else b`: F# uses the *then*-branch's type as the result
            // and coerces `else` to it. The then-branch carries the if's mode (the
            // result's source); the else-branch is checked against the result (a
            // coercion-possible position — not emitted). The condition is left to
            // name resolution — typing it as `bool` needs modelled function types
            // to stay sound (see the module docs), a later slice.
            //
            // In **synth** mode the result is the then-branch's synthesized type;
            // if the then-branch can't synthesize, the whole `if` defers (its type
            // is unknown — we must *not* take it from the coercible else, which FCS
            // may retarget). An `if` **without a final `else`** is *not*
            // synthesized: `if c then a` (and an `elif` chain with no trailing
            // `else`, e.g. `if a then 1 elif b then 2`) desugars with an implicit
            // `else ()`, so its result is `unit` and the then-branch sits in a unit
            // *check* position — emitting its synthesized type would disagree with
            // FCS, so we defer the whole `if` ([`if_chain_has_final_else`]). In
            // **check** mode both branches are checked against the expected type and
            // nothing is emitted. (3.2c-1)
            Expr::IfThenElse(if_expr) => {
                // The condition is `bool` in either mode (F# admits no coercion
                // there), so constrain it regardless of the `if`'s own mode — this
                // grounds a parameter used directly as a condition (3.2c-2b).
                self.constrain_bool(scope, if_expr.condition());
                match expected {
                    Expected::Synth => {
                        // An `if` with no final `else` desugars to `else ()`
                        // (result `unit`), which this stage does not model — defer,
                        // and mark incomplete (its then-branch's true type is a
                        // dropped unit-check relation).
                        if !if_chain_has_final_else(if_expr) {
                            scope.mark_incomplete(Incomplete::ElselessIf);
                            return None;
                        }
                        let Some(then_branch) = if_expr.then_branch() else {
                            scope.mark_incomplete(Incomplete::Recovery);
                            return None;
                        };
                        // A then-branch that cannot synthesize leaves the `if`'s
                        // result unknown; its recursion already set incomplete.
                        let then_var = self.infer_expr(scope, &then_branch, Expected::Synth)?;
                        // FCS checks the `else` branch against the overall
                        // type the `then` branch fixed, before anything in it.
                        if let Some(else_branch) = if_expr.else_branch() {
                            self.infer_expr(scope, &else_branch, Expected::Known(then_var));
                        }
                        self.emit(
                            self.facts.node_span(if_expr.syntax()),
                            then_var,
                            Expected::Synth,
                        );
                        Some(then_var)
                    }
                    // Each branch is checked against the overall type itself,
                    // known or not, which relates it where FCS does.
                    Expected::Known(_) | Expected::Equal(_) | Expected::Unknown => {
                        // Without an `else` FCS relates the overall type to
                        // `unit` before the branch, which it then checks
                        // against `unit`. (An `elif` chain is an `if` in the
                        // `else` of another, which meets this rule itself.)
                        if if_expr.else_branch().is_none() {
                            let unit = self.solver.table.fresh();
                            let unit_ty = self.solver.tys.named(self.facts.env.names(), UNIT);
                            self.eq(scope, self.solver.tys.var(unit), unit_ty);
                            // FCS's `unit` equality is strict: where it fails, or
                            // against a type not known here, FCS reports it and
                            // what it checks next is not known, so the prefix
                            // ends before the branch.
                            let related = match expected.target() {
                                Some(d) => self.decide(scope, unit, d) == Decision::Taken,
                                None => false,
                            };
                            let branch_expected = if related {
                                Expected::Known(unit)
                            } else {
                                scope.mark_incomplete(Incomplete::ElselessIf);
                                Expected::Unknown
                            };
                            if let Some(then_branch) = if_expr.then_branch() {
                                self.infer_expr(scope, &then_branch, branch_expected);
                            }
                            return Some(unit);
                        }
                        // Under an equality the `then` branch is exact, but
                        // the `else` branch is checked against the type the
                        // `then` branch fixed, which admits a coercion: it
                        // records nothing.
                        let else_expected = match expected {
                            Expected::Equal(d) => Expected::Known(d),
                            other => other,
                        };
                        let mut result = None;
                        if let Some(then_branch) = if_expr.then_branch() {
                            result = self.infer_expr(scope, &then_branch, expected);
                        }
                        if let Some(else_branch) = if_expr.else_branch() {
                            self.infer_expr(scope, &else_branch, else_expected);
                        }
                        if let Expected::Equal(exp) = expected {
                            self.emit(self.facts.node_span(if_expr.syntax()), exp, expected);
                        }
                        // Against a known expected type the `if` is that type;
                        // under an equality it is what its `then` branch is,
                        // which the caller compares with what it expected.
                        match expected {
                            Expected::Known(d) => Some(d),
                            _ => result,
                        }
                    }
                }
            }
            // `match e with p1 when g1 -> r1 | …`, in FCS's checking order
            // (`TcMatchClauses`): the scrutinee first, then each clause in
            // source order — its pattern against the scrutinee's type, by
            // equality; its guard as a condition, `bool` by equality; its
            // result. The arms agree as an `if`'s branches do: with no
            // expected type the first synthesises the match's type and the
            // rest are checked against it, else each is checked against the
            // expected type.
            Expr::Match(m) => {
                let Some(scrutinee) = m.scrutinee() else {
                    scope.mark_incomplete(Incomplete::Recovery);
                    return None;
                };
                // FCS elaborates a match of one clause to other nodes than
                // its source's (`match o with _ -> "s"` keeps no node at
                // `"s"`), so its dump cannot grade one; such a match is the
                // rare spelling of a `let`, and declines.
                if m.clauses().nth(1).is_none() {
                    scope.mark_incomplete(Incomplete::Unmodelled(SyntaxKind::MATCH_EXPR));
                    return None;
                }
                // FCS's decision compiler keeps no node or binder of a
                // clause no value reaches (FS0026: `_ -> 1 | Some x -> x`, or
                // a case repeated without a guard), and none in a first clause
                // that matches everything either (`() -> 1 | _ -> 2` keeps no
                // node at `1`), so a match with an unreachable clause declines
                // before any of it is walked, as a match of one clause does.
                if !self.every_clause_provably_reachable(m) {
                    scope.mark_incomplete(Incomplete::UnreachableClause);
                    return None;
                }
                let mark = self.out.mark();
                let sv = self.infer_expr(scope, &scrutinee, Expected::Synth)?;
                // FCS may bind the scrutinee to a temporary at the
                // scrutinee's own range — a `let` node typed as the whole
                // match (`match c with 'a' -> true | _ -> false` reports
                // `bool` at `c`) — so the scrutinee's own node, the last its
                // walk emitted, is not one FCS's dump can grade. What it
                // contains is.
                self.out.ungrade_last_since(mark);
                let mut first: Option<TyVid> = None;
                let mut any = false;
                for clause in m.clauses() {
                    let (Some(pat), Some(body)) = (clause.pat(), clause.result()) else {
                        scope.mark_incomplete(Incomplete::Recovery);
                        return None;
                    };
                    // A name bound twice is FS0038 (FCS keeps the second),
                    // as for a `let` pattern.
                    if binds_a_name_twice(std::slice::from_ref(&pat)) {
                        scope.mark_incomplete(Incomplete::DuplicateBinder);
                        return None;
                    }
                    let shape =
                        match self.pattern_shape_in(&pat, PatSite::Match, AnnotationCx::Plain) {
                            Ok(shape) => shape,
                            Err(why) => {
                                scope.mark_incomplete(why);
                                return None;
                            }
                        };
                    shape.names(&mut scope.match_locals);
                    // Every equality the pattern generates — its fields'
                    // included — counts toward its fit, so the count is taken
                    // before it is generated, once what came before settled.
                    self.settle(scope);
                    let failures = scope.eq_failures;
                    let pt = self.gen_pattern(scope, &shape, BinderSite::Local);
                    // As for a `let` pattern ([`Self::pattern_rhs`]): a
                    // pattern of structure must not give an earlier binding's
                    // open variable a shape of this binding's variables
                    // (`let a = None` then `match a with Some 1 -> …` would
                    // retype `a`, which FCS keeps `'a option`).
                    // Nor one whose resolution FCS decides by something
                    // inference does not see — a local FCS may generalise
                    // (`let g = idf in match g ho with Some 1 -> …` keeps
                    // `idf : 'a -> 'a`) — the variables an argument check
                    // refuses to bind too ([`Self::touches_opaque`]).
                    self.settle(scope);
                    if !matches!(self.solver.tys.kind(pt), TyKind::Var(_))
                        && (self.mentions_inherited_open(scope, sv)
                            || self.touches_opaque(scope, sv, sv))
                    {
                        scope.mark_incomplete(Incomplete::InheritedOpen);
                        return None;
                    }
                    // FCS checks in source order, so an argument check still
                    // pending here was applied before this pattern: a pattern
                    // that contradicts one (`(fs x, match x with 1 -> …)` with
                    // `fs : string -> _`) is the one FCS rejects, and relating
                    // it now would fix the scrutinee in the check's place.
                    if !matches!(self.solver.tys.kind(pt), TyKind::Var(_))
                        && self.pattern_preempts_earlier_relation(scope, sv, pt)
                    {
                        scope.mark_incomplete(Incomplete::PatternAfterCheck);
                        return None;
                    }
                    // An unmodelled construct before the pattern may have
                    // fixed what the scrutinee's open variables are in FCS
                    // (`Some x -> (if x then …) | Some "" -> …` makes `x`
                    // `bool`, then rejects the pattern), and it left no
                    // relation to probe; so on an incomplete binding a
                    // pattern of structure relates only a ground scrutinee.
                    if !scope.complete
                        && !matches!(self.solver.tys.kind(pt), TyKind::Var(_))
                        && !self
                            .solver
                            .tys
                            .is_ground(self.solver.table.resolve(self.solver.tys.var(sv)))
                    {
                        scope.mark_incomplete(Incomplete::PatternAfterCheck);
                        return None;
                    }
                    self.eq(scope, self.solver.tys.var(sv), pt);
                    // The pattern's names are typed before the clause's uses
                    // of them are walked, so a use reads a known type
                    // ([`Self::value_use`]).
                    self.settle(scope);
                    // A pattern that does not fit the scrutinee fails whole
                    // (atomically), leaving its names untyped where FCS typed
                    // the part that fit before rejecting the rest (`(x, 1)`
                    // against `int * string` keeps `x : int`): the clause
                    // declines rather than let its body type them.
                    if scope.eq_failures > failures {
                        scope.mark_incomplete(Incomplete::PatternMismatch);
                        return None;
                    }
                    if clause.guard().is_some() {
                        self.constrain_bool(scope, clause.guard());
                    }
                    // With no expected type the first clause's result fixes
                    // the overall type, and each later one is checked against
                    // it; otherwise each is checked against the expected type.
                    let arm_expected = match (expected, first) {
                        (Expected::Synth, Some(first)) => Expected::Known(first),
                        // Under an equality only the first clause is exact:
                        // the rest are checked against the type it fixed.
                        (Expected::Equal(d), Some(_)) => Expected::Known(d),
                        _ => expected,
                    };
                    let v = self.infer_expr(scope, &body, arm_expected);
                    if first.is_none() {
                        first = Some(v?);
                    }
                    any = true;
                }
                if !any {
                    scope.mark_incomplete(Incomplete::Recovery);
                    return None;
                }
                // Nothing is emitted at the match itself: FCS elaborates
                // some matches to other nodes (a single irrefutable clause,
                // `match o with x -> x`, is a `let`), so whether its dump has
                // a node there is its decision compiler's to say.
                match expected {
                    Expected::Known(d) => Some(d),
                    _ => first,
                }
            }
            // A lambda `fun x … -> body`. Walk the body so its sub-expressions get
            // typed, carrying the lambda's **mode**: coercion-free (synth) only when
            // the lambda itself is (a bare `let g = fun … -> …`); reached in *check*
            // mode (e.g. an `if`-branch checked against another function), an
            // expected function type could retarget the body, so we check it —
            // emission suppressed. The lambda's own function type is not modelled
            // yet (`TyKind::Fun` is a later slice), so it defers. A param use in the
            // body binds lazily via name resolution. (3.2c-2a)
            Expr::Fun(fun) => {
                // The lambda's own function type is not modelled yet (`TyKind::Fun` on
                // a `fun` value is a later slice), so it defers — and marks the
                // binding incomplete, since a body containing a lambda has an FCS
                // type we cannot reproduce. FCS relates the expected type to the
                // lambda's before its body, so the prefix ends here, before
                // anything in the body is decided.
                scope.mark_incomplete(Incomplete::Lambda);
                if let Some(body) = fun.body() {
                    let body_expected = if expected.is_synth() {
                        Expected::Synth
                    } else {
                        Expected::Unknown
                    };
                    // A lambda's parameters are elaborated as a function's
                    // are: behind a non-simple one the body's nodes move, so
                    // it records nothing (see [`is_simple_param`]).
                    let body_mark = self.out.mark();
                    self.infer_expr(scope, &body, body_expected);
                    if !fun.args().all(|arg| is_simple_param(&arg)) {
                        self.out.discard_since(body_mark);
                    }
                }
                None
            }
            // A `while c do body`: the condition is constrained to `bool`
            // (3.2c-2b), and the body is **checked against `unit`** — a check (not
            // synth) position — so it is walked in check mode (emission suppressed:
            // a non-unit body is a coercion/error FCS reports as `unit`, not the
            // body's synthesized type). The loop's own `unit` type is left to a
            // later slice. (3.2c-2a / 3.2c-2b)
            Expr::While(while_expr) => {
                // A `while` expression's own `unit` type is not modelled yet, so it
                // defers — and marks the binding incomplete. FCS relates that type
                // to the expected one before the condition, so the prefix ends
                // before anything in the loop is decided.
                scope.mark_incomplete(Incomplete::While);
                self.constrain_bool(scope, while_expr.cond());
                if let Some(body) = while_expr.body() {
                    self.infer_expr(scope, &body, Expected::Unknown);
                }
                None
            }
            // Function application `f x` (Stage 3.2c-3). Both `APP_EXPR` and
            // `INFIX_APP_EXPR` cast to `Expr::App`. An infix `x + 1` is the outer
            // (non-infix) `APP_EXPR` applying the inner `INFIX_APP_EXPR` `(+) x`,
            // so it is matched here and its inner application is a callee
            // ([`Self::infer_callee`]). A **bracket indexer** (`arr[i]`, which F#
            // lowers to a `GetSlice`/`Item` member lookup unless `arr` unifies
            // with a function type, but the parser still stores under `APP_EXPR`)
            // stays unmodelled ⇒ incomplete, as do `TypeApp`, applied `DotGet`,
            // and everything else (the catch-all below / other arms). Curried
            // `f x y` falls out of the nested `App`s. A markerless `(f x)[1]` is
            // an application here, which is FCS's reading whenever the shape `Eq`
            // succeeds (see `AppExpr::is_bracket_indexer`); when it fails, the
            // result is poisoned, as for any failed application.
            Expr::App(app) if !app.is_infix() && !app.is_bracket_indexer() => {
                let r = self.infer_app(scope, app, expected)?;
                self.emit(self.facts.node_span(app.syntax()), r, expected);
                Some(r)
            }
            // A dotted long-ident `s.Length` (Stage 3.3a). The parser stores a
            // value-receiver member access as a `LONG_IDENT_EXPR` (its head resolves
            // to the receiver value; the trailing segments are the members) — *not*
            // a `DotGet`, which is the `(expr).Member` shape below. This arm only
            // fires when the **head** segment resolves to an in-file value binder: a
            // fully-qualified static path (`System.Console.WriteLine`, whose head is
            // a namespace/type, not a value) is left unmodelled here (the catch-all
            // defers it, so the static-member `Member` resolution is untouched — no
            // regression). The receiver's own value node is emitted at the head
            // range (FCS emits a `value:module` node there), then the members chain.
            Expr::LongIdent(li) => self.infer_long_ident_member(scope, li, expected),
            // A `(expr).Member` member access (Stage 3.3a). Both `"hi".Length` and
            // `(f x).Foo` parse as `DOT_GET_EXPR`: an inner receiver *expression*
            // plus a `LongIdent` member path. The receiver is synthesized (its own
            // node emitted where FCS has one — e.g. the `"hi"` literal), and the
            // member path chains from its variable.
            Expr::DotGet(dg) => self.infer_dot_get(scope, dg, expected),
            // An expression-level `let … in` (CE-1). The bang, `use` and `rec`
            // forms stay unmodelled: a `let!` is a builder call, a `use` a
            // disposal, and a recursive group's bindings constrain each other.
            Expr::LetOrUse(e) if !e.is_bang() && !e.is_use() && !e.is_rec() => {
                self.infer_let_in(scope, e, expected)
            }
            Expr::Sequential(seq) => self.infer_sequential(scope, seq, expected),
            // Any other expression shape is unmodelled: defer and mark incomplete
            // (the FCS type on this subtree is one we did not reproduce, so an
            // enclosing binding must not generalise). This catches a
            // **bracket-indexer** `App` too, which the guarded arm above deliberately
            // does not match, and an infix `App` outside a callee position, which
            // only a recovered parse produces.
            _ => {
                scope.mark_incomplete(Incomplete::Unmodelled(e.syntax().kind()));
                None
            }
        }
    }

    /// An expression-level `let … in body` (CE-1): each binding is a local
    /// ([`Self::local_binding`]), and the whole expression is typed as its body,
    /// which carries the `let`'s own mode.
    ///
    /// No node is recorded for the `let` itself. FCS keys its `Let` node at the
    /// *binder's identifier* range, typed as the **body** (`let y = 1 in "s"`
    /// puts `string` at `y`), so the only range it could go at is one where the
    /// binder is also named — and the binder's own type lives on
    /// [`InferredFile::def_type`], not there.
    ///
    /// Reached in check mode, the `let` records nothing at all — neither its
    /// RHS nodes nor its binders — by [`Self::infer_expr_inner`]'s barrier.
    fn infer_let_in(
        &mut self,
        scope: &mut Scope,
        e: &LetOrUseExpr,
        expected: Expected,
    ) -> Option<TyVid> {
        for binding in e.bindings() {
            // A local that may carry `[<EntryPoint>]` is not typed, as at
            // module level ([`Self::let_binding`]).
            if self.facts.may_be_entry_point(e.syntax())
                || self.facts.may_be_entry_point(binding.syntax())
            {
                scope.mark_incomplete(Incomplete::LocalBindingShape);
                continue;
            }
            self.local_binding(scope, &binding);
        }
        let Some(body) = e.body() else {
            scope.mark_incomplete(Incomplete::Recovery);
            return None;
        };
        let body_mark = self.out.mark();
        let result = self.infer_expr(scope, &body, expected);
        if e.bindings().any(|b| moves_its_continuation(&b)) {
            self.out.discard_since(body_mark);
        }
        result
    }

    /// One binding of an expression-level `let` (CE-1). A **local is not
    /// monomorphic** in F#: FCS generalises an eligible one (`let local = idf`
    /// is `'a -> 'a`), and one shared variable is wrong for such a local — in
    /// `(local 1, local "s")` the first use's argument check would ground it to
    /// `int`, and the second use's result would read back `int` where FCS has
    /// `string`.
    ///
    /// So a local types only when it is **ground on its own**, before the
    /// continuation is walked: the pattern is typed ([`Self::pattern_ty`]), the
    /// RHS is inferred and linked to it, and the constraints so far are
    /// [settled](Self::settle). A ground binder can then only be *confirmed* by
    /// the continuation — a conflicting use fails and rolls back, exactly as
    /// FCS reports the use rather than retyping the binder. A binder still open
    /// at that point is one FCS may have generalised, or grounded through
    /// something we do not model, so the binding is marked **incomplete**: no
    /// argument check fires in it, which is the one channel through which a
    /// use could ground the local's variable, and nothing in it generalises.
    ///
    /// FCS checks the RHS against the pattern's type, which decides what it
    /// keeps of the RHS's nodes ([`Self::pattern_rhs`]).
    ///
    /// A function head or a return annotation is unmodelled, as is a pattern
    /// [`Self::pattern_ty`] rejects: the binding is marked incomplete and its
    /// RHS is not walked. Its binders get variables lazily at their uses,
    /// open, and only the incompleteness keeps them from being grounded there.
    fn local_binding(&mut self, scope: &mut Scope, binding: &Binding) {
        let (None, Some(pat), Some(rhs)) = (binding.return_type(), binding.pat(), binding.expr())
        else {
            scope.mark_incomplete(Incomplete::LocalBindingShape);
            return;
        };
        if matches!(pat, Pat::LongIdent(_)) {
            scope.mark_incomplete(Incomplete::LocalBindingShape);
            return;
        }
        let recorded = scope.reasons_recorded();
        let pat_from = self.solver.table.mark();
        let pat_ty = match self.binding_pattern_ty(scope, binding, &pat, BinderSite::Local) {
            Ok(t) => t,
            Err(why) => {
                scope.mark_incomplete(why);
                return;
            }
        };
        self.pattern_rhs(scope, &pat, pat_ty, pat_from, &rhs, BinderSite::Local);
        // The whole pattern's type, not just its names': a wildcard binds
        // nothing, but an RHS still open under it is as unsettled as a named
        // one.
        if !self.solver.tys.is_ground(self.solver.table.resolve(pat_ty)) {
            scope.mark_consequence(recorded, Incomplete::OpenLocal);
        }
    }

    /// Walk the RHS of a pattern binding against the pattern's type `pat_ty`
    /// and [settle](Self::settle), for a binding at `site`.
    ///
    /// FCS checks the RHS *against* the pattern's type. What that relation is
    /// depends on whether the pattern holds an annotation.
    ///
    /// **Annotated** (`let (a: obj, b) = …`): the check is a coercion position,
    /// so the relation is subsumption, which is not modelled. An equality in
    /// its place would be wrong both ways — it would write the annotation's
    /// type into whatever the RHS mentions (an earlier binder FCS generalised,
    /// a parameter a condition grounds), and it fails on a legal coercion. So
    /// the relation is dropped: the RHS is walked in check mode, recording
    /// nothing, and the binding is marked incomplete. The annotated names keep
    /// their annotations' types, which hold at the binder whatever the RHS.
    ///
    /// **Unannotated**: the pattern's type is a tuple tree of fresh variables,
    /// so the relation is an equality, and one that can only bind those fresh
    /// variables or impose tuple structure — never a type the RHS did not
    /// have. It is added after the RHS's own constraints have settled, since
    /// FCS resolves those first, and only if the settled RHS holds no earlier
    /// binding's open variable ([`Self::mentions_inherited_open`]). What FCS keeps of the RHS's nodes is mirrored
    /// in two ways:
    ///
    /// - A local pattern binding (not a bare name) whose RHS is a bare value
    ///   binds that value directly, and FCS keeps no node for it. So a name or
    ///   dotted path RHS is walked in check mode, which records nothing; for a
    ///   name that loses nothing else, and a dotted path (which may be a
    ///   qualified value, or a member access FCS does keep) gives up its
    ///   receiver's nodes too.
    /// - A check that fails drops the RHS's nodes — how far down depends on
    ///   where the expected type stops propagating (a tuple of the wrong arity
    ///   keeps none of its elements). So the RHS's nodes stand only if the
    ///   equality holds once settled. A relation still pending then is an
    ///   argument check, which FCS resolves after pushing the pattern's type
    ///   into the call, so it may fail inside the call's argument; but an
    ///   argument's nodes are never recorded, so nothing kept here sits there.
    pub(super) fn pattern_rhs(
        &mut self,
        scope: &mut Scope,
        pat: &Pat,
        pat_ty: Ty,
        pat_from: u32,
        rhs: &Expr,
        site: BinderSite,
    ) {
        let annotated = pat
            .syntax()
            .descendants_where(|k| k == SyntaxKind::TYPED_PAT)
            .next()
            .is_some();
        if annotated {
            // FCS relates the RHS to the annotation as it enters it, so the
            // prefix ends before the RHS is walked.
            scope.mark_incomplete(Incomplete::CoercedPattern);
            self.infer_expr(scope, rhs, Expected::Unknown);
            self.settle(scope);
            return;
        }
        let bound_directly = site == BinderSite::Local
            && !matches!(pat, Pat::Named(_))
            && matches!(
                unparenthesize(rhs.clone()),
                Some(Expr::Ident(_) | Expr::LongIdent(_))
            );
        // A pattern that is a single variable (a name, a wildcard) imposes no
        // structure, so its check cannot fail, and the RHS's nodes stand even
        // when the RHS itself does not synthesize.
        let structural = !matches!(self.solver.tys.kind(pat_ty), TyKind::Var(_));
        // The pattern's own variables: every one made since `pat_from`, the
        // pattern being the last thing typed.
        let own = pat_from..self.solver.table.mark();
        // FCS checks the RHS against the pattern's type, by equality: a
        // pattern of structure is related where the RHS's form relates its
        // expected type — an application's result before its arguments.
        let expected = if bound_directly {
            Expected::Known(self.solver.table.fresh())
        } else if structural && scope.complete {
            let pv = self.solver.table.fresh();
            self.eq(scope, self.solver.tys.var(pv), pat_ty);
            Expected::Equal(pv)
        } else {
            Expected::Synth
        };
        let mark = self.out.mark();
        let rhs_var = self.infer_expr(scope, rhs, expected);
        self.settle(scope);
        if structural
            && rhs_var.is_some_and(|v| {
                self.mentions_inherited_open(scope, v)
                    || (scope.complete && self.touches_opaque(scope, v, v))
            })
        {
            // The equality would give an earlier binding's open variable a
            // structure of this binding's fresh variables, which then pass for
            // this binding's own: an argument check could ground them, and so
            // retype the earlier binder. Nor, while the prefix is faithful,
            // may it give one whose type FCS may know and inference does not
            // (a tainted one) a structure: that is a decision, which such a
            // variable declines. (Once the prefix has ended no decision is
            // taken, and the equality is applied unless it binds a variable
            // older than that end, below.) The relation is dropped instead.
            scope.mark_incomplete(Incomplete::InheritedOpen);
            self.out.discard_since(mark);
            return;
        }
        // Related inside the walk where it was decided, the prefix faithful
        // throughout ([`Expected::Equal`]); otherwise here.
        if let Some(rhs_var) = rhs_var
            && !(matches!(expected, Expected::Equal(_)) && scope.complete)
        {
            let rhs_ty = self.solver.tys.var(rhs_var);
            if structural && !scope.complete {
                if !self.eq_sparing_older(scope, pat_ty, rhs_ty, own) {
                    // FCS may have bound the variable through the construct
                    // that ended the prefix (`(p : int), (let () = p in ())`),
                    // so the pattern's structure is not imposed on it.
                    scope.mark_incomplete(Incomplete::InheritedOpen);
                    self.out.discard_since(mark);
                    return;
                }
            } else {
                self.eq(scope, pat_ty, rhs_ty);
            }
        }
        self.settle(scope);
        let agrees = rhs_var.is_some_and(|v| {
            self.solver.table.resolve(pat_ty) == self.solver.table.resolve(self.solver.tys.var(v))
        });
        if structural && !agrees {
            self.out.discard_since(mark);
        }
    }

    /// Whether `v`'s type mentions an open variable an earlier binding owns —
    /// the variables [`Self::arg_check_binds_only_current_vars`] refuses to
    /// let an argument check ground.
    pub(super) fn mentions_inherited_open(&mut self, scope: &Scope, v: TyVid) -> bool {
        let mut roots = HashSet::default();
        collect_var_roots(
            self.solver.tys,
            self.solver.table.resolve(self.solver.tys.var(v)),
            &mut roots,
        );
        roots
            .into_iter()
            .any(|r| self.solver.table.any_older_unioned(r, scope.mark))
    }

    /// A sequence `s1; …; sn` (CE-1), typed as its last statement, which carries
    /// the sequence's mode; the whole sequence is recorded in synth mode, as FCS
    /// keys one node at the full range typed as the last statement.
    ///
    /// Each earlier statement is a **check** position. FCS types it with no
    /// expected type and then *unifies its type with `unit`*: an open type
    /// becomes `unit`, and a ground non-unit one draws a warning and is wrapped
    /// in a synthetic `unit` node at the statement's own range — which is why the
    /// statement's root is never recorded here. The unit relation is not
    /// modelled, so it is dropped: the check-mode poison covers generalisation,
    /// and a statement whose type is not ground once the constraints so far are
    /// [settled](Self::settle) also marks the binding **incomplete**, since FCS's
    /// unification would ground it to `unit` and a later argument check could
    /// otherwise ground it to something else (`let h x = x; mono x` has
    /// `x : unit` in FCS, not `bool`). A condition grounding a parameter slot is
    /// the one grounding incompleteness does not block; it is held to the
    /// parameter's first occurrence instead ([`Self::is_first_occurrence`]),
    /// which a statement naming the parameter already is. A ground statement
    /// type is untouched by the unification, so it costs nothing.
    fn infer_sequential(
        &mut self,
        scope: &mut Scope,
        seq: &SequentialExpr,
        expected: Expected,
    ) -> Option<TyVid> {
        let stmts: Vec<Expr> = seq.statements().collect();
        let Some((last, init)) = stmts.split_last() else {
            scope.mark_incomplete(Incomplete::Recovery);
            return None;
        };
        if init.is_empty() {
            // A one-statement sequence is a recovery artefact, not `e1; e2`.
            scope.mark_incomplete(Incomplete::Recovery);
            return None;
        }
        for stmt in init {
            // FCS checks a statement against a fresh type, and relates it to
            // `unit` afterwards.
            let fresh = Expected::Known(self.solver.table.fresh());
            // A statement that does not synthesize a variable has already marked
            // the binding incomplete in its own arm.
            let recorded = scope.reasons_recorded();
            if let Some(v) = self.infer_expr(scope, stmt, fresh) {
                self.settle(scope);
                if !self
                    .solver
                    .tys
                    .is_ground(self.solver.table.resolve(self.solver.tys.var(v)))
                {
                    scope.mark_consequence(recorded, Incomplete::OpenStatement);
                }
            }
        }
        let v = self.infer_expr(scope, last, expected)?;
        self.emit(self.facts.node_span(seq.syntax()), v, expected);
        Some(v)
    }

    /// Constrain an `if` / `while` condition to `bool`. A condition admits **no**
    /// subsumption — F# requires it to be exactly `bool`, unlike a coercion-
    /// possible `if` branch or function argument — so unifying with `bool` is a
    /// *genuine* equality (not the emission-suppressing check mode). This is the
    /// mechanism that grounds a **simple named function parameter** used directly
    /// as a condition (`let f c = if c then …` ⇒ `c : bool`), feeding that
    /// binder's function type (3.2c-2b).
    ///
    /// It grounds the parameter's **private function-type slot**
    /// ([`BinderEnv::param_slot`]), *not* its binder variable — so the `bool` reaches
    /// only the function's `TyKind::Fun`, never a standalone parameter read-off. It
    /// fires only for a binder that owns such a slot (a simple named parameter of
    /// the function head), so a condition referencing any *other* binder (an
    /// annotated / `rec` / value binder whose type this stage defers) is left
    /// untouched — grounding it would risk `bool` where FCS, on ill-typed input,
    /// keeps that binder's own type. The condition itself records no expression
    /// node.
    ///
    /// **Completeness (Stage 3.2c-2c).** A condition shape this method *fully*
    /// models — a paren-peeled ident that resolves to a slot-owning parameter of
    /// this binding, or a `bool` literal — leaves the binding complete. Anything
    /// else (a compound `x && y`, a member `p.HasValue`, an ident that is not such
    /// a parameter) drops FCS constraints on the condition's sub-terms, so it marks
    /// the binding **incomplete** — otherwise a function whose only openness came
    /// from an unmodelled condition would wrongly generalise.
    fn constrain_bool(&mut self, scope: &mut Scope, cond: Option<Expr>) {
        let Some(cond) = cond else {
            // A missing condition (recovery) is unmodelled.
            scope.mark_incomplete(Incomplete::Recovery);
            return;
        };
        match cond {
            Expr::Ident(ident) => {
                let slot = ident
                    .ident()
                    .and_then(|tok| self.facts.def_at(tok.text_range()))
                    .and_then(|def| self.binders.param_slot(def));
                // A parameter whose annotation mentions an implicitly scoped
                // type variable is reachable through every other mention of
                // it too (`(y: 'a) (x: 'a)`), so no occurrence of its own is
                // provably the first constraint on it. Read off the head, not
                // the table, which says so only once the body has met another
                // mention.
                let shares_typar = ident
                    .ident()
                    .and_then(|tok| self.facts.def_at(tok.text_range()))
                    .is_some_and(|def| scope.typar_params.contains(&def));
                let def = ident
                    .ident()
                    .and_then(|tok| self.facts.def_at(tok.text_range()));
                match slot {
                    Some(_) if shares_typar => {
                        scope.mark_incomplete(Incomplete::ConditionNotFirstOccurrence);
                    }
                    // While the prefix is faithful, the condition is FCS's
                    // equality at this point in its checking order, on the
                    // parameter's one variable: a decision on the binder's
                    // variable, which its uses read, and on the slot with it.
                    // A tainted binder declines it, and the slot-only rule
                    // below applies.
                    Some(slot)
                        if scope.complete
                            && def.is_some_and(|def| {
                                let dv = self.def_var(def);
                                !self.solver.table.touches_taint(self.solver.tys.var(dv))
                            }) =>
                    {
                        let dv = self.def_var(def.expect("checked above"));
                        let bool_ty = self
                            .solver
                            .tys
                            .named(self.facts.env.names(), "System.Boolean");
                        let b = self.solver.table.fresh();
                        self.eq(scope, self.solver.tys.var(b), bool_ty);
                        if self.decide(scope, dv, b) == Decision::Taken {
                            self.eq(scope, self.solver.tys.var(slot), bool_ty);
                        }
                    }
                    Some(slot)
                        if ident
                            .ident()
                            .is_some_and(|tok| self.is_first_occurrence(scope, &tok)) =>
                    {
                        self.eq(
                            scope,
                            self.solver.tys.var(slot),
                            self.solver
                                .tys
                                .named(self.facts.env.names(), "System.Boolean"),
                        )
                    }
                    // A condition on a parameter something earlier may have
                    // fixed: FCS reports the condition, it does not retype.
                    Some(_) => scope.mark_incomplete(Incomplete::ConditionNotFirstOccurrence),
                    // A condition ident that is not a slot-owning parameter of this
                    // binding (a value / annotated / `rec` binder, a cross-file
                    // name) is unmodelled here — its `bool`-ness is an FCS
                    // constraint we drop.
                    None => scope.mark_incomplete(Incomplete::ConditionNotParameter),
                }
            }
            // A literal condition is complete only when it is a `bool` literal
            // (`if true then …`) — already `bool`, no constraint needed. Any other
            // literal in condition position is ill-typed input we do not model.
            Expr::Const(c) => {
                if c.literal().map(|l| l.kind()) != Some(SyntaxKind::BOOL_LIT) {
                    scope.mark_incomplete(Incomplete::ConditionShape);
                }
            }
            Expr::Paren(p) => self.constrain_bool(scope, p.inner()),
            // Any other condition shape (`x && y`, `p.HasValue`, a call) imposes FCS
            // constraints on its sub-terms that we drop.
            _ => scope.mark_incomplete(Incomplete::ConditionShape),
        }
    }

    /// Whether the parameter token `tok` in a condition is the parameter's
    /// **first occurrence** in the current function's body — the rule that lets
    /// a condition ground the parameter's slot ([`Self::constrain_bool`]).
    ///
    /// FCS unifies in source order and reports a later conflict rather than
    /// retyping: in `let f x = (mono x, if x then 1 else 2)` with
    /// `mono : string -> int`, `x` is `string` and the condition is the error.
    /// Our solver is not ordered — the condition's equality is discharged before
    /// any argument check — so a condition grounds soundly only if nothing could
    /// have constrained the parameter before it. A parameter's type is reachable
    /// only through its occurrences (and aliases made from them), so "nothing
    /// before" is "no earlier occurrence". The test is **syntactic**, over the
    /// body's identifier tokens: an occurrence in a subtree the walk skips, or
    /// one the resolver reads some other way, still counts.
    fn is_first_occurrence(&self, scope: &Scope, tok: &SyntaxToken) -> bool {
        let Some(body) = &scope.body else {
            return false;
        };
        let name = ident_text(tok);
        body.descendants_with_tokens()
            .filter_map(|el| el.into_token())
            .find(|t| t.kind() == SyntaxKind::IDENT_TOK && ident_text(t) == name)
            .is_some_and(|first| first.text_range() == tok.text_range())
    }

    /// Record an expression's type variable `v` at `range` for read-off — but
    /// only in *synth* mode (`expected` None), a coercion-free position where the
    /// synthesized type is the elaborated one. In *check* mode the node is
    /// **deferred**: its elaborated type may be a coercion this stage cannot
    /// model yet (no subtype relation), so we say nothing rather than risk a
    /// wrong type (D5), and we add no cross-constraint (which, on an unbound
    /// binder, could otherwise back-flow a coerced expected onto it). The
    /// threaded `expected` type is what subtype-aware checking will later consume
    /// here — emitting the coerced type when the synthesized one is a subtype.
    pub(super) fn emit(&mut self, range: TextRange, v: TyVid, expected: Expected) {
        if expected.records() {
            self.out.node(range, v);
        }
    }
}

/// Whether this `if`/`elif` chain ends in a genuine `else` value branch, so its
/// result type *is* the then-branch's (and may be synthesized in synth mode).
///
/// `elif`/`else if` desugar to a nested [`IfThenElseExpr`] sitting in the outer's
/// else slot, so `else_branch()` alone is misleading: `if a then 1 elif b then 2`
/// has an immediate else-branch (the nested *else-less* `if b then 2`) yet no
/// *final* `else`. Such a chain gets an implicit trailing `else ()`, so its
/// result is `unit`, not the then-branch's type — emitting the latter would
/// disagree with FCS (D5). Only a chain terminating in a non-`if` else branch may
/// be synthesized. Parentheses are transparent: a parenthesized else-less if
/// (`else (if b then 2)`) is likewise `unit`, so we peel them before recursing.
fn if_chain_has_final_else(if_expr: &IfThenElseExpr) -> bool {
    match if_expr.else_branch().and_then(unparenthesize) {
        // No else at all, an `else`-keyword recovery hole, or a parenthesized
        // recovery hole — none is a final value else, so the chain is `unit`.
        None => false,
        // A trailing `elif`/`else if`: recurse — it is final only if *it* is.
        Some(Expr::IfThenElse(nested)) => if_chain_has_final_else(&nested),
        // Any other else expression is a genuine value branch.
        Some(_) => true,
    }
}

/// The member name an identifier token denotes for assembly lookup — its text
/// with surrounding backticks stripped (`` `Foo Bar` `` → `Foo Bar`), matching
/// FCS's `Ident.idText`. Assembly member names carry no backticks, so a
/// backticked source segment must be de-quoted before it is compared against
/// them. A plain identifier passes through unchanged.
/// Whether FCS keys the continuation of the local `let` `binding` somewhere
/// other than its own nodes: a tuple pattern binding no name, over a bare
/// value, moves the continuation's root to the pattern (measured, with every
/// other combination of pattern, RHS and continuation agreeing, by
/// `a_local_pattern_binding_records_nothing_misplaced`).
fn moves_its_continuation(binding: &Binding) -> bool {
    let (Some(pat), Some(rhs)) = (binding.pat(), binding.expr()) else {
        return false;
    };
    let mut peeled = pat.clone();
    while let Pat::Paren(p) = &peeled {
        match p.inner() {
            Some(inner) => peeled = inner,
            None => return false,
        }
    }
    matches!(peeled, Pat::Tuple(_))
        && pat
            .syntax()
            .descendants_where(|k| k == SyntaxKind::NAMED_PAT)
            .next()
            .is_none()
        && matches!(
            unparenthesize(rhs),
            Some(Expr::Ident(_) | Expr::LongIdent(_))
        )
}
