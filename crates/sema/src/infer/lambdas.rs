//! Lambdas: `fun p1 … pn -> body`, checked as FCS checks them.

use super::*;

/// A lambda parameter inference models: a name, an annotated name, `_` or
/// `()`, each under any parentheses. These are the shapes FCS binds directly
/// (`SimplePatOfPat` with no `match`) other than a tuple, which FCS elaborates
/// through a `let` that reshapes the enclosing declaration's typed tree.
#[derive(Debug, Clone, Copy)]
enum LambdaParam {
    Name(DefId),
    Annotated(DefId, Ty),
    Wildcard,
    Unit,
}

impl<'a> Gen<'a> {
    /// A lambda `fun p1 … pn -> body` checked against `expected`, in FCS's
    /// order (`TcIteratedLambdas`): for each parameter, the expected type is
    /// split into a domain and a result ([`Self::function_split`]) and the
    /// parameter is checked against the domain; then the body is checked
    /// against the last result — synthesized where the lambda is. The lambda's
    /// type is the curried function of the domains over the body's result,
    /// and its node is recorded at the whole lambda.
    ///
    /// A parameter outside [`LambdaParam`], or a name bound twice, declines
    /// the lambda, whose body is still walked ([`Self::unmodelled_lambda`]).
    /// An expected type that is not a function type, or a parameter whose
    /// pattern does not fit its domain, declines it too: FCS reports either
    /// and checks nothing further inside the lambda, so the body is not
    /// walked.
    ///
    /// A parameter is a variable of the enclosing binding that FCS never
    /// generalises, so its uses read it as a `match` pattern's names are read
    /// ([`Scope::pattern_locals`]). It is never published: FCS's binder dump
    /// lists a lambda's parameters only where it folds the lambda into a
    /// declaration's own ([`Self::fold_binding_lambdas`]).
    pub(super) fn infer_lambda(
        &mut self,
        scope: &mut Scope,
        fun: &FunExpr,
        expected: Expected,
    ) -> Inferred {
        let args: Vec<Pat> = fun.args().collect();
        let (Some(body), false) = (fun.body(), args.is_empty()) else {
            return Inferred::untyped(self.decline_expected(scope, Incomplete::Recovery));
        };
        // `fun x x -> …` is FS0038, as in a function head.
        let params = if binds_a_name_twice(&args) {
            Err(Incomplete::DuplicateBinder)
        } else {
            args.iter()
                .map(|arg| self.lambda_param(arg))
                .collect::<Result<Vec<_>, _>>()
        };
        let params = match params {
            Ok(params) => params,
            Err(why) => return self.unmodelled_lambda(scope, &args, &body, expected, why),
        };
        // A lambda of n parameters is a chain n + 1 deep, which the tree does
        // not bound: its parameters are siblings. Past the type budget's depth
        // the chain is not built.
        if params.len() >= MAX_TYPE_DEPTH {
            self.solver.table.exceed(TypeBudgetExceeded::Depth);
            return Inferred::untyped(self.decline_expected_propagated(scope));
        }
        let mut rest = expected;
        let mut proof: Option<Discharged> = None;
        let mut domains = Vec::with_capacity(params.len());
        let mut result = None;
        for param in &params {
            let (split, discharged) = self.function_split(scope, rest);
            let discharged = match proof.take() {
                Some(p) => p.and(discharged),
                None => discharged,
            };
            let FunctionSplit::Split {
                domain,
                result: r,
                rest: next,
                fresh,
            } = split
            else {
                let d = self.decline_expected(scope, Incomplete::LambdaNotAFunction);
                return Inferred::untyped(discharged.and(d));
            };
            if !self.bind_lambda_param(scope, *param, domain, fresh) {
                let d = self.decline_expected(scope, Incomplete::LambdaParameterMismatch);
                return Inferred::untyped(discharged.and(d));
            }
            proof = Some(discharged);
            domains.push(domain);
            result = Some(r);
            rest = next;
        }
        let proof = proof.expect("a lambda has a parameter");
        // The body's expected type is of the split's making: the lambda's own
        // relation is discharged by the split, and the body's through it.
        let Some(body_var) = self.infer_expr(scope, &body, rest).var() else {
            return Inferred::untyped(proof.and(self.decline_expected_propagated(scope)));
        };
        let ret = if rest.is_synth() {
            body_var
        } else {
            result.expect("a lambda has a parameter")
        };
        let tys = self.solver.tys;
        let mut fun_ty = tys.var(ret);
        for &d in domains.iter().rev() {
            fun_ty = tys.fun(tys.var(d), fun_ty);
        }
        let lv = self.fresh_equal(scope, fun_ty);
        self.emit(self.facts.node_span(fun.syntax()), lv, expected);
        Inferred::typed(lv, proof)
    }

    /// A lambda with a parameter inference does not model, declined for
    /// `why`: the prefix ends at the lambda, before anything inside it is
    /// decided, and the body is still walked, for what is known there
    /// without a decision (a member of a receiver both know), synthesized
    /// only where the lambda is. Behind a parameter FCS does not bind
    /// directly the body's nodes move ([`is_simple_param`]), so it records
    /// nothing.
    fn unmodelled_lambda(
        &mut self,
        scope: &mut Scope,
        args: &[Pat],
        body: &Expr,
        expected: Expected,
        why: Incomplete,
    ) -> Inferred {
        let d = self.decline_expected(scope, why);
        let body_expected = if expected.is_synth() {
            Expected::Synth
        } else {
            Expected::Unknown
        };
        let body_mark = self.out.mark();
        let _ = self.infer_expr(scope, body, body_expected).var();
        if !args.iter().all(is_simple_param) {
            self.out.discard_since(body_mark);
        }
        Inferred::untyped(d)
    }

    /// Read one lambda parameter ([`LambdaParam`]), or say why it is not
    /// modelled.
    fn lambda_param(&self, arg: &Pat) -> Result<LambdaParam, Incomplete> {
        let shape = self.pattern_shape_in(arg, PatSite::Binding, AnnotationCx::Plain)?;
        Ok(match shape {
            PatShape::Name(def) => LambdaParam::Name(def),
            PatShape::Annotated(def, t) => LambdaParam::Annotated(def, t),
            PatShape::Wildcard => LambdaParam::Wildcard,
            PatShape::Unit => LambdaParam::Unit,
            PatShape::Tuple(_) | PatShape::Const(..) | PatShape::Case(..) => {
                return Err(Incomplete::LambdaParameter(arg.syntax().kind()));
            }
        })
    }

    /// Check the lambda parameter `param` against its `domain` (FCS's
    /// `TcSimplePats`): a name's type is the domain itself; an annotation, or
    /// `()`'s `unit`, is related to the domain where FCS relates it
    /// ([`Self::relate_domain`]), and `false` when that fails, which FCS
    /// reports, abandoning the lambda. An annotated name's type is its
    /// annotation whatever becomes of that relation, as for a function's
    /// parameter.
    fn bind_lambda_param(
        &mut self,
        scope: &mut Scope,
        param: LambdaParam,
        domain: TyVid,
        fresh: bool,
    ) -> bool {
        let tys = self.solver.tys;
        match param {
            LambdaParam::Name(def) => {
                let dv = self.lambda_binder(scope, def);
                self.eq(scope, tys.var(dv), tys.var(domain), Own::var(dv));
                true
            }
            LambdaParam::Annotated(def, t) => {
                let dv = self.lambda_binder(scope, def);
                self.eq(scope, tys.var(dv), t, Own::var(dv));
                self.relate_domain(scope, t, domain, fresh)
            }
            LambdaParam::Wildcard => true,
            LambdaParam::Unit => {
                let unit = tys.named(self.facts.env.names(), UNIT);
                self.relate_domain(scope, unit, domain, fresh)
            }
        }
    }

    /// Relate a parameter's type `t`, which is ground, to its `domain`, as
    /// FCS's equality, `false` when it fails. A `fresh` domain is the
    /// lambda's own variable, which nothing but this relation binds in FCS,
    /// so it is an equality the site owns ([`Self::eq`]), applied even once
    /// the prefix has ended. Any other domain is part of the expected type,
    /// and the relation is a decision ([`Self::decide`]).
    fn relate_domain(&mut self, scope: &mut Scope, t: Ty, domain: TyVid, fresh: bool) -> bool {
        let tys = self.solver.tys;
        if fresh {
            self.eq(scope, tys.var(domain), t, Own::var(domain)) != Equated::Failed
        } else {
            let tv = self.fresh_equal(scope, t);
            self.decide(scope, tv, domain) != Decision::Failed
        }
    }

    /// The variable of the lambda parameter `def`: one of the binding's
    /// monomorphic locals, never published.
    fn lambda_binder(&mut self, scope: &mut Scope, def: DefId) -> TyVid {
        scope.pattern_locals.insert(def);
        self.out.unpublished_local(def);
        self.def_var(def)
    }

    /// Leave ungraded the lambdas FCS folds into a module-level binding's own
    /// parameters: those that are its right-hand side, or a function head's
    /// body, and each that is the body of one so folded, through parentheses.
    /// FCS gives such a binding the arity of all its parameters and keeps no
    /// lambda node for any of them; the body beneath them is checked, and
    /// keeps its nodes, as a function's body is. A paren pattern
    /// (`let (f) = fun …`) folds nothing.
    pub(super) fn fold_binding_lambdas(&mut self, rhs: &Expr) {
        let mut cur = unparenthesize(rhs.clone());
        while let Some(Expr::Fun(fun)) = cur {
            self.out.ungrade(self.facts.node_span(fun.syntax()));
            cur = fun.body().and_then(unparenthesize);
        }
    }
}
