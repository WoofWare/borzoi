//! Reading a normalised AST back as a `borzoi_print` tree.
//!
//! This is the oracle's inverse of the printer: what the printed text parses to
//! (in the currency FCS and our parser are compared in) must lower to the tree
//! that was printed. It is also how the corpus sweep gets realistic trees to
//! print, by lowering each corpus file and dropping the declarations that use
//! something the tree does not model.
//!
//! Lowering a *source* file need not preserve its meaning, only produce some
//! tree: the property under test is about the printer, which round-trips the
//! tree it is given. So it may read `M(x = 1)` as an application to a `bool`,
//! or `(-) x` as the prefix `-x` the currency spells the same way; the printer
//! then writes that tree as what it means, and the round trip is checked on
//! that.
//!
//! Parentheses are dropped everywhere: the tree has none, and the printer adds
//! its own.

use borzoi_print::names::{Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName};
use borzoi_print::tree::{
    Access, ArrayRank, Attribute, Binding, BindingHead, Const, Expr, Float32, Float64,
    ForDirection, ImplFile, LetBindings, MatchClause, ModuleDecl, NamedModule, Namespace,
    NamespaceName, NestedModule, Pat, RecordField, Type, TypeDefn, TypeRepr, UnionCase, UnionField,
};
use borzoi_print::vec::{Vec1, Vec2};
use borzoi_print::version::{Gate, Version};

use crate::common::normalised_ast::{
    NamedKind, NormalisedAccess, NormalisedArgPats, NormalisedAttribute, NormalisedBinding,
    NormalisedConst, NormalisedDecl, NormalisedExpr, NormalisedLeadingKeyword,
    NormalisedMatchClause, NormalisedModule, NormalisedModuleKind, NormalisedOpenTarget,
    NormalisedPat, NormalisedRecordDeclItem, NormalisedRecordItem, NormalisedRoot,
    NormalisedTupleSegment, NormalisedTypar, NormalisedType, NormalisedTypeDefn,
    NormalisedTypeRepr, NormalisedUnionCase, NormalisedUnionCaseKind, fun_body_scaffold,
};

/// Why something has no tree: the construct the tree does not model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Decline(pub &'static str);

type L<T> = Result<T, Decline>;

fn decline<T>(what: &'static str) -> L<T> {
    Err(Decline(what))
}

/// What lowering a file kept and dropped.
#[derive(Debug, Default)]
pub struct Tally {
    /// Declarations lowered, nested modules' own declarations counted instead
    /// of the module.
    pub kept: usize,
    /// Why each dropped declaration was dropped.
    pub dropped: Vec<Decline>,
}

/// `root` as a tree, dropping every declaration that does not lower.
pub fn lower_file_lossy<V: Version>(root: &NormalisedRoot) -> L<(ImplFile<V>, Tally)> {
    let mut tally = Tally::default();
    let file = file(root, &mut tally)?;
    Ok((file, tally))
}

/// `root` as a tree, or why some part of it has none.
pub fn lower_file_strict<V: Version>(root: &NormalisedRoot) -> L<ImplFile<V>> {
    let mut tally = Tally::default();
    let file = file(root, &mut tally)?;
    match tally.dropped.first() {
        Some(&d) => Err(d),
        None => Ok(file),
    }
}

fn file<V: Version>(root: &NormalisedRoot, tally: &mut Tally) -> L<ImplFile<V>> {
    let NormalisedRoot::Impl(f) = root else {
        return decline("signature file");
    };
    match f.modules.as_slice() {
        [
            NormalisedModule {
                kind: NormalisedModuleKind::Anon,
                is_rec: false,
                attributes,
                access: None,
                decls,
            },
        ] if attributes.is_empty() => Ok(ImplFile::AnonModule(decls_lossy(decls, tally))),
        [
            NormalisedModule {
                kind:
                    NormalisedModuleKind::Named {
                        long_id,
                        kind: NamedKind::Module,
                    },
                is_rec,
                attributes,
                access,
                decls,
            },
        ] => Ok(ImplFile::NamedModule(NamedModule {
            attributes: attributes_of(attributes)?,
            access: access.map(lower_access),
            is_rec: *is_rec,
            name: long_ident(long_id)?,
            decls: decls_lossy(decls, tally),
        })),
        modules => {
            let mut namespaces = Vec::new();
            for m in modules {
                let NormalisedModuleKind::Named { long_id, kind } = &m.kind else {
                    return decline("file shape");
                };
                if !m.attributes.is_empty() || m.access.is_some() {
                    return decline("namespace attributes or access");
                }
                let name = match kind {
                    NamedKind::Namespace => NamespaceName::Named(long_ident(long_id)?),
                    NamedKind::GlobalNamespace => NamespaceName::Global,
                    NamedKind::Module => return decline("file shape"),
                };
                namespaces.push(Namespace {
                    is_rec: m.is_rec,
                    name,
                    decls: decls_lossy(&m.decls, tally),
                });
            }
            Vec1::from_vec(namespaces)
                .map(ImplFile::Namespaces)
                .ok_or(Decline("file shape"))
        }
    }
}

fn decls_lossy<V: Version>(decls: &[NormalisedDecl], tally: &mut Tally) -> Vec<ModuleDecl<V>> {
    let mut out = Vec::new();
    for d in decls {
        if let NormalisedDecl::NestedModule {
            long_id,
            is_rec,
            attributes,
            access,
            decls,
        } = d
        {
            let header = (|| {
                let [name] = long_id.as_slice() else {
                    return decline("dotted nested module name");
                };
                Ok((ident(name)?, attributes_of(attributes)?))
            })();
            match header {
                Ok((name, attributes)) => out.push(ModuleDecl::NestedModule(NestedModule {
                    attributes,
                    access: access.map(lower_access),
                    is_rec: *is_rec,
                    name,
                    decls: decls_lossy(decls, tally),
                })),
                Err(d) => tally.dropped.push(d),
            }
            continue;
        }
        match decl(d) {
            Ok(d) => {
                tally.kept += 1;
                out.push(d);
            }
            Err(d) => tally.dropped.push(d),
        }
    }
    out
}

fn decl<V: Version>(d: &NormalisedDecl) -> L<ModuleDecl<V>> {
    match d {
        NormalisedDecl::Expr(e) => Ok(ModuleDecl::Expr(expr(e)?)),
        NormalisedDecl::Let { is_rec, bindings } => {
            Ok(ModuleDecl::Let(let_bindings(*is_rec, bindings)?))
        }
        NormalisedDecl::Open {
            target: NormalisedOpenTarget::ModuleOrNamespace(path),
        } => Ok(ModuleDecl::Open(long_ident(path)?)),
        NormalisedDecl::Open {
            target: NormalisedOpenTarget::Type(_),
        } => decline("open type"),
        NormalisedDecl::NestedModule { .. } => unreachable!("handled by decls_lossy"),
        NormalisedDecl::ModuleAbbrev {
            ident: name,
            long_id,
        } => Ok(ModuleDecl::ModuleAbbrev {
            name: ident(name)?,
            target: long_ident(long_id)?,
        }),
        NormalisedDecl::Types(defns) => Ok(ModuleDecl::Types(vec1(defns, type_defn)?)),
        NormalisedDecl::Exception(exn) => {
            if !exn.attributes.is_empty()
                || exn.access.is_some()
                || exn.abbrev.is_some()
                || !exn.members.is_empty()
            {
                return decline("exception attributes, access, abbreviation or members");
            }
            Ok(ModuleDecl::Exception(union_case(&exn.case)?))
        }
        NormalisedDecl::Attributes(_) => decline("standalone attributes"),
        NormalisedDecl::HashDirective { .. } => decline("hash directive"),
    }
}

fn type_defn<V: Version>(d: &NormalisedTypeDefn) -> L<TypeDefn<V>> {
    if d.head_type.is_some() || !d.constraints.is_empty() || d.implicit_ctor.is_some() {
        return decline("type head, constraints or constructor");
    }
    if !d.members.is_empty() {
        return decline("type members");
    }
    let [name] = d.long_id.as_slice() else {
        return decline("dotted type name");
    };
    let repr = match &d.repr {
        NormalisedTypeRepr::Abbrev(t) => TypeRepr::Abbrev(ty(t)?),
        NormalisedTypeRepr::Record {
            access: None,
            fields,
        } => TypeRepr::Record(vec1(fields, |f| match f {
            NormalisedRecordDeclItem::Field(f)
                if f.attributes.is_empty() && f.access.is_none() && !f.is_static =>
            {
                let Some(name) = &f.name else {
                    return decline("unnamed record field");
                };
                Ok(RecordField {
                    is_mutable: f.is_mutable,
                    name: ident(name)?,
                    ty: ty(&f.ty)?,
                })
            }
            _ => decline("record field attributes, access, static or spread"),
        })?),
        NormalisedTypeRepr::Union {
            access: None,
            cases,
        } => TypeRepr::Union(vec1(cases, union_case)?),
        NormalisedTypeRepr::Record { .. } | NormalisedTypeRepr::Union { .. } => {
            return decline("representation access");
        }
        NormalisedTypeRepr::None => return decline("type without representation"),
        NormalisedTypeRepr::Enum(_) => return decline("enum type"),
        NormalisedTypeRepr::ObjectModel { .. } => return decline("class, struct or interface"),
        NormalisedTypeRepr::Delegate(_) => return decline("delegate type"),
    };
    Ok(TypeDefn {
        attributes: attributes_of(&d.attributes)?,
        access: d.access.map(lower_access),
        name: ident(name)?,
        typars: d.typars.iter().map(typar_decl).collect::<L<_>>()?,
        repr,
    })
}

fn typar_decl(t: &NormalisedTypar) -> L<TyparName> {
    if t.head_type || !t.attributes.is_empty() || !t.intersection_constraints.is_empty() {
        return decline("type parameter attributes or static requirement");
    }
    typar_name(&t.name)
}

fn union_case(c: &NormalisedUnionCase) -> L<UnionCase> {
    if !c.attributes.is_empty() {
        return decline("union case attributes");
    }
    let NormalisedUnionCaseKind::Fields(fields) = &c.kind else {
        return decline("union case with a full type");
    };
    Ok(UnionCase {
        name: ident(&c.ident)?,
        fields: fields
            .iter()
            .map(|f| {
                if !f.attributes.is_empty() || f.access.is_some() || f.is_mutable || f.is_static {
                    return decline("union field attributes or modifiers");
                }
                Ok(UnionField {
                    name: f.name.as_deref().map(ident).transpose()?,
                    ty: ty(&f.ty)?,
                })
            })
            .collect::<L<_>>()?,
    })
}

fn let_bindings<V: Version>(is_rec: bool, bindings: &[NormalisedBinding]) -> L<LetBindings<V>> {
    if is_rec {
        Ok(LetBindings::Rec(vec1(bindings, binding)?))
    } else {
        match bindings {
            [b] => Ok(LetBindings::NonRec(Box::new(binding(b)?))),
            _ => decline("non-recursive let … and"),
        }
    }
}

fn binding<V: Version>(b: &NormalisedBinding) -> L<Binding<V>> {
    use NormalisedLeadingKeyword as K;
    if !matches!(b.leading_keyword, K::Let | K::LetRec | K::And) {
        return decline("binding keyword other than let/and");
    }
    if b.self_id.is_some() {
        return decline("binding self identifier");
    }
    let access = b.access.map(lower_access);
    let head = match &b.pat {
        NormalisedPat::Named(name) => BindingHead::Name {
            is_mutable: b.is_mutable,
            access,
            name: value_name(name)?,
        },
        NormalisedPat::LongIdent {
            head,
            typars,
            args: NormalisedArgPats::Pats(params),
        } if typars.is_empty() => {
            let [name] = head.as_slice() else {
                return decline("dotted binding name");
            };
            let name = value_name(name)?;
            match Vec1::from_vec(params.iter().map(pat).collect::<L<Vec<_>>>()?) {
                None => BindingHead::Name {
                    is_mutable: b.is_mutable,
                    access,
                    name,
                },
                Some(params) => {
                    if b.is_mutable {
                        return decline("mutable function");
                    }
                    BindingHead::Function {
                        access,
                        name,
                        params,
                    }
                }
            }
        }
        p => {
            if b.is_mutable || access.is_some() {
                return decline("mutable or access on a pattern binding");
            }
            BindingHead::Pattern(pat(p)?)
        }
    };
    Ok(Binding {
        attributes: attributes_of(&b.attributes)?,
        is_inline: b.is_inline,
        head,
        body: expr(&b.expr)?,
    })
}

fn attributes_of<V: Version>(lists: &[Vec<NormalisedAttribute>]) -> L<Vec<Attribute<V>>> {
    lists
        .iter()
        .flatten()
        .map(|a| {
            if a.target.is_some() {
                return decline("attribute target");
            }
            Ok(Attribute {
                name: long_ident(&a.type_name)?,
                arg: expr(&a.arg)?,
            })
        })
        .collect()
}

fn lower_access(a: NormalisedAccess) -> Access {
    match a {
        NormalisedAccess::Public => Access::Public,
        NormalisedAccess::Internal => Access::Internal,
        NormalisedAccess::Private => Access::Private,
    }
}

fn expr<V: Version>(e: &NormalisedExpr) -> L<Expr<V>> {
    use NormalisedExpr as N;
    let b = |e: &NormalisedExpr| expr(e).map(Box::new);
    Ok(match e {
        // `( * )` cannot be an operator token, as `(*` opens a comment, so FCS
        // parses it as a parenthesised `*` wildcard and its checker reads that
        // as the operator (`CheckExpressions.fs`, `TcExprUndelayed`).
        N::Paren(inner)
            if matches!(
                &**inner,
                N::IndexRange {
                    lower: None,
                    upper: None
                }
            ) =>
        {
            Expr::OpValue(Operator::new("*").expect("an operator"))
        }
        N::Paren(inner) => return expr(inner),
        N::Const(c) => Expr::Const(constant(c)?),
        N::Null => Expr::Null,
        N::Ident(name) => Expr::Name(LongIdent::single(ident(name)?)),
        N::LongIdent(path) => match path.as_slice() {
            [single] if Ident::new(single).is_err() => {
                Expr::OpValue(Operator::new(single).map_err(|_| Decline("operator name"))?)
            }
            _ => Expr::Name(long_ident(path)?),
        },
        N::Tuple {
            is_struct: false,
            elements,
        } => Expr::Tuple(vec2(elements, expr)?),
        N::App {
            is_infix: false,
            bracket_indexer: false,
            func,
            arg,
            ..
        } => match &**func {
            N::App {
                is_infix: true,
                bracket_indexer: false,
                func: op,
                arg: lhs,
                ..
            } => {
                let N::LongIdent(op) = &**op else {
                    return decline("infix application of a non-operator");
                };
                let [op] = op.as_slice() else {
                    return decline("qualified infix operator");
                };
                let op = Operator::new(op)
                    .ok()
                    .and_then(InfixOperator::new)
                    .ok_or(Decline("infix operator name"))?;
                Expr::Infix {
                    op,
                    lhs: b(lhs)?,
                    rhs: b(arg)?,
                }
            }
            _ => Expr::App {
                func: b(func)?,
                arg: b(arg)?,
            },
        },
        N::App {
            is_infix: true,
            bracket_indexer: false,
            func,
            arg,
            ..
        } => match (&**func, &**arg) {
            (
                N::LongIdent(op),
                N::Tuple {
                    is_struct: false,
                    elements,
                },
            ) if op.as_slice() == ["::"] => match elements.as_slice() {
                [head, tail] => Expr::Cons {
                    head: b(head)?,
                    tail: b(tail)?,
                },
                _ => return decline("cons arity"),
            },
            _ => return decline("partial infix application"),
        },
        N::DotGet {
            expr: e,
            long_dot_id,
        } => {
            let mut acc = expr(e)?;
            for field in long_dot_id {
                acc = Expr::FieldGet {
                    expr: Box::new(acc),
                    field: ident(field)?,
                };
            }
            acc
        }
        N::IfThenElse {
            condition,
            then_branch,
            else_branch,
        } => Expr::IfThenElse {
            cond: b(condition)?,
            then_branch: b(then_branch)?,
            else_branch: else_branch.as_deref().map(b).transpose()?,
        },
        N::Sequential(items) => {
            // The currency flattens `a; b; c`; the tree nests to the right, as
            // F# does. A nested sequence the source parenthesised stays nested.
            let mut items = items.iter().rev();
            let mut acc = expr(items.next().ok_or(Decline("empty sequential"))?)?;
            let mut any = false;
            for item in items {
                any = true;
                acc = Expr::Sequential(b(item)?, Box::new(acc));
            }
            if !any {
                return decline("one-element sequential");
            }
            acc
        }
        N::Lambda { args, body } => Expr::Lambda {
            params: vec1(args, pat)?,
            body: Box::new(expr(lambda_body(args, body)?)?),
        },
        N::Match { scrutinee, clauses } => Expr::Match {
            scrutinee: b(scrutinee)?,
            clauses: vec1(clauses, match_clause)?,
        },
        N::MatchLambda { clauses } => Expr::Function(vec1(clauses, match_clause)?),
        N::While { cond, body } => Expr::While {
            cond: b(cond)?,
            body: b(body)?,
        },
        N::For {
            ident: var,
            from,
            ascending,
            to,
            body,
        } => Expr::For {
            var: ident(var)?,
            from: b(from)?,
            direction: if *ascending {
                ForDirection::To
            } else {
                ForDirection::Downto
            },
            to: b(to)?,
            body: b(body)?,
        },
        N::ForEach {
            pat: p,
            enum_expr,
            body,
        } => Expr::ForEach {
            pat: pat(p)?,
            source: b(enum_expr)?,
            body: b(body)?,
        },
        N::TryWith { body, clauses } => Expr::TryWith {
            body: b(body)?,
            clauses: vec1(clauses, match_clause)?,
        },
        N::TryFinally { body, finally } => Expr::TryFinally {
            body: b(body)?,
            finally: b(finally)?,
        },
        N::Record {
            inherit_info: None,
            copy,
            fields,
        } => Expr::Record {
            copy: copy.as_deref().map(b).transpose()?,
            fields: vec1(fields, |f| match f {
                NormalisedRecordItem::Field(f) => {
                    let Some(value) = &f.value else {
                        return decline("record field without a value");
                    };
                    Ok((long_ident(&f.name)?, expr(value)?))
                }
                NormalisedRecordItem::Spread(_) => decline("record spread"),
            })?,
        },
        N::ArrayOrList { is_array, elements } => {
            let items = elements.iter().map(expr).collect::<L<Vec<_>>>()?;
            if *is_array {
                Expr::Array(items)
            } else {
                Expr::List(items)
            }
        }
        N::ArrayOrListComputed { is_array, inner } => {
            let items = match &**inner {
                N::Sequential(items) => items.iter().map(expr).collect::<L<Vec<_>>>()?,
                one => vec![expr(one)?],
            };
            if *is_array {
                Expr::Array(items)
            } else {
                Expr::List(items)
            }
        }
        N::Typed { expr: e, ty: t } => Expr::Typed {
            expr: b(e)?,
            ty: ty(t)?,
        },
        N::TypeTest { expr: e, ty: t } => Expr::TypeTest {
            expr: b(e)?,
            ty: ty(t)?,
        },
        N::Upcast { expr: e, ty: t } => Expr::Upcast {
            expr: b(e)?,
            ty: ty(t)?,
        },
        N::Downcast { expr: e, ty: t } => Expr::Downcast {
            expr: b(e)?,
            ty: ty(t)?,
        },
        N::LetOrUse {
            is_rec,
            bindings,
            body,
        } => Expr::LetIn {
            bindings: let_bindings(*is_rec, bindings)?,
            body: b(body)?,
        },
        N::LongIdentSet { long_dot_id, value } => Expr::Set {
            target: long_ident(long_dot_id)?,
            value: b(value)?,
        },
        N::Lazy { expr: e } => Expr::Lazy(b(e)?),
        N::Assert { expr: e } => Expr::Assert(b(e)?),
        N::Do(e) => Expr::Do(b(e)?),
        N::DotLambda { expr: body } => {
            let path = match &**body {
                N::Ident(name) => LongIdent::single(ident(name)?),
                N::LongIdent(path) => long_ident(path)?,
                _ => return decline("expr: dot lambda of a non-path"),
            };
            Expr::DotLambda {
                gate: V::AccessorFunctionShorthand::WITNESS
                    .ok_or(Decline("expr: dot lambda before its version"))?,
                path,
            }
        }
        other => return decline(expr_kind(other)),
    })
}

/// The body a lambda was written with, under the `match` scaffold FCS's parser
/// wraps it in for each parameter that is not a simple pattern. The scaffold is
/// built by the normaliser's own [`fun_body_scaffold`] around a placeholder no
/// clean parse holds, and peeled off in step with it.
fn lambda_body<'a>(args: &[NormalisedPat], body: &'a NormalisedExpr) -> L<&'a NormalisedExpr> {
    fn peel<'a>(scaffold: &NormalisedExpr, body: &'a NormalisedExpr) -> L<&'a NormalisedExpr> {
        match (scaffold, body) {
            (NormalisedExpr::Error, _) => Ok(body),
            (
                NormalisedExpr::Match {
                    scrutinee: s,
                    clauses: sc,
                },
                NormalisedExpr::Match {
                    scrutinee: b,
                    clauses: bc,
                },
            ) if s == b => match (sc.as_slice(), bc.as_slice()) {
                ([sc], [bc]) if sc.pat == bc.pat && sc.when.is_none() && bc.when.is_none() => {
                    peel(&sc.result, &bc.result)
                }
                _ => decline("lambda scaffold mismatch"),
            },
            _ => decline("lambda scaffold mismatch"),
        }
    }
    peel(&fun_body_scaffold(args, NormalisedExpr::Error), body)
}

/// The name of an expression the tree does not model, for the decline census.
fn expr_kind(e: &NormalisedExpr) -> &'static str {
    use NormalisedExpr as N;
    match e {
        N::Typar(_) => "expr: typar",
        N::Tuple { .. } => "expr: struct tuple",
        N::App { .. } => "expr: indexer application",
        N::Dynamic { .. } => "expr: dynamic",
        N::DotIndexedGet { .. } => "expr: dot indexed get",
        N::IndexRange { .. } => "expr: index range",
        N::IndexFromEnd { .. } => "expr: index from end",
        N::AddressOf { .. } => "expr: address of",
        N::New { .. } => "expr: new",
        N::ObjExpr { .. } => "expr: object expression",
        N::InferredUpcast { .. } => "expr: upcast",
        N::InferredDowncast { .. } => "expr: downcast",
        N::Fixed { .. } => "expr: fixed",
        N::TypeApp { .. } => "expr: type application",
        N::InterpolatedString { .. } => "expr: interpolated string",
        N::MatchBang { .. } => "expr: match!",
        N::WhileBang { .. } => "expr: while!",
        N::Quote { .. } => "expr: quotation",
        N::ComputationExpr(_) => "expr: computation expression",
        N::Record { .. } => "expr: record inherit",
        N::AnonRecd { .. } => "expr: anonymous record",
        N::YieldOrReturn { .. } => "expr: yield or return",
        N::DoBang(_) => "expr: do!",
        N::JoinIn { .. } => "expr: join in",
        N::Set { .. } => "expr: set",
        N::NamedIndexedPropertySet { .. } => "expr: named indexed property set",
        N::DotIndexedSet { .. } => "expr: dot indexed set",
        N::DotSet { .. } => "expr: dot set",
        N::DotNamedIndexedPropertySet { .. } => "expr: dot named indexed property set",
        N::TraitCall { .. } => "expr: trait call",
        N::InlineIl { .. } => "expr: inline IL",
        N::StaticOptimization { .. } => "expr: static optimization",
        N::LibraryOnlyUnionCaseFieldGet { .. } | N::LibraryOnlyUnionCaseFieldSet { .. } => {
            "expr: library-only"
        }
        N::Error | N::FromParseError(_) | N::DiscardAfterMissingQualificationAfterDot(_) => {
            "expr: error"
        }
        _ => "expr: other",
    }
}

fn match_clause<V: Version>(c: &NormalisedMatchClause) -> L<MatchClause<V>> {
    Ok(MatchClause {
        pat: pat(&c.pat)?,
        guard: c.when.as_deref().map(expr).transpose()?,
        result: expr(&c.result)?,
    })
}

fn pat(p: &NormalisedPat) -> L<Pat> {
    use NormalisedPat as P;
    let b = |p: &NormalisedPat| pat(p).map(Box::new);
    Ok(match p {
        P::Paren(inner) => return pat(inner),
        P::Wildcard => Pat::Wildcard,
        P::Named(name) => Pat::Name(LongIdent::single(ident(name)?)),
        P::LongIdent {
            head,
            typars,
            args: NormalisedArgPats::Pats(args),
        } if typars.is_empty() => {
            let name = long_ident(head)?;
            match Vec1::from_vec(args.iter().map(pat).collect::<L<Vec<_>>>()?) {
                None => Pat::Name(name),
                Some(args) => Pat::Ctor { name, args },
            }
        }
        P::LongIdent { .. } => return decline("pat: named arguments or type parameters"),
        P::Const(c) => Pat::Const(constant(c)?),
        P::Null => Pat::Null,
        P::Typed { pat: p, ty: t } => Pat::Typed {
            pat: b(p)?,
            ty: ty(t)?,
        },
        P::Tuple {
            is_struct: false,
            elements,
        } => Pat::Tuple(vec2(elements, pat)?),
        P::Tuple { .. } => return decline("pat: struct tuple"),
        P::As { lhs, rhs } => Pat::As {
            pat: b(lhs)?,
            alias: b(rhs)?,
        },
        P::ArrayOrList { is_array, elements } => {
            let items = elements.iter().map(pat).collect::<L<Vec<_>>>()?;
            if *is_array {
                Pat::Array(items)
            } else {
                Pat::List(items)
            }
        }
        P::Record { fields } => {
            Pat::Record(vec1(fields, |(name, p)| Ok((long_ident(name)?, pat(p)?)))?)
        }
        P::IsInst { ty: t } => Pat::IsInst(ty(t)?),
        P::ListCons { lhs, rhs } => Pat::Cons {
            head: b(lhs)?,
            tail: b(rhs)?,
        },
        P::Ands { pats } => Pat::Ands(vec2(pats, pat)?),
        P::Or { lhs, rhs } => Pat::Or(b(lhs)?, b(rhs)?),
        P::Attrib { .. } => return decline("pat: attributes"),
        P::OptionalVal(_) => return decline("pat: optional"),
        P::QuoteExpr(_) => return decline("pat: quotation"),
        P::FromParseError(_) => return decline("pat: error"),
    })
}

fn ty(t: &NormalisedType) -> L<Type> {
    use NormalisedType as T;
    let b = |t: &NormalisedType| ty(t).map(Box::new);
    Ok(match t {
        T::Paren(inner) => return ty(inner),
        T::LongIdent(path) => Type::Name(long_ident(path)?),
        T::Anon => Type::Anon,
        T::Var {
            name,
            head_type: false,
        } => Type::Var(typar_name(name)?),
        T::Fun { arg, ret } => Type::Fun {
            arg: b(arg)?,
            ret: b(ret)?,
        },
        T::Tuple {
            is_struct: false,
            path,
        } => {
            let mut items = Vec::new();
            for (i, seg) in path.iter().enumerate() {
                match (i % 2, seg) {
                    (0, NormalisedTupleSegment::Type(t)) => items.push(ty(t)?),
                    (1, NormalisedTupleSegment::Star) => {}
                    _ => return decline("type: measure tuple"),
                }
            }
            Type::Tuple(Vec2::from_vec(items).ok_or(Decline("type: tuple arity"))?)
        }
        T::App {
            type_name,
            type_args,
            ..
        } => {
            let T::LongIdent(head) = &**type_name else {
                return decline("type: application of a non-name");
            };
            Type::App {
                head: long_ident(head)?,
                args: vec1(type_args, ty)?,
            }
        }
        T::Array { rank, element_type } => Type::Array {
            rank: u8::try_from(*rank)
                .ok()
                .and_then(ArrayRank::new)
                .ok_or(Decline("type: array rank"))?,
            elem: b(element_type)?,
        },
        _ => return decline("type: other"),
    })
}

fn constant(c: &NormalisedConst) -> L<Const> {
    use NormalisedConst as C;
    Ok(match c {
        C::Unit => Const::Unit,
        C::Bool(v) => Const::Bool(*v),
        C::SByte(v) => Const::SByte(*v),
        C::Byte(v) => Const::Byte(*v),
        C::Int16(v) => Const::Int16(*v),
        C::UInt16(v) => Const::UInt16(*v),
        C::Int32(v) => Const::Int32(*v),
        C::UInt32(v) => Const::UInt32(*v),
        C::Int64(v) => Const::Int64(*v),
        C::UInt64(v) => Const::UInt64(*v),
        C::IntPtr(v) => Const::NativeInt(*v),
        C::UIntPtr(v) => Const::UNativeInt(*v),
        C::Single(bits) => Const::Single(Float32(*bits)),
        C::Double(bits) => Const::Double(Float64(*bits)),
        C::Char(v) => Const::Char(*v),
        // The string's kind (verbatim, triple-quoted) is only how it was
        // spelled.
        C::String { value, .. } => Const::String(
            String::from_utf16(value).map_err(|_| Decline("const: lone surrogate in string"))?,
        ),
        C::Bytes { .. } => return decline("const: byte string"),
        C::Decimal(_) => return decline("const: decimal"),
        C::UserNum { .. } => return decline("const: user numeric literal"),
        C::SourceIdentifier { .. } => return decline("const: source identifier"),
        C::Measure { .. } => return decline("const: unit of measure"),
    })
}

fn ident(s: &str) -> L<Ident> {
    Ident::new(s).map_err(|_| Decline("name: not an identifier"))
}

fn long_ident(path: &[String]) -> L<LongIdent> {
    let idents = path.iter().map(|s| ident(s)).collect::<L<Vec<_>>>()?;
    Vec1::from_vec(idents)
        .map(LongIdent)
        .ok_or(Decline("name: empty path"))
}

fn value_name(s: &str) -> L<ValueName> {
    match Ident::new(s) {
        Ok(id) => Ok(ValueName::Ident(id)),
        Err(_) => Operator::new(s)
            .map(ValueName::Operator)
            .map_err(|_| Decline("name: neither identifier nor operator")),
    }
}

fn typar_name(s: &str) -> L<TyparName> {
    TyparName::new(s).map_err(|_| Decline("name: type variable"))
}

fn vec1<A, B>(items: &[A], f: impl Fn(&A) -> L<B>) -> L<Vec1<B>> {
    Vec1::from_vec(items.iter().map(f).collect::<L<Vec<_>>>()?).ok_or(Decline("empty list"))
}

fn vec2<A, B>(items: &[A], f: impl Fn(&A) -> L<B>) -> L<Vec2<B>> {
    Vec2::from_vec(items.iter().map(f).collect::<L<Vec<_>>>()?).ok_or(Decline("short list"))
}
