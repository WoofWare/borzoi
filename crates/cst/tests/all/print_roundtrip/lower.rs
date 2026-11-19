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
//! tree it is given. So it may read `(-) x` as the prefix `-x` the currency
//! spells the same way; the printer then writes that tree as what it means,
//! and the round trip is checked on that.
//!
//! Parentheses are dropped everywhere but one place: the tree has none, and
//! the printer adds its own. The exception is an argument, where F#'s checker
//! reads them: `f (a, b)` and `f (x = c)` apply `f` to an argument list, and
//! `f ((a, b))` to one tuple ([`application`]).

use borzoi_print::names::{
    EntityName, EntityPath, ExceptionName, Ident, InfixOperator, LongIdent, Operator, TyparName,
    UnionCaseName, ValueName, VarName,
};
use borzoi_print::tree::{
    Access, AliasPat, AndBang, Args, ArrayRank, AsAlias, Attribute, AttributeArgs, Binding,
    BindingHead, Comp, CompClause, CompItem, Const, Context, DeclRefusal, ExceptionDefn, Expr,
    Float32, Float64, ForDirection, ForSource, ImplFile, LetBang, LetBindings, ListBody, ListComp,
    LocalBindings, MatchClause, ModuleBindings, ModuleBody, ModuleDecl, NamedModule, Namespace,
    NamespaceName, NestedModule, Pat, Range, RecDecls, RecordField, Stmt, StmtExpr, Type, TypeDefn,
    TypeRepr, UnionCase, UnionField, UseBang, UseBinding, UseName,
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
            name: entity_path(long_id)?,
            body: module_body(*is_rec, decls_lossy(decls, tally))?,
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
                    NamedKind::Namespace => NamespaceName::Named(entity_path(long_id)?),
                    NamedKind::GlobalNamespace => NamespaceName::Global,
                    NamedKind::Module => return decline("file shape"),
                };
                namespaces.push(Namespace {
                    name,
                    body: module_body(m.is_rec, decls_lossy(&m.decls, tally))?,
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
                Ok((entity_name(name)?, attributes_of(attributes)?))
            })();
            // The module's declarations count as kept only if it is, and
            // as dropped with it otherwise, its header's refusal included.
            let mut inner = Tally::default();
            let body = decls_lossy(decls, &mut inner);
            let module = header.and_then(|(name, attributes)| {
                Ok(NestedModule {
                    attributes,
                    access: access.map(lower_access),
                    name,
                    body: module_body(*is_rec, body)?,
                })
            });
            match module {
                Ok(m) => {
                    tally.kept += inner.kept;
                    out.push(ModuleDecl::NestedModule(m));
                }
                // Each declaration the module would have kept is lost with it;
                // a module with none to keep or drop is one loss.
                Err(d) => {
                    let lost = if inner.kept == 0 && inner.dropped.is_empty() {
                        1
                    } else {
                        inner.kept
                    };
                    tally.dropped.extend(std::iter::repeat_n(d, lost));
                }
            }
            tally.dropped.extend(inner.dropped);
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
            let group = let_bindings(*is_rec, bindings)?;
            ModuleBindings::new(group)
                .map(ModuleDecl::Let)
                .map_err(|_| Decline("let: a group F# refuses in a module"))
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
            let (name, fields) = case_parts(&exn.case)?;
            let name =
                ExceptionName::new(name).map_err(|_| Decline("name: refused for an exception"))?;
            ExceptionDefn::new(name, fields)
                .map(ModuleDecl::Exception)
                .map_err(refused)
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
    TypeDefn::new(
        attributes_of(&d.attributes)?,
        d.access.map(lower_access),
        entity_name(name)?,
        d.typars.iter().map(typar_decl).collect::<L<_>>()?,
        repr,
    )
    .map_err(refused)
}

/// `decls` as a module's body, recursive if `is_rec`.
fn module_body<V: Version>(is_rec: bool, decls: Vec<ModuleDecl<V>>) -> L<ModuleBody<V>> {
    if !is_rec {
        return Ok(ModuleBody::NonRec(decls));
    }
    RecDecls::new(decls)
        .map(ModuleBody::Rec)
        .map_err(|_| Decline("module rec: declarations out of order, or a mutable"))
}

/// What a declaration constructor's refusal declines.
fn refused(r: DeclRefusal) -> Decline {
    Decline(match r {
        DeclRefusal::DuplicateTypar(_) => "type: a type parameter twice",
        DeclRefusal::UnusedTypar(_) => "type: an abbreviation's unused type parameter",
        DeclRefusal::DuplicateField(_) => "type: a field twice",
        DeclRefusal::DuplicateCase(_) => "type: a union case twice",
        DeclRefusal::CaseNamedTags => "type: a union case named Tags",
        DeclRefusal::FieldNamedAsGenerated(_) => "type: a field named as an unnamed one",
        DeclRefusal::AnonymousType => "type: `_` in a declaration",
        DeclRefusal::CaseNamedAsTester(_) => "type: a union case named as a tester",
        DeclRefusal::UndeclaredTypar(_) => "type: an undeclared type parameter",
        DeclRefusal::DuplicateTester(_) => "type: two union cases with one tester",
    })
}

fn typar_decl(t: &NormalisedTypar) -> L<TyparName> {
    if t.head_type || !t.attributes.is_empty() || !t.intersection_constraints.is_empty() {
        return decline("type parameter attributes or static requirement");
    }
    typar_name(&t.name)
}

fn union_case(c: &NormalisedUnionCase) -> L<UnionCase> {
    let (name, fields) = case_parts(c)?;
    let name = UnionCaseName::new(name).map_err(|_| Decline("name: refused for a union case"))?;
    UnionCase::new(name, fields).map_err(refused)
}

/// A union case's or an exception's name and fields.
fn case_parts(c: &NormalisedUnionCase) -> L<(Ident, Vec<UnionField>)> {
    if !c.attributes.is_empty() {
        return decline("union case attributes");
    }
    let NormalisedUnionCaseKind::Fields(fields) = &c.kind else {
        return decline("union case with a full type");
    };
    Ok((
        ident(&c.ident)?,
        fields
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
    ))
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
    binding_body(b)
}

/// A binding whatever its keyword, which the caller has checked.
fn binding_body<V: Version>(b: &NormalisedBinding) -> L<Binding<V>> {
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
            if is_parenthesised_wildcard(p) {
                // The tree prints `_` bare, which a recursive group admits
                // and `(_)` it refuses (FS3521).
                return decline("pat: a parenthesised `_` binding");
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
                args: match argument_list(&a.arg) {
                    Some(elements) => AttributeArgs::List(args(elements)?),
                    None => AttributeArgs::Value(expr(&a.arg)?),
                },
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
            _ if let N::ComputationExpr(body) = &**arg => Expr::Computation {
                builder: b(func)?,
                body: Box::new(comp(body)?),
            },
            _ => application(func, arg)?,
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
            source: Box::new(for_source(enum_expr)?),
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
            if !elements.is_empty() {
                return decline("expr: list of elements outside a body");
            }
            if *is_array {
                Expr::Array(None)
            } else {
                Expr::List(None)
            }
        }
        N::ArrayOrListComputed { is_array, inner } => {
            let body = Some(Box::new(list_body(inner)?));
            if *is_array {
                Expr::Array(body)
            } else {
                Expr::List(body)
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
            bindings: local_bindings(*is_rec, bindings)?,
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

/// `func` applied to `arg`, read as F#'s checker reads an argument: in
/// parentheses, a tuple's elements are an argument list, and so is a single
/// named argument; anything else, however many parentheses it is in, is one
/// argument passed whole.
///
/// A name or member access in parentheses is refused as the head: the
/// printer writes one bare, as F#'s checker makes a parenthesised method a
/// function value first, and the parse is all the oracle sees of that.
fn application<V: Version>(func: &NormalisedExpr, arg: &NormalisedExpr) -> L<Expr<V>> {
    if let NormalisedExpr::Paren(inner) = func
        && match &**inner {
            NormalisedExpr::Ident(_) | NormalisedExpr::DotGet { .. } => true,
            // `( + )` is a path too, an operator's, which is never bare.
            NormalisedExpr::LongIdent(path) => path.iter().all(|s| Ident::new(s).is_ok()),
            _ => false,
        }
    {
        return decline("expr: application of a parenthesised name");
    }
    if is_parenthesised_unit(arg) {
        // `f ()` and `f (())` call a method with no argument and with `()`;
        // the tree's unit argument is the first.
        return decline("expr: a parenthesised unit argument");
    }
    let func = Box::new(expr(func)?);
    Ok(match argument_list(arg) {
        Some(elements) => Expr::MethodApp {
            func,
            args: args(elements)?,
        },
        None => Expr::App {
            func,
            arg: Box::new(expr(arg)?),
        },
    })
}

/// Whether `arg` is `(())`, `((()))`, ….
fn is_parenthesised_unit(arg: &NormalisedExpr) -> bool {
    let NormalisedExpr::Paren(first) = arg else {
        return false;
    };
    let mut inner: &NormalisedExpr = first;
    while let NormalisedExpr::Paren(next) = inner {
        inner = next;
    }
    matches!(inner, NormalisedExpr::Const(NormalisedConst::Unit))
}

/// The elements of `arg` if F#'s checker reads it as an argument list.
fn argument_list(arg: &NormalisedExpr) -> Option<&[NormalisedExpr]> {
    let NormalisedExpr::Paren(inner) = arg else {
        return None;
    };
    match &**inner {
        NormalisedExpr::Tuple {
            is_struct: false,
            elements,
        } => Some(elements),
        one if named_argument(one).is_some() => Some(std::slice::from_ref(one)),
        _ => None,
    }
}

/// `x = e` with `x` a bare name: in an argument list, the argument named `x`.
fn named_argument(e: &NormalisedExpr) -> Option<(&str, &NormalisedExpr)> {
    use NormalisedExpr as N;
    let N::App {
        is_infix: false,
        bracket_indexer: false,
        func,
        arg: value,
        ..
    } = e
    else {
        return None;
    };
    let N::App {
        is_infix: true,
        bracket_indexer: false,
        func: op,
        arg: lhs,
        ..
    } = &**func
    else {
        return None;
    };
    match (&**op, &**lhs) {
        (N::LongIdent(op), N::Ident(name)) if op.as_slice() == ["="] => Some((name, value)),
        _ => None,
    }
}

/// An argument list's elements as [`Args`].
fn args<V: Version>(elements: &[NormalisedExpr]) -> L<Args<V>> {
    let mut positional = Vec::new();
    let mut named = Vec::new();
    for e in elements {
        match named_argument(e) {
            Some((name, value)) => named.push((ident(name)?, expr(value)?)),
            None if named.is_empty() => positional.push(expr(e)?),
            None => return decline("expr: positional argument after a named one"),
        }
    }
    Ok(match Vec1::from_vec(named) {
        Some(named) => Args::Named { positional, named },
        None => Args::Positional(Vec2::from_vec(positional).ok_or(Decline("short list"))?),
    })
}

/// A computation expression's body. FCS nests a binding over the statements
/// after it, and flattens the rest of a sequence; the tree keeps the block
/// flat, each binding scoping over what follows it. A binding before the end
/// of a sequence scopes over less than the rest of the block, which the tree
/// cannot say.
fn comp<V: Version, K: Context>(e: &NormalisedExpr) -> L<Comp<V, K>> {
    use NormalisedExpr as N;
    let mut init = Vec::new();
    let mut e = e;
    loop {
        match e {
            N::Sequential(items) => {
                let (last, before) = items.split_last().ok_or(Decline("empty sequential"))?;
                for item in before {
                    if let N::LetOrUse { .. } = item {
                        return decline("comp: binding scoped short of the block");
                    }
                    init.push(CompItem::Stmt(stmt(item)?));
                }
                e = last;
            }
            N::LetOrUse {
                is_rec,
                bindings,
                body,
            } => {
                init.push(comp_binding(*is_rec, bindings)?);
                e = body;
            }
            other => {
                return Ok(Comp {
                    init,
                    last: stmt(other)?,
                });
            }
        }
    }
}

/// A `let` group in an expression or a computation expression.
fn local_bindings<V: Version>(is_rec: bool, bindings: &[NormalisedBinding]) -> L<LocalBindings<V>> {
    LocalBindings::new(let_bindings(is_rec, bindings)?)
        .map_err(|_| Decline("local binding with access or attributes"))
}

/// A list's or array's body: a whole range, a literal's elements, or a
/// comprehension. F# reads a body as elements exactly when each of its
/// statements is simple ([`is_list_element`]).
fn list_body<V: Version>(e: &NormalisedExpr) -> L<ListBody<V>> {
    let items = match e {
        NormalisedExpr::IndexRange { .. } => return Ok(ListBody::Range(range(e)?)),
        NormalisedExpr::Sequential(items) => items.as_slice(),
        other => std::slice::from_ref(other),
    };
    if items.iter().all(is_list_element) {
        let elements = items.iter().map(expr).collect::<L<Vec<_>>>()?;
        return Ok(ListBody::Elements(
            Vec1::from_vec(elements).ok_or(Decline("list: no elements"))?,
        ));
    }
    Ok(ListBody::Comp(ListComp::new(comp(e)?).map_err(|_| {
        Decline("list: a literal with an `if` before implicit yields")
    })?))
}

/// Whether F# reads `e`, a list body's statement, as a literal's element
/// (FCS's `IsSimpleSemicolonSequenceElement` from F# 4.7, which accepts no
/// `if`).
fn is_list_element(e: &NormalisedExpr) -> bool {
    use NormalisedExpr as N;
    !matches!(
        e,
        N::IfThenElse { .. }
            | N::TryWith { .. }
            | N::Match { .. }
            | N::For { .. }
            | N::ForEach { .. }
            | N::TryFinally { .. }
            | N::YieldOrReturn { .. }
            | N::LetOrUse { .. }
            | N::Do(_)
            | N::MatchBang { .. }
            | N::While { .. }
            | N::WhileBang { .. }
    )
}

/// `K`'s gate for a builder's own statements, or a decline.
fn bang<K: Context>() -> L<K::Bang> {
    K::Bang::WITNESS.ok_or(Decline("comp: builder statement in a list"))
}

/// What a `use` or `use!` binds, where `G` gates the discard.
fn use_name<G: Gate>(b: &NormalisedBinding) -> L<UseName<G>> {
    use NormalisedPat as P;
    if !b.attributes.is_empty() || b.is_mutable || b.is_inline || b.access.is_some() {
        return decline("comp: use binding with modifiers");
    }
    let mut p = &b.pat;
    while let P::Paren(inner) = p {
        p = inner;
    }
    Ok(match p {
        P::Wildcard => {
            UseName::Discard(G::WITNESS.ok_or(Decline("comp: use discard before its version"))?)
        }
        P::Named(name) => UseName::Named(value_name(name)?),
        P::LongIdent {
            head,
            typars,
            args: NormalisedArgPats::Pats(args),
        } if typars.is_empty() && args.is_empty() => match head.as_slice() {
            [name] => UseName::Named(value_name(name)?),
            _ => return decline("comp: use binding of a dotted name"),
        },
        _ => return decline("comp: use binding of a pattern"),
    })
}

/// A computation expression's binding group.
fn comp_binding<V: Version, Ctx: Context>(
    is_rec: bool,
    bindings: &[NormalisedBinding],
) -> L<CompItem<V, Ctx>> {
    use NormalisedLeadingKeyword as K;
    let [first, others @ ..] = bindings else {
        return decline("comp: binding group without bindings");
    };
    if first.self_id.is_some() {
        return decline("comp: binding self identifier");
    }
    Ok(match first.leading_keyword {
        K::Let | K::LetRec => CompItem::Let(local_bindings(is_rec, bindings)?),
        K::Use if !is_rec && others.is_empty() => CompItem::Use(UseBinding {
            name: use_name(first)?,
            value: expr(&first.expr)?,
        }),
        K::UseBang if !is_rec && others.is_empty() => CompItem::UseBang(UseBang {
            gate: bang::<Ctx>()?,
            name: use_name(first)?,
            value: expr(&first.expr)?,
        }),
        K::LetBang => {
            let simple = |b: &NormalisedBinding| {
                b.attributes.is_empty()
                    && !b.is_mutable
                    && !b.is_inline
                    && b.access.is_none()
                    && b.self_id.is_none()
            };
            if is_rec || !bindings.iter().all(simple) {
                return decline("comp: bang binding with modifiers");
            }
            let ands = others
                .iter()
                .map(|b| {
                    if b.leading_keyword != K::AndBang {
                        return decline("comp: bang group keyword");
                    }
                    Ok(AndBang {
                        gate: V::AndBang::WITNESS
                            .ok_or(Decline("comp: and! before its version"))?,
                        pat: pat(&b.pat)?,
                        value: expr(&b.expr)?,
                    })
                })
                .collect::<L<Vec<_>>>()?;
            CompItem::LetBang(LetBang {
                gate: bang::<Ctx>()?,
                pat: pat(&first.pat)?,
                value: expr(&first.expr)?,
                ands,
            })
        }
        _ => return decline("comp: binding keyword"),
    })
}

/// A computation expression's statement. A parenthesised one is an
/// expression, which `K` may refuse ([`StmtExpr`]).
fn stmt<V: Version, K: Context>(e: &NormalisedExpr) -> L<Stmt<V, K>> {
    use NormalisedExpr as N;
    let c = |e: &NormalisedExpr| comp(e).map(Box::new);
    Ok(match e {
        N::YieldOrReturn { flags, from, inner } => {
            let inner = expr(inner)?;
            match (flags, from) {
                ((true, false), false) => Stmt::Yield(inner),
                ((true, false), true) => Stmt::YieldFrom(inner),
                ((false, true), false) => Stmt::Return {
                    gate: bang::<K>()?,
                    expr: inner,
                },
                ((false, true), true) => Stmt::ReturnFrom {
                    gate: bang::<K>()?,
                    expr: inner,
                },
                _ => return decline("comp: yield or return flags"),
            }
        }
        N::DoBang(e) => Stmt::DoBang {
            gate: bang::<K>()?,
            expr: expr(e)?,
        },
        N::IfThenElse {
            condition,
            then_branch,
            else_branch,
        } => Stmt::IfThenElse {
            cond: expr(condition)?,
            then_branch: c(then_branch)?,
            else_branch: else_branch.as_deref().map(c).transpose()?,
        },
        N::Match { scrutinee, clauses } => Stmt::Match {
            scrutinee: expr(scrutinee)?,
            clauses: vec1(clauses, comp_clause)?,
        },
        N::MatchBang { scrutinee, clauses } => Stmt::MatchBang {
            gate: bang::<K>()?,
            scrutinee: expr(scrutinee)?,
            clauses: vec1(clauses, comp_clause)?,
        },
        N::While { cond, body } => Stmt::While {
            cond: expr(cond)?,
            body: c(body)?,
        },
        N::WhileBang { cond, body } => Stmt::WhileBang {
            gate: V::WhileBang::WITNESS.ok_or(Decline("comp: while! before its version"))?,
            bang: bang::<K>()?,
            cond: expr(cond)?,
            body: c(body)?,
        },
        N::For {
            ident: var,
            from,
            ascending,
            to,
            body,
        } => Stmt::For {
            var: ident(var)?,
            from: expr(from)?,
            direction: if *ascending {
                ForDirection::To
            } else {
                ForDirection::Downto
            },
            to: expr(to)?,
            body: c(body)?,
        },
        N::ForEach {
            pat: p,
            enum_expr,
            body,
        } => Stmt::ForEach {
            pat: pat(p)?,
            source: for_source(enum_expr)?,
            body: c(body)?,
        },
        N::IndexRange { .. } => return decline("comp: range as a statement"),
        N::TryWith { body, clauses } => Stmt::TryWith {
            gate: K::TryWith::<V>::WITNESS
                .ok_or(Decline("comp: try/with in a list before its version"))?,
            body: c(body)?,
            clauses: vec1(clauses, comp_clause)?,
        },
        N::TryFinally { body, finally } => Stmt::TryFinally {
            body: c(body)?,
            finally: expr(finally)?,
        },
        N::LetOrUse { .. } | N::Sequential(_) => {
            return decline("comp: block where a statement belongs");
        }
        other => Stmt::Expr(
            StmtExpr::new(expr(other)?)
                .map_err(|_| Decline("comp: statement-shaped expression in parentheses"))?,
        ),
    })
}

fn for_source<V: Version>(e: &NormalisedExpr) -> L<ForSource<V>> {
    Ok(match e {
        NormalisedExpr::IndexRange { .. } => ForSource::Range(range(e)?),
        other => ForSource::Expr(expr(other)?),
    })
}

/// `a .. b`, or `a .. s .. b`, which FCS nests as `(a .. s) .. b` with no
/// parentheses. A range missing a bound is a slice's, not this.
fn range<V: Version>(e: &NormalisedExpr) -> L<Range<V>> {
    let NormalisedExpr::IndexRange {
        lower: Some(lower),
        upper: Some(upper),
    } = e
    else {
        return decline("expr: index range without both bounds");
    };
    let to = expr(upper)?;
    Ok(match &**lower {
        NormalisedExpr::IndexRange {
            lower: Some(from),
            upper: Some(step),
        } => Range {
            from: expr(from)?,
            step: Some(expr(step)?),
            to,
        },
        from => Range {
            from: expr(from)?,
            step: None,
            to,
        },
    })
}

fn comp_clause<V: Version, K: Context>(cl: &NormalisedMatchClause) -> L<CompClause<V, K>> {
    Ok(CompClause {
        pat: pat(&cl.pat)?,
        guard: cl.when.as_deref().map(expr).transpose()?,
        body: comp(&cl.result)?,
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

fn pat<V: Version>(p: &NormalisedPat) -> L<Pat<V>> {
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
        P::As { lhs, rhs } => {
            if is_parenthesised_type_test(lhs) {
                // `(:? t) as x` binds `x` at the matched type, `:? t as x` at
                // `t`; the tree's type test under `as` is the second.
                return decline("pat: a parenthesised type test under `as`");
            }
            Pat::As {
                pat: b(lhs)?,
                alias: as_alias(rhs)?,
            }
        }
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

/// Whether `p` is `(_)`, `((_))`, ….
fn is_parenthesised_wildcard(p: &NormalisedPat) -> bool {
    let NormalisedPat::Paren(first) = p else {
        return false;
    };
    let mut inner: &NormalisedPat = first;
    while let NormalisedPat::Paren(next) = inner {
        inner = next;
    }
    matches!(inner, NormalisedPat::Wildcard)
}

/// Whether `p` is `(:? t)`, `((:? t))`, ….
fn is_parenthesised_type_test(p: &NormalisedPat) -> bool {
    let NormalisedPat::Paren(first) = p else {
        return false;
    };
    let mut inner: &NormalisedPat = first;
    while let NormalisedPat::Paren(next) = inner {
        inner = next;
    }
    matches!(inner, NormalisedPat::IsInst { .. })
}

/// What follows `as`: a variable, or from F# 6 another pattern.
fn as_alias<V: Version>(p: &NormalisedPat) -> L<AsAlias<V>> {
    let gate = V::NonVariablePatternsToRightOfAsPatterns::WITNESS;
    if gate.is_none() && matches!(p, NormalisedPat::Paren(_)) {
        // Before F# 6, `p as (x)` is a pattern after `as`, which only F# 6
        // admits; `p as x` is the variable.
        return decline("pat: a pattern after `as` before F# 6");
    }
    let p = pat(p)?;
    if let Pat::Name(path) = &p
        && let [only] = path.segments()
        && let Ok(v) = VarName::new(only.clone())
    {
        return Ok(AsAlias::Var(v));
    }
    let Some(gate) = gate else {
        return decline("pat: a pattern after `as` before F# 6");
    };
    let alias = AliasPat::new(gate, p).expect("not a variable, which returned above");
    Ok(AsAlias::Pat(alias))
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

fn entity_name(s: &str) -> L<EntityName> {
    EntityName::new(ident(s)?).map_err(|_| Decline("name: refused for a type, module or case"))
}

fn entity_path(path: &[String]) -> L<EntityPath> {
    let names = path.iter().map(|s| entity_name(s)).collect::<L<Vec<_>>>()?;
    Vec1::from_vec(names)
        .map(EntityPath)
        .ok_or(Decline("name: empty path"))
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
