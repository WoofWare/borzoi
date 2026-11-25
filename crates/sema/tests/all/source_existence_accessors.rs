//! The typed accessors `source_existence` leaves unread, pinned with their
//! reasons.
//!
//! Each leaf's classifier accounts for every child of its node
//! (`source_existence::consumed`), but a child it accounts for without
//! reading is still a claim that the child cannot move the surface. Under
//! `accessor-trace` the walk is run over the grid, the generator's pinned
//! seeds and every form's witness, and for every node type it read any
//! accessor of, each accessor of that type it never called must be listed
//! in [`UNREAD`] with the reason it cannot change the entity surface. A new
//! accessor the grammar grows on a node the walk reads, or a reason for an
//! accessor the walk now calls, fails here.

use std::collections::{BTreeMap, BTreeSet};

use borzoi_cst::syntax::accessor_trace;
use borzoi_sema::{Budget, CompileItem, Form, Producer, source_existence};

use crate::source_existence_diff::{Cell, project_files};

/// Every accessor of a node type the walk reads that it does not call, with
/// why that cannot change the entity surface.
const UNREAD: &[(&str, &str)] = &[
    (
        "Attribute::arg",
        "an attribute decides no entity fact the walk reads: one on an entity, standing alone \
         or with a target declines by where it sits, and any other decides nothing",
    ),
    (
        "Attribute::type_name",
        "an attribute is classified by its carrier and target, never by what it names",
    ),
    (
        "ExceptionDefnDecl::attributes",
        "every attribute list is classified by its carrier in the file-wide scan, which \
         declines one on an exception",
    ),
    (
        "ExceptionDefnDecl::members",
        "an exception's members declare no entity",
    ),
    (
        "LongIdent::active_pat_names",
        "an active pattern's name is an ACTIVE_PAT_NAME node, which `long_ident`'s consumption \
         check names as no child, so a long identifier holding one is unreadable",
    ),
    (
        "ModuleOrNamespace::attributes",
        "every attribute list is classified by its carrier in the file-wide scan, which \
         declines one on a module header",
    ),
    (
        "ModuleOrNamespace::is_anon",
        "`kind()` is read, and its `Anon` arm is the same fact",
    ),
    (
        "ModuleOrNamespace::is_rec",
        "`rec` orders FCS's checking of the same declarations and moves no entity path",
    ),
    (
        "ModuleOrNamespace::sig_decls",
        "the walk reads implementation files only; a signature file declines",
    ),
    (
        "NestedModuleDecl::attributes",
        "every attribute list is classified by its carrier in the file-wide scan, which \
         declines one on a nested module",
    ),
    (
        "NestedModuleDecl::is_rec",
        "`rec` orders FCS's checking of the same declarations and moves no entity path",
    ),
    (
        "NestedModuleDecl::sig_decls",
        "the walk reads implementation files only; a signature file declines",
    ),
    (
        "ObjectModelRepr::is_class",
        "a type's kind beyond abbreviation is a constant no entity question reads",
    ),
    (
        "ObjectModelRepr::is_interface",
        "a type's kind beyond abbreviation is a constant no entity question reads",
    ),
    (
        "ObjectModelRepr::is_struct",
        "a type's kind beyond abbreviation is a constant no entity question reads",
    ),
    ("ObjectModelRepr::members", "members declare no entity"),
    (
        "TyparDecls::constraint_clause",
        "a constraint declares no entity",
    ),
    (
        "TyparDecls::form",
        "whether type parameters are written before or after the name moves no path; only \
         whether any is written is read (`typars`)",
    ),
    (
        "TypeDefn::attributes",
        "every attribute list is classified by its carrier in the file-wide scan, which \
         declines one on a type",
    ),
    ("TypeDefn::constraints", "a constraint declares no entity"),
    ("TypeDefn::members", "members declare no entity"),
    (
        "UnionCase::attributes",
        "every attribute list is classified by its carrier in the file-wide scan, which \
         declines one on an exception's case as the exception's",
    ),
    (
        "UnionCase::fields",
        "an exception's fields declare no entity",
    ),
    (
        "UnionCase::full_type",
        "an exception's type declares no entity",
    ),
    (
        "UnionCase::operator_name",
        "a case named by an operator has no `ident()`, and the exception is unreadable",
    ),
];

/// Every accessor `borzoi-cst`'s typed AST declares, by node type: each
/// public accessor opens with `accessor!("Type::method")`.
fn declared() -> BTreeMap<String, BTreeSet<String>> {
    let src = include_str!("../../../cst/src/syntax/union.rs");
    let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for chunk in src.split("accessor!(\"").skip(1) {
        let Some(end) = chunk.find("\")") else {
            continue;
        };
        if let Some((ty, method)) = chunk[..end].split_once("::") {
            out.entry(ty.to_owned())
                .or_default()
                .insert(method.to_owned());
        }
    }
    out
}

/// The producers the walk is traced over, all FCS-free.
fn producers() -> Vec<Cell> {
    let mut cells = crate::source_existence_grid::cells();
    cells.extend((0..90).map(|s| crate::source_existence_gen::case(s).cell));
    cells.extend(
        Form::ALL
            .iter()
            .map(|f| match f.witness().split_once("//--\n") {
                Some((sig, imp)) => Cell::new(
                    format!("witness_{f:?}"),
                    &[("Lib.fsi", sig), ("Lib.fs", imp)],
                ),
                None => Cell::new(format!("witness_{f:?}"), &[("Lib.fs", f.witness())]),
            }),
    );
    cells
}

#[test]
fn every_accessor_the_walk_leaves_unread_has_a_reason() {
    let mut called: BTreeSet<&'static str> = BTreeSet::new();
    for cell in producers() {
        let project = project_files(&cell);
        let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
        let (_, accessors) = accessor_trace::record(|| {
            source_existence(
                Producer {
                    items: &items,
                    providers: cell.providers,
                },
                Budget::DEFAULT,
            )
        });
        called.extend(accessors);
    }
    let declared = declared();
    let visited: BTreeSet<&str> = called
        .iter()
        .filter_map(|a| a.split_once("::").map(|(t, _)| t))
        .collect();
    let mut unread: BTreeSet<String> = BTreeSet::new();
    for ty in &visited {
        for method in declared.get(*ty).into_iter().flatten() {
            let accessor = format!("{ty}::{method}");
            if !called.contains(accessor.as_str()) {
                unread.insert(accessor);
            }
        }
    }
    let reasoned: BTreeSet<String> = UNREAD.iter().map(|(a, _)| (*a).to_owned()).collect();
    let missing: Vec<&String> = unread.difference(&reasoned).collect();
    let stale: Vec<&String> = reasoned.difference(&unread).collect();
    assert!(
        missing.is_empty() && stale.is_empty(),
        "accessors the walk leaves unread with no reason: {missing:#?}\n\
         reasons for accessors it reads, or of a type it no longer reads: {stale:#?}\n\
         visited types: {visited:?}"
    );
}
