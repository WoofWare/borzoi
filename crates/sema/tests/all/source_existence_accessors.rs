//! The typed accessors `source_existence` leaves unread, pinned with their
//! reasons.
//!
//! Each leaf's classifier accounts for every child of its node
//! (`source_existence::consumed`), but a child it accounts for without
//! reading is still a claim that the child cannot move the surface. Under
//! `accessor-trace` the walk is run over the grid, the generator's pinned
//! seeds, every form's witness and the placement grid, and for every node
//! type it read any accessor of, each accessor of that type it never called
//! must be listed in [`UNREAD`] with the reason it cannot change the entity
//! surface. A new accessor the grammar grows on a node the walk reads, or a
//! reason for an accessor the walk now calls, fails here.

use std::collections::{BTreeMap, BTreeSet};

use borzoi_cst::syntax::accessor_trace;
use borzoi_sema::{Form, MarkerRoutes};

use crate::source_existence_diff::{Cell, ours_with};

/// Every accessor of a node type the walk reads that it does not call, with
/// why that cannot change the entity surface.
const UNREAD: &[(&str, &str)] = &[
    (
        "ExceptionDefnDecl::members",
        "an exception's members declare no entity; its extension members are A's ExtensionNames'",
    ),
    (
        "LongIdent::active_pat_names",
        "an active pattern's name is an ACTIVE_PAT_NAME node, which `long_ident`'s consumption \
         check names as no child, so a long identifier holding one declines",
    ),
    (
        "ModuleOrNamespace::is_anon",
        "`kind()` is read, and its `Anon` arm is the same fact",
    ),
    (
        "ObjectModelRepr::is_class",
        "a type's kind beyond abbreviation is a constant (`Channel::EntityKind`)",
    ),
    (
        "ObjectModelRepr::is_interface",
        "a type's kind beyond abbreviation is a constant (`Channel::EntityKind`)",
    ),
    (
        "ObjectModelRepr::is_struct",
        "a type's kind beyond abbreviation is a constant (`Channel::EntityKind`)",
    ),
    (
        "ObjectModelRepr::members",
        "members declare no entity; extension members are A's ExtensionNames'",
    ),
    (
        "TyparDecls::constraint_clause",
        "a constraint declares no entity",
    ),
    (
        "TyparDecls::form",
        "whether type parameters are written before or after the name moves no path; \
         only whether any is written is read (`typars`)",
    ),
    ("TypeDefn::constraints", "a constraint declares no entity"),
    (
        "UnionCase::attributes",
        "an exception's attributes are `ExceptionDefnDecl::attributes`'; an attribute on its \
         case moves no entity fact (an exception lends nothing and keeps its written name), \
         and an `assembly:` one is read by the raw scan wherever it sits",
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
        "a case named by an operator has no `ident()`, and the exception declines",
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
    cells.extend((0..60).map(crate::source_existence_gen::cell));
    cells.extend(
        Form::ALL
            .iter()
            .map(|f| Cell::new(format!("witness_{f:?}"), &[("Lib.fs", f.witness())])),
    );
    cells.extend(crate::source_existence_placement::grid(&[""]));
    cells
}

#[test]
fn every_accessor_the_walk_leaves_unread_has_a_reason() {
    let mut called: BTreeSet<&'static str> = BTreeSet::new();
    for cell in producers() {
        for routes in [None, Some(MarkerRoutes::Unknown)] {
            ours_with(&cell, routes.as_ref(), |walk| {
                let (read, accessors) = accessor_trace::record(walk);
                called.extend(accessors);
                read
            });
        }
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
