//! The existence index ([`borzoi_assembly::existence`]) held to two
//! independent readers of the same assembly, row for row.
//!
//! - Its `TypeDef` layer against `System.Reflection.Metadata`'s walk of the
//!   same table: every row, at every visibility, with its `AutoOpen` and
//!   `Extension` markers and whether some attribute's owner is unreadable.
//! - Its pickle layer against FCS's view of the assembly
//!   (`FSharpAssembly.Contents`), which reads the same pickle: every
//!   non-namespace entity, at every accessibility, by kind. FCS reads a
//!   referenced assembly's `internal` as `private`, so accessibility is
//!   compared as public or not. FCS lists no namespace as an entity, so the
//!   index's namespace fragments are not compared.
//!
//! Both comparisons are exact multisets: a row either side lacks is a
//! failure, whichever side lacks it. An F# assembly whose pickle the index
//! cannot read fails too, for the assemblies here, whose pickles are all
//! sound.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use borzoi_assembly::{
    Ecma335Assembly, EcmaView, ExistenceIndex, IndexLayer, PickleLayer, PickledEntityKind,
};

use crate::common::assembly_entities::{
    AssemblyEntities, ExtensionStyle, FcsAccess, invoke_fcs_dump_assembly_entities,
};
use crate::common::{
    ensure_abbrev_fixture_built, ensure_active_pattern_fixture_built,
    ensure_attribute_alias_fixture_built, ensure_autoopen_fixture_built,
    ensure_existence_fixture_built, ensure_ext_universe_fixture_built, ensure_fsharp_core_dll,
    ensure_measure_fixture_built, ensure_memberref_attr_dll_built,
    ensure_module_value_fixture_built, ensure_rqa_union_fixture_built, ensure_system_runtime_dll,
    ensure_union_case_autoopen_fixture_built, temp_fs_file,
};

/// One comparable line per `TypeDef` row of `index`.
fn il_ours(index: &ExistenceIndex) -> Vec<String> {
    index
        .il
        .iter()
        .map(|r| {
            format!(
                "{} | {} | {} | {:?} | auto_open={} extension={} unreadable={}",
                r.namespace.join("."),
                r.enclosing.join("+"),
                r.name,
                r.visibility,
                r.auto_open,
                r.extension,
                r.unreadable_attribute
            )
        })
        .collect()
}

fn il_theirs(entities: &AssemblyEntities) -> Vec<String> {
    entities
        .il
        .rows
        .iter()
        .map(|r| {
            format!(
                "{} | {} | {} | {:?} | auto_open={} extension={} unreadable={}",
                r.namespace,
                r.enclosing.join("+"),
                r.name,
                r.visibility,
                r.auto_open,
                r.extension,
                r.unreadable_attribute
            )
        })
        .collect()
}

/// One comparable line per non-namespace pickled entity of `index`, or
/// `None` when the index holds no pickle layer.
fn pickle_ours(index: &ExistenceIndex) -> Result<Option<Vec<String>>, String> {
    match &index.pickle {
        PickleLayer::NotFSharp => Ok(None),
        PickleLayer::Unreadable(reason) => Err(reason.clone()),
        PickleLayer::Read(rows) => Ok(Some(
            rows.iter()
                .filter(|r| r.kind != PickledEntityKind::Namespace)
                .map(|r| {
                    format!(
                        "{} | {} | {} ({}) | {:?} | public={} auto_open={} extension={}",
                        r.namespace.join("."),
                        r.enclosing.join("+"),
                        r.logical_name,
                        r.compiled_name,
                        r.kind,
                        r.public,
                        r.auto_open,
                        r.extension
                    )
                })
                .collect(),
        )),
    }
}

fn pickle_theirs(entities: &AssemblyEntities) -> Vec<String> {
    entities
        .fcs
        .entities
        .iter()
        .map(|e| {
            format!(
                "{} | {} | {} ({}) | {:?} | public={} auto_open={} extension={}",
                e.namespace,
                e.enclosing.join("+"),
                e.logical_name,
                e.compiled_name,
                e.kind,
                e.access == FcsAccess::Public,
                e.auto_open,
                e.extension
            )
        })
        .collect()
}

/// The `TypeDef` layer's extension methods of `index`, one line per
/// (namespace, declaring type chain, method name).
fn il_extensions_ours(index: &ExistenceIndex) -> BTreeSet<String> {
    index
        .extensions
        .iter()
        .filter(|r| r.layer == IndexLayer::TypeDef)
        .flat_map(|r| {
            r.names.iter().map(move |name| {
                format!(
                    "{} | {} | {name}",
                    r.namespace.join("."),
                    r.enclosing.join("+")
                )
            })
        })
        .collect()
}

fn il_extensions_theirs(entities: &AssemblyEntities) -> BTreeSet<String> {
    entities
        .il
        .extension_methods
        .iter()
        .map(|m| format!("{} | {} | {}", m.namespace, m.enclosing.join("+"), m.name))
        .collect()
}

/// One extension row's names and instance-ness.
type RowNames<'a> = (&'a [String], Option<bool>);

/// Every disagreement between the pickle layer's extension rows of `index`
/// and FCS's extension members, both ways: each member FCS reads must be a
/// row of the index at its place answering to its logical and compiled
/// names (and, for an F# extension, of its instance-ness), and each row must
/// answer to a member FCS reads there (when `every_row_read`: FCS's
/// `MembersFunctionsAndValues` lists no class `let`, whose val the pickle
/// holds, so a project read from source with a marked one has rows FCS's view
/// lacks).
pub(crate) fn pickle_extension_failures(
    index: &ExistenceIndex,
    members: &[crate::common::assembly_entities::FcsExtensionMember],
    every_row_read: bool,
) -> Vec<String> {
    let place = |ns: &str, enclosing: &[String]| format!("{ns} | {}", enclosing.join("+"));
    let mut ours: BTreeMap<String, Vec<RowNames<'_>>> = BTreeMap::new();
    for row in index
        .extensions
        .iter()
        .filter(|r| r.layer == IndexLayer::Pickle)
    {
        ours.entry(place(&row.namespace.join("."), &row.enclosing))
            .or_default()
            .push((&row.names, row.instance));
    }
    let mut failures = Vec::new();
    for m in members {
        let at = place(&m.namespace, &m.enclosing);
        // FCS's view reads a property as marked when any one of its
        // accessors is, and then lists every accessor; the pickle marks only
        // the accessor that carries the attribute. Where every row need not be
        // read (a project from source), a marked sibling accessor stands for
        // an accessor FCS lists under its property.
        let property = (!every_row_read && m.style == ExtensionStyle::Csharp)
            .then(|| {
                ["get_", "set_"]
                    .iter()
                    .find_map(|p| m.logical_name.strip_prefix(p))
            })
            .flatten();
        let found = ours.get(&at).is_some_and(|rows| {
            rows.iter().any(|(names, instance)| {
                (names.contains(&m.logical_name)
                    && names.contains(&m.compiled_name)
                    && (m.style != ExtensionStyle::Fsharp || *instance == Some(m.is_instance)))
                    || property.is_some_and(|p| names.iter().any(|n| n == p))
            })
        });
        if !found {
            failures.push(format!(
                "  FCS reads {:?} extension {} ({}, instance {}) at {at}; the index has no such row",
                m.style, m.logical_name, m.compiled_name, m.is_instance
            ));
        }
    }
    let mut theirs: BTreeMap<String, BTreeSet<&str>> = BTreeMap::new();
    for m in members {
        let names = theirs.entry(place(&m.namespace, &m.enclosing)).or_default();
        names.insert(&m.logical_name);
        names.insert(&m.compiled_name);
    }
    for (at, rows) in ours.iter().filter(|_| every_row_read) {
        for (names, _) in rows {
            let read = theirs
                .get(at)
                .is_some_and(|fcs| names.iter().any(|n| fcs.contains(n.as_str())));
            if !read {
                failures.push(format!(
                    "  the index lists extension {names:?} at {at}; FCS reads none of them there"
                ));
            }
        }
    }
    failures.truncate(20);
    failures
}

/// The lines one side has more often than the other, each with how many
/// more, at most `limit` of them.
fn excess(ours: &[String], theirs: &[String], limit: usize) -> Vec<String> {
    let mut count: BTreeMap<&str, i64> = BTreeMap::new();
    for l in ours {
        *count.entry(l).or_default() += 1;
    }
    for l in theirs {
        *count.entry(l).or_default() -= 1;
    }
    count
        .into_iter()
        .filter(|(_, n)| *n != 0)
        .take(limit)
        .map(|(l, n)| {
            if n > 0 {
                format!("  only ours (x{n}): {l}")
            } else {
                format!("  only the oracle's (x{}): {l}", -n)
            }
        })
        .collect()
}

/// Every disagreement between the index of each of `graded` and the oracle,
/// and how many rows of each layer were compared. `support` is referenced
/// too, ungraded: the assemblies whose types `graded` reads (an attribute's
/// type from another package), without which FCS reads less of it.
fn compare(graded: &[PathBuf], support: &[PathBuf]) -> (Vec<String>, usize, usize, usize) {
    let anchor = temp_fs_file(
        "assembly_entities_diff_anchor",
        "module Anchor\nlet x = 1\n",
    );
    let refs: Vec<&Path> = graded.iter().chain(support).map(PathBuf::as_path).collect();
    let canonical = |p: &Path| std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let graded_files: Vec<PathBuf> = graded.iter().map(|p| canonical(p)).collect();
    let report = invoke_fcs_dump_assembly_entities(&anchor, &refs);
    let _ = std::fs::remove_file(&anchor);
    let mut failures = Vec::new();
    let (mut il_rows, mut pickle_rows, mut extension_rows) = (0, 0, 0);
    for entities in &report.assemblies {
        let file = &entities.file;
        if !graded_files.contains(&canonical(Path::new(file))) {
            continue;
        }
        let bytes = std::fs::read(file).expect("read the assembly");
        let index = Ecma335Assembly::parse(&bytes)
            .and_then(|a| a.existence_index())
            .unwrap_or_else(|e| panic!("{file}: {e}"));
        if let Some(error) = &entities.il.error {
            failures.push(format!("{file}: the IL oracle failed: {error}"));
            continue;
        }
        let (ours, theirs) = (il_ours(&index), il_theirs(entities));
        il_rows += theirs.len();
        let moved = excess(&ours, &theirs, 20);
        if !moved.is_empty() {
            failures.push(format!(
                "{file}: the TypeDef layer differs\n{}",
                moved.join("\n")
            ));
        }
        let (ours_ext, theirs_ext) = (il_extensions_ours(&index), il_extensions_theirs(entities));
        extension_rows += theirs_ext.len();
        let moved: Vec<String> = ours_ext
            .symmetric_difference(&theirs_ext)
            .take(20)
            .map(|l| {
                let side = if ours_ext.contains(l) {
                    "ours"
                } else {
                    "the oracle's"
                };
                format!("  only {side}: {l}")
            })
            .collect();
        if !moved.is_empty() {
            failures.push(format!(
                "{file}: the TypeDef layer's extension methods differ\n{}",
                moved.join("\n")
            ));
        }
        match pickle_ours(&index) {
            Ok(None) => {}
            Err(reason) => failures.push(format!("{file}: the pickle is unreadable: {reason}")),
            Ok(Some(ours)) => {
                if !entities.fcs.seen || entities.fcs.error.is_some() {
                    failures.push(format!(
                        "{file}: FCS did not read the assembly: {:?}",
                        entities.fcs.error
                    ));
                    continue;
                }
                if !entities.fcs.read_errors.is_empty() {
                    failures.push(format!(
                        "{file}: FCS could not read some entities: {:?}",
                        entities.fcs.read_errors
                    ));
                }
                let theirs = pickle_theirs(entities);
                pickle_rows += theirs.len();
                extension_rows += entities.fcs.extension_members.len();
                let moved =
                    pickle_extension_failures(&index, &entities.fcs.extension_members, true);
                if !moved.is_empty() {
                    failures.push(format!(
                        "{file}: the pickle layer's extension members differ\n{}",
                        moved.join("\n")
                    ));
                }
                let moved = excess(&ours, &theirs, 20);
                if !moved.is_empty() {
                    failures.push(format!(
                        "{file}: the pickle layer differs\n{}",
                        moved.join("\n")
                    ));
                }
            }
        }
    }
    (failures, il_rows, pickle_rows, extension_rows)
}

/// The reference pack, FSharp.Core and the F# fixtures: the pickles hold
/// every kind of entity at every accessibility, and the reference pack every
/// shape of `TypeDef` the compilers write. `MemberRefAttr.dll` adds an
/// attribute constructor no compiler here writes, a `MemberRef` on a local
/// `TypeDef`.
#[test]
fn the_existence_index_is_what_both_readers_report() {
    let ref_dir = ensure_system_runtime_dll()
        .parent()
        .expect("the reference pack's directory")
        .to_path_buf();
    let mut dlls: Vec<PathBuf> = std::fs::read_dir(&ref_dir)
        .expect("list the reference pack")
        .map(|e| e.expect("a directory entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "dll"))
        .collect();
    dlls.sort();
    dlls.push(ensure_fsharp_core_dll());
    for fixture in [
        ensure_existence_fixture_built(),
        ensure_abbrev_fixture_built(),
        ensure_autoopen_fixture_built(),
        ensure_attribute_alias_fixture_built(),
        ensure_active_pattern_fixture_built(),
        ensure_measure_fixture_built(),
        ensure_module_value_fixture_built(),
        ensure_ext_universe_fixture_built(),
        ensure_union_case_autoopen_fixture_built(),
        ensure_rqa_union_fixture_built(),
        ensure_memberref_attr_dll_built(),
    ] {
        dlls.push(fixture.to_path_buf());
    }
    let (failures, il_rows, pickle_rows, extension_rows) = compare(&dlls, &[]);
    eprintln!(
        "{} assemblies: {il_rows} TypeDef rows, {pickle_rows} pickled entities and \
         {extension_rows} extension members compared",
        dlls.len()
    );
    assert!(
        extension_rows > 300,
        "only {extension_rows} extension members compared"
    );
    assert!(il_rows > 5_000, "only {il_rows} TypeDef rows compared");
    assert!(
        pickle_rows > 400,
        "only {pickle_rows} pickled entities compared"
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every `.dll` under `BORZOI_EXISTENCE_SWEEP_ROOT` (a NuGet cache, say),
/// each graded on its own, an F# one with the cache's copy of each assembly
/// it references (outside the reference pack) beside it. A root that cannot
/// be read, or fewer assemblies than `BORZOI_EXISTENCE_SWEEP_MIN` (default 1)
/// compared, fails: a sweep that reads nothing must not pass.
#[test]
#[ignore = "walks a package cache named by BORZOI_EXISTENCE_SWEEP_ROOT"]
fn the_existence_index_is_what_both_readers_report_over_a_package_cache() {
    let root = PathBuf::from(
        std::env::var_os("BORZOI_EXISTENCE_SWEEP_ROOT")
            .expect("BORZOI_EXISTENCE_SWEEP_ROOT names the directory to sweep"),
    );
    let min: usize = std::env::var("BORZOI_EXISTENCE_SWEEP_MIN")
        .map(|v| v.parse().expect("BORZOI_EXISTENCE_SWEEP_MIN is a count"))
        .unwrap_or(1);
    let mut dlls = Vec::new();
    let mut stack = vec![root.clone()];
    while let Some(dir) = stack.pop() {
        let entries = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()));
        for entry in entries {
            let path = entry
                .unwrap_or_else(|e| panic!("cannot read an entry of {}: {e}", dir.display()))
                .path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|x| x == "dll") {
                dlls.push(path);
            }
        }
    }
    dlls.sort();
    // The cache's copy of each simple name, the last in path order (the
    // highest version, as near as a path says), and the reference pack's
    // names, which the oracle's script references supply.
    let mut by_name: BTreeMap<String, PathBuf> = BTreeMap::new();
    for dll in &dlls {
        if let Some(stem) = dll.file_stem().and_then(|s| s.to_str()) {
            by_name.insert(stem.to_ascii_lowercase(), dll.clone());
        }
    }
    let framework: Vec<String> = std::fs::read_dir(
        ensure_system_runtime_dll()
            .parent()
            .expect("the reference pack's directory"),
    )
    .expect("list the reference pack")
    .filter_map(|e| {
        let path = e.expect("a directory entry").path();
        path.file_stem()
            .and_then(|s| s.to_str())
            .map(str::to_ascii_lowercase)
    })
    .chain(["fsharp.core".to_string()])
    .collect();
    let mut failures = Vec::new();
    let (mut compared, mut il_rows, mut pickle_rows) = (0, 0, 0);
    for dll in &dlls {
        let bytes = std::fs::read(dll).expect("read");
        let Ok(assembly) = Ecma335Assembly::parse(&bytes) else {
            continue;
        };
        let fsharp = !matches!(
            assembly.existence_index().map(|i| i.pickle),
            Ok(PickleLayer::NotFSharp)
        );
        let support: Vec<PathBuf> = if fsharp {
            assembly
                .assembly_refs()
                .iter()
                .map(|r| r.name.to_ascii_lowercase())
                .filter(|name| !framework.contains(name))
                .filter_map(|name| by_name.get(&name).cloned())
                .filter(|p| p != dll)
                .collect()
        } else {
            Vec::new()
        };
        let (f, i, p, _) = compare(std::slice::from_ref(dll), &support);
        failures.extend(f);
        compared += 1;
        il_rows += i;
        pickle_rows += p;
    }
    eprintln!(
        "{compared} assemblies: {il_rows} TypeDef rows and {pickle_rows} pickled entities compared"
    );
    assert!(
        compared >= min,
        "only {compared} assemblies compared under {}, fewer than {min}",
        root.display()
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
