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

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use borzoi_assembly::{Ecma335Assembly, ExistenceIndex, PickleLayer, PickledEntityKind};

use crate::common::assembly_entities::{
    AssemblyEntities, FcsAccess, invoke_fcs_dump_assembly_entities,
};
use crate::common::{
    ensure_abbrev_fixture_built, ensure_active_pattern_fixture_built,
    ensure_attribute_alias_fixture_built, ensure_autoopen_fixture_built,
    ensure_existence_fixture_built, ensure_ext_universe_fixture_built, ensure_fsharp_core_dll,
    ensure_measure_fixture_built, ensure_module_value_fixture_built,
    ensure_rqa_union_fixture_built, ensure_system_runtime_dll,
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

/// Every disagreement between the index of each of `dlls` and the oracle,
/// and how many rows of each layer were compared.
fn compare(dlls: &[PathBuf]) -> (Vec<String>, usize, usize) {
    let anchor = temp_fs_file(
        "assembly_entities_diff_anchor",
        "module Anchor\nlet x = 1\n",
    );
    let refs: Vec<&Path> = dlls.iter().map(PathBuf::as_path).collect();
    let report = invoke_fcs_dump_assembly_entities(&anchor, &refs);
    let _ = std::fs::remove_file(&anchor);
    let mut failures = Vec::new();
    let (mut il_rows, mut pickle_rows) = (0, 0);
    for entities in &report.assemblies {
        let file = &entities.file;
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
    (failures, il_rows, pickle_rows)
}

/// The reference pack, FSharp.Core and the F# fixtures: the pickles hold
/// every kind of entity at every accessibility, and the reference pack every
/// shape of `TypeDef` the compilers write.
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
    ] {
        dlls.push(fixture.to_path_buf());
    }
    let (failures, il_rows, pickle_rows) = compare(&dlls);
    eprintln!(
        "{} assemblies: {il_rows} TypeDef rows and {pickle_rows} pickled entities compared",
        dlls.len()
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
/// each read on its own.
#[test]
#[ignore = "walks a package cache named by BORZOI_EXISTENCE_SWEEP_ROOT"]
fn the_existence_index_is_what_both_readers_report_over_a_package_cache() {
    let root = std::env::var_os("BORZOI_EXISTENCE_SWEEP_ROOT")
        .expect("BORZOI_EXISTENCE_SWEEP_ROOT names the directory to sweep");
    let mut dlls = Vec::new();
    let mut stack = vec![PathBuf::from(root)];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|x| x == "dll") {
                dlls.push(path);
            }
        }
    }
    dlls.sort();
    let mut failures = Vec::new();
    let (mut il_rows, mut pickle_rows) = (0, 0);
    for dll in &dlls {
        if Ecma335Assembly::parse(&std::fs::read(dll).expect("read")).is_err() {
            continue;
        }
        let (f, i, p) = compare(std::slice::from_ref(dll));
        failures.extend(f);
        il_rows += i;
        pickle_rows += p;
    }
    eprintln!(
        "{} assemblies: {il_rows} TypeDef rows and {pickle_rows} pickled entities compared",
        dlls.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
