//! Smoke test of the `assembly-entities` oracle
//! ([`crate::common::assembly_entities`]) over the real FSharp.Core: both
//! readers answer, and neither filters by accessibility.

use std::collections::BTreeMap;

use crate::common::assembly_entities::{
    FcsAccess, FcsEntityKind, IlVisibility, invoke_fcs_dump_assembly_entities,
};
use crate::common::{ensure_fsharp_core_dll, temp_fs_file};

#[test]
fn fsharp_core_reports_every_accessibility_from_both_readers() {
    let fsharp_core = ensure_fsharp_core_dll();
    let anchor = temp_fs_file("assembly_entities_anchor", "module Anchor\nlet x = 1\n");
    let report = invoke_fcs_dump_assembly_entities(&anchor, &[&fsharp_core]);
    let _ = std::fs::remove_file(&anchor);

    let [assembly] = report.assemblies.as_slice() else {
        panic!("one ref, so one assembly: {report:?}");
    };
    let fcs = &assembly.fcs;
    let il = &assembly.il;
    assert!(fcs.seen, "FCS did not load {}", assembly.file);
    assert_eq!(fcs.error, None, "the FCS walk failed");
    assert!(
        fcs.read_errors.is_empty(),
        "FCS property reads failed: {:?}",
        fcs.read_errors
    );
    assert_eq!(il.error, None, "the IL reader failed");

    let mut by_kind_access: BTreeMap<(FcsEntityKind, FcsAccess), usize> = BTreeMap::new();
    for e in &fcs.entities {
        *by_kind_access.entry((e.kind, e.access)).or_default() += 1;
    }
    let mut by_visibility: BTreeMap<IlVisibility, usize> = BTreeMap::new();
    for r in &il.rows {
        *by_visibility.entry(r.visibility).or_default() += 1;
    }
    println!("FCS entities by kind and access: {by_kind_access:?}");
    println!("IL rows by visibility: {by_visibility:?}");

    assert!(
        il.rows.iter().any(|r| matches!(
            r.visibility,
            IlVisibility::NestedPrivate | IlVisibility::NotPublic
        )),
        "the IL reader reported no non-public row"
    );
    assert!(
        fcs.entities
            .iter()
            .any(|e| e.kind == FcsEntityKind::Abbreviation && e.logical_name == "int"),
        "FCS reported no abbreviation named `int`"
    );
    assert!(
        fcs.entities.iter().any(|e| e.access != FcsAccess::Public),
        "FCS reported no non-public entity"
    );
}
