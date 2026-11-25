//! NuGet's restore guards as one table ([`crate::NUGET_GUARDS`]), held to
//! the matcher it replaced: by a generated property, and on every hostile
//! property value of the shared library (`hostile::value`) as each guard's
//! compared value, recorded in the census `nuget_guards`.

/// The guard atoms of NuGet's restore groups as they were matched before
/// they were a table, kept verbatim as the reference the table must equal.
fn nuget_group_atom_before(atom: &str) -> bool {
    let literal = |text: &str| !crate::expands(text);
    let quoted = |atom: &str, prefix: &str, suffix: &str| {
        atom.strip_prefix(prefix)
            .and_then(|rest| rest.strip_suffix(suffix))
            .is_some_and(|value| literal(value) && !value.contains('\''))
    };
    atom == "'$(ExcludeRestorePackageImports)' != 'true'"
        || atom == "'$(TargetFramework)' == ''"
        || quoted(atom, "'$(TargetFramework)' == '", "'")
        || quoted(atom, "'$(Language)' == '", "'")
        || quoted(atom, "'$(Language)' != '", "'")
}

/// An atom shaped like a guard: one of the guards' names or another, in
/// either case, an operator, and a value that may expand, hold a quote or a
/// line break or tab, with the spacing perturbed.
fn nuget_guard_atom() -> impl proptest::strategy::Strategy<Value = String> {
    use proptest::prelude::*;
    let name = prop::sample::select(vec![
        "ExcludeRestorePackageImports",
        "TargetFramework",
        "Language",
        "language",
        "TargetFrameworks",
        "Configuration",
    ]);
    let op = prop::sample::select(vec!["==", "!=", "=", "<"]);
    let value = prop_oneof![
        prop::sample::select(vec![
            "", "true", "false", "F#", "net10.0", "a'b", "$(X)", "@(Y)", "%(Z)", "$"
        ])
        .prop_map(str::to_string),
        "[ -~\t\n\r]{0,6}",
    ];
    let spacing = prop::sample::select(vec![" ", "", "  "]);
    (name, op, value, spacing.clone(), spacing).prop_map(|(name, op, value, before, after)| {
        format!("'$({name})'{before}{op}{after}'{value}'")
    })
}

proptest::proptest! {
    /// The table of NuGet's guards matches exactly the atoms the matcher it
    /// replaced matched.
    #[test]
    fn nuget_guards_match_as_before(atom in nuget_guard_atom()) {
        proptest::prop_assert_eq!(crate::nuget_group_atom(&atom), nuget_group_atom_before(&atom));
    }
}

/// Each guard matches somewhere, so the property above compares every row.
#[test]
fn every_nuget_guard_matches() {
    for atom in [
        "'$(ExcludeRestorePackageImports)' != 'true'",
        "'$(TargetFramework)' == ''",
        "'$(TargetFramework)' == 'net10.0'",
        "'$(Language)' == 'F#'",
        "'$(Language)' != 'C#'",
    ] {
        assert!(crate::nuget_group_atom(atom), "{atom}");
    }
    for atom in [
        "'$(TargetFramework)' == '$(X)'",
        "'$(Language)' == 'a'b'",
        "'$(ExcludeRestorePackageImports)' != 'false'",
    ] {
        assert!(!crate::nuget_group_atom(atom), "{atom}");
    }
}

/// Every hostile property value (`hostile::value`), rendered on a plain value,
/// as the compared value of each guard's name and operator: the table and the
/// matcher it replaced agree, each value recorded in the census
/// `nuget_guards`.
#[test]
fn nuget_guards_agree_on_every_hostile_value() {
    use borzoi_oracle_harness::hostile::{coverage, value};
    use std::collections::BTreeSet;
    let census = coverage::open(file!(), "nuget_guards", &[]);
    let mut failures = Vec::new();
    for entry in value::alphabet().entries() {
        for plain in ["", "true", "F#"] {
            let compared = entry.value.render(plain);
            for (name, op, _) in crate::NUGET_GUARDS {
                let atom = format!("'$({name})' {op} '{compared}'");
                let ours = crate::nuget_group_atom(&atom);
                if ours != nuget_group_atom_before(&atom) {
                    failures.push(format!("{atom:?}: table {ours}"));
                }
                census.reached(
                    &BTreeSet::from([entry.dimension]),
                    if ours { "match" } else { "no match" },
                );
            }
        }
    }
    census.reached(&BTreeSet::new(), "plain");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --lib \
         nuget_guard_tests::",
    );
}
