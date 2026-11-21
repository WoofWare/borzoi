//! `MSBuildAllProjects` after the property pass, against design-time MSBuild
//! (#1131).
//!
//! Between its property pass and its item pass, MSBuild's evaluator prepends
//! the most recently written of the project and its imports to
//! `MSBuildAllProjects` (`Evaluator.SetAllProjectsProperty`, MSBuild 18.9):
//! a write no document makes, by file times the walk does not read. So every
//! read of the name after the property pass (an item's, and the final table's)
//! must be exact against MSBuild or declined, while a read during the property
//! pass, before the write, stays exact.

mod common;

use std::collections::{BTreeSet, HashMap};

use tempfile::TempDir;

/// What the documents write to the name before the item pass: nothing, an
/// empty value, a value, and the SDK's own append.
const WRITES: &[&str] = &[
    "",
    "<{name}></{name}>",
    "<{name}>a.props</{name}>",
    "<{name}>$({name});b.props</{name}>",
];

/// The spellings of the name a document reads it by.
const SPELLINGS: &[&str] = &["MSBuildAllProjects", "msbuildallprojects"];

#[test]
fn all_projects_after_the_property_pass_is_exact_or_declined() {
    let mut oracle = common::Oracle::spawn();
    let mut violations = Vec::new();
    for write in WRITES {
        for name in SPELLINGS {
            let write = write.replace("{name}", name);
            let tmp = TempDir::new().unwrap();
            let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
            let path = dir.join("Demo.fsproj");
            let body = format!(
                "<Project><PropertyGroup>{write}<During>[$({name})]</During></PropertyGroup>\
                 <ItemGroup><Compile Include=\"$({name})x.fs\" /></ItemGroup></Project>"
            );
            std::fs::write(&path, &body).unwrap();
            let names = ["MSBuildAllProjects".to_owned(), "During".to_owned()];
            let theirs = oracle
                .project_design_time(&body, &names, Some(&path), &[])
                .expect("MSBuild evaluates the project");
            let their_items: BTreeSet<String> = oracle
                .items(&body, &path, "Compile", &[])
                .expect("MSBuild evaluates the project")
                .into_iter()
                .collect();
            let ours = common::parse_fsproj_with_imports(
                &borzoi_msbuild::ProjectFile::buffer(&path, &body)
                    .expect("a project path spelt as its full path"),
                &HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed XML parses");
            let label = format!("write {write:?}, read as {name}");
            // The final table's value: exact, or declined.
            let property = ours.property("MSBuildAllProjects");
            if let Some(value) = property.value()
                && property.untrusted_cause().is_none()
                && Some(value) != theirs.get("MSBuildAllProjects").map(String::as_str)
            {
                violations.push(format!(
                    "{label}: the final value {value:?} committed, MSBuild holds {:?}",
                    theirs.get("MSBuildAllProjects")
                ));
            }
            // An item read after the write: exact, or declined.
            if !ours.items_uncertain {
                let our_items: BTreeSet<String> = ours
                    .items
                    .iter()
                    .filter(|item| item.kind == borzoi_msbuild::ItemKind::Compile)
                    .map(|item| item.include.to_string_lossy().into_owned())
                    .collect();
                if our_items != their_items {
                    violations.push(format!(
                        "{label}: Compile {our_items:?} committed, MSBuild holds {their_items:?}"
                    ));
                }
            }
            // A read during the property pass, before the write: exact, and,
            // after a document's write of the name that reads nothing, committed (an unwritten
            // name is one the toolset may define, which the walk declines).
            let during = ours.property("During");
            if write.is_empty() || write.contains("$(") {
                if let Some(value) = during.value()
                    && during.untrusted_cause().is_none()
                {
                    assert_eq!(
                        Some(value),
                        theirs.get("During").map(String::as_str),
                        "{label}: the property pass's read"
                    );
                }
            } else {
                assert_eq!(
                    during.value(),
                    theirs.get("During").map(String::as_str),
                    "{label}: the property pass's read"
                );
                assert!(
                    during.untrusted_cause().is_none(),
                    "{label}: the property pass's read declined"
                );
            }
        }
    }
    assert!(
        violations.is_empty(),
        "certain-implies-exact violated:\n{}",
        violations.join("\n")
    );
}
