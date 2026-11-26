//! `MSBuildAllProjects` after the property pass, against design-time MSBuild
//! (#1131).
//!
//! Between its property pass and its item pass, MSBuild's evaluator prepends
//! the most recently written of the project and its imports to
//! `MSBuildAllProjects` (`Evaluator.SetAllProjectsProperty`, MSBuild 18.9):
//! a write no document makes, by file times the walk does not read. So every
//! read of the name after the property pass must be exact against MSBuild or
//! declined: the final table's, a `Compile` item's spec, and a
//! `ProjectReference`'s and a `PackageReference`'s gate, one of [`GATES`] in
//! each project, so that a decline of one gate cannot hide a wrong decision
//! of another behind the list it makes uncertain. A read during the property
//! pass, before the write, stays exact; and a gate another operand decides
//! stays decided.
//!
//! The reference list's contract tolerates a missing edge behind a gate the
//! walk cannot decide (`ParsedProject::project_references_uncertain`), so a
//! certain list is held to no phantom edge only. What tells an empty list the
//! walk mistook for exact from a decline is the walk's own read of the list,
//! the one an `@(ProjectReference)` in it takes (`ItemRead::exact`): an exact
//! one must hold MSBuild's references, so a walk that took the opened gate for
//! a closed one reads an exact list without them.

mod common;

use std::collections::{BTreeSet, HashMap};

use borzoi_msbuild::PropertyRead;
use borzoi_msbuild::test_support::{ReadProbe, parse_fsproj_reads};
use tempfile::TempDir;

/// What the documents write to the name before the item pass: nothing, an
/// empty value, a value, the value the gates below test, and the SDK's own
/// append.
const WRITES: &[&str] = &[
    "",
    "<{name}></{name}>",
    "<{name}>a.props</{name}>",
    "<{name}>off</{name}>",
    "<{name}>$({name});b.props</{name}>",
];

/// The reference gates: one the rewritten value closes, and one it opens.
const GATES: &[&str] = &["'$({name})' == 'off'", "'$({name})' != ''"];

/// The spellings of the name a document reads it by.
const SPELLINGS: &[&str] = &["MSBuildAllProjects", "msbuildallprojects"];

/// A property read the walk publishes, against MSBuild's value of it: exact
/// (`Value` equal, `Unset` where MSBuild leaves it undefined), or declined.
fn exact_or_declined(ours: &PropertyRead, theirs: Option<&String>) -> Result<(), String> {
    match ours {
        PropertyRead::Value(value) if Some(value) == theirs => Ok(()),
        PropertyRead::Unset if theirs.is_none_or(String::is_empty) => Ok(()),
        PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => Ok(()),
        other => Err(format!("we publish {other:?}, MSBuild holds {theirs:?}")),
    }
}

#[test]
fn all_projects_after_the_property_pass_is_exact_or_declined() {
    let mut oracle = common::Oracle::spawn();
    let mut violations = Vec::new();
    for write in WRITES {
        for (name, gate) in SPELLINGS
            .iter()
            .flat_map(|name| GATES.iter().map(move |gate| (name, gate)))
        {
            let write = write.replace("{name}", name);
            let gate = gate.replace("{name}", name);
            let tmp = TempDir::new().unwrap();
            let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
            let path = dir.join("Demo.fsproj");
            let body = format!(
                "<Project><PropertyGroup>{write}<During>[$({name})]</During></PropertyGroup>\
                 <ItemGroup><Compile Include=\"$({name})x.fs\" />\
                 <ProjectReference Include=\"P.fsproj\" Condition=\"{gate}\" />\
                 <PackageReference Include=\"Pkg\" Version=\"1.0.0\" Condition=\"{gate}\" />\
                 </ItemGroup></Project>"
            );
            std::fs::write(&path, &body).unwrap();
            let names = ["MSBuildAllProjects".to_owned(), "During".to_owned()];
            let theirs = oracle
                .project_design_time(&body, &names, Some(&path), &[])
                .expect("MSBuild evaluates the project");
            let mut their_items = |item_type: &str| {
                oracle
                    .items(&body, &path, item_type, &[])
                    .expect("MSBuild evaluates the project")
            };
            let their_compile = their_items("Compile");
            let their_references = their_items("ProjectReference");
            let their_packages: BTreeSet<String> = their_items("PackageReference")
                .iter()
                .filter_map(|full| full.rsplit('/').next().map(str::to_owned))
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
            let label = format!("write {write:?}, read as {name}, gate {gate:?}");
            if let Err(error) = exact_or_declined(
                &ours.property("MSBuildAllProjects"),
                theirs.get("MSBuildAllProjects"),
            ) {
                violations.push(format!("{label}: the final value: {error}"));
            }
            if !ours.items_uncertain {
                let our_compile: Vec<String> = ours
                    .items
                    .iter()
                    .filter(|item| item.kind == borzoi_msbuild::ItemKind::Compile)
                    .map(|item| item.include.to_string_lossy().into_owned())
                    .collect();
                if our_compile != their_compile {
                    violations.push(format!(
                        "{label}: Compile {our_compile:?} committed, MSBuild holds {their_compile:?}"
                    ));
                }
            }
            if !ours.project_references_uncertain && !ours.project_references_incomplete {
                let our_references: Vec<String> = ours
                    .project_references
                    .iter()
                    .map(|item| item.include.to_string_lossy().into_owned())
                    .collect();
                if our_references
                    .iter()
                    .any(|reference| !their_references.contains(reference))
                {
                    violations.push(format!(
                        "{label}: ProjectReference {our_references:?} committed, a phantom edge: MSBuild holds \
                         {their_references:?}"
                    ));
                }
            }
            let probe = ReadProbe {
                item_types: vec!["ProjectReference".to_owned()],
                ..ReadProbe::default()
            };
            let (_, reads) = parse_fsproj_reads(
                &borzoi_msbuild::ProjectFile::buffer(&path, &body)
                    .expect("a project path spelt as its full path"),
                &HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
                None,
                &probe,
            )
            .expect("well-formed XML parses");
            let read = &reads.items["ProjectReference"];
            if read.exact {
                let our_list: Vec<String> = read
                    .items
                    .iter()
                    .flatten()
                    .map(|row| dir.join(&row.identity).to_string_lossy().into_owned())
                    .collect();
                if our_list != their_references {
                    violations.push(format!(
                        "{label}: @(ProjectReference) read exactly as {our_list:?}, MSBuild \
                         holds {their_references:?}"
                    ));
                }
            }
            if !ours.package_references_uncertain {
                let our_packages: BTreeSet<String> = ours
                    .package_references
                    .iter()
                    .map(|package| package.id.clone())
                    .collect();
                if our_packages != their_packages {
                    violations.push(format!(
                        "{label}: PackageReference {our_packages:?} committed, MSBuild holds \
                         {their_packages:?}"
                    ));
                }
            }
            // A read during the property pass, before the write: exact; and,
            // after a document's write of the name that reads nothing,
            // committed (an unwritten name is one the toolset may define,
            // which the walk declines).
            let during = ours.property("During");
            if let Err(error) = exact_or_declined(&during, theirs.get("During")) {
                violations.push(format!("{label}: the property pass's read: {error}"));
            }
            if !write.is_empty() && !write.contains("$(") {
                assert!(
                    during.value().is_some(),
                    "{label}: the property pass's read declined: {during:?}"
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

/// A `Compile` item gated on the name by a condition another operand decides
/// (`false And …`) is ruled out whatever the name holds: the list stays
/// certain.
#[test]
fn a_gate_another_operand_decides_keeps_compile_certain() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let body = "<Project><PropertyGroup><MSBuildAllProjects>off</MSBuildAllProjects>\
                </PropertyGroup><ItemGroup><Compile Include=\"a.fs\" />\
                <Compile Include=\"g.fs\" Condition=\"false And '$(MSBuildAllProjects)' == 'off'\" />\
                </ItemGroup></Project>";
    std::fs::write(&path, body).unwrap();
    let ours = common::parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&path, body)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed XML parses");
    assert!(!ours.items_uncertain, "{:#?}", ours.diagnostics);
    let compile: Vec<String> = ours
        .items
        .iter()
        .map(|item| item.include.to_string_lossy().into_owned())
        .collect();
    assert_eq!(
        compile,
        vec![dir.join("a.fs").to_string_lossy().into_owned()]
    );
}
