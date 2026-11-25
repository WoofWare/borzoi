//! Differential test: `MSBuildStartupDirectory`, the working directory of the
//! build process, against MSBuild run from a chosen working directory.
//!
//! The walk seeds the name only for an evaluation that models a process the
//! caller launches (`test_support::parse_fsproj_reads`'s `startup_directory`,
//! the restore cone's A₁ path). Each oracle child here runs from one directory,
//! since MSBuild fixes the value once per process, and the same projects are
//! evaluated on both sides:
//!
//! - **With the directory supplied**, every read the projects make must commit,
//!   and to MSBuild's value. The reads cover the name in a property body, in
//!   an imported file, in an item `Include` (where a raw `;` splits the list),
//!   in conditions (an equality with `MSBuildProjectDirectory`, which MSBuild
//!   escapes where it splices this name raw; `HasTrailingSlash`; `Exists`), a
//!   `<Choose>` arm, an `<Import>` path built from it (and the self-default
//!   idiom over the name the imported file writes), and a gated `Compile`
//!   item. Where MSBuild rejects a project, the walk must commit nothing.
//! - **Without it**, as every evaluation the LSP serves runs, nothing the walk
//!   commits may move between two of MSBuild's working directories: a value
//!   that depends on the startup directory is a guess there, never a fact.
//!
//! The working directories are the project's own, a symlink to it, directories
//! whose names hold a space, a `;`, a `%20`, a `$` and a `$(…)` reference, and a
//! symlink to a directory (MSBuild reports the directory a link resolves to).

#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use borzoi_msbuild::ItemKind;
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::test_support::{InexactUnset, PropertyRead, ReadProbe, parse_fsproj_reads};
use common::Oracle;
use serde_json::Value;
use tempfile::TempDir;

/// The names of the directories, beside the project's, that the oracle starts
/// in. Each also holds a `start.props` the projects import through
/// `$(MSBuildStartupDirectory)`.
const SPELLINGS: &[&str] = &[
    "plain",
    "with space",
    "semi;colon",
    "pct%20enc",
    "dollar$sign",
    "$(Body)",
];

/// The project whose directory may be the startup directory: the name in a
/// body, in an equality with `MSBuildProjectDirectory`, in a `<Choose>` arm, in
/// an imported file, in an item `Include` and in a `Compile` item's condition.
const APP: &str = r#"<Project>
  <PropertyGroup>
    <Body>$(MSBuildStartupDirectory)</Body>
    <IsProjectDir Condition="'$(MSBuildStartupDirectory)' == '$(MSBuildProjectDirectory)'">yes</IsProjectDir>
  </PropertyGroup>
  <Choose>
    <When Condition="'$(MSBuildStartupDirectory)' == '$(MSBuildProjectDirectory)'">
      <PropertyGroup><Arm>project</Arm></PropertyGroup>
    </When>
    <Otherwise>
      <PropertyGroup><Arm>elsewhere</Arm></PropertyGroup>
    </Otherwise>
  </Choose>
  <Import Project="Imp.props" />
  <ItemGroup>
    <Split Include="$(MSBuildStartupDirectory)" />
    <Compile Include="A.fs" Condition="'$(MSBuildStartupDirectory)' == '$(MSBuildProjectDirectory)'" />
    <Compile Include="B.fs" />
  </ItemGroup>
</Project>
"#;

/// The name in the functions that take a scalar, which MSBuild refuses a `;`
/// in (it rejects the project), and in the path of an `<Import>`, followed by
/// the self-default idiom over the name the imported file writes: the walk
/// without a startup directory cannot know which branch the default takes.
const PROBES: &str = r#"<Project>
  <PropertyGroup>
    <Slash Condition="HasTrailingSlash('$(MSBuildStartupDirectory)')">yes</Slash>
    <Present Condition="Exists('$(MSBuildStartupDirectory)')">yes</Present>
  </PropertyGroup>
  <Import Project="$(MSBuildStartupDirectory)/start.props" Condition="Exists('$(MSBuildStartupDirectory)/start.props')" />
  <PropertyGroup>
    <FromStart Condition="'$(FromStart)' == ''">no</FromStart>
  </PropertyGroup>
</Project>
"#;

const IMPORTED: &str = r#"<Project>
  <PropertyGroup>
    <FromImport>$(MSBuildStartupDirectory)/sub</FromImport>
  </PropertyGroup>
</Project>
"#;

const START_PROPS: &str = r#"<Project>
  <PropertyGroup>
    <FromStart>yes</FromStart>
  </PropertyGroup>
</Project>
"#;

const PROPERTIES: &[&str] = &[
    "MSBuildStartupDirectory",
    "Body",
    "IsProjectDir",
    "Arm",
    "FromImport",
    "Slash",
    "Present",
    "FromStart",
];

const ITEMS: &[&str] = &["Split", "Compile"];

/// One evaluation's answer: each property's value (`None` when unset), and
/// each item type's identities in order.
#[derive(Debug, PartialEq, Eq, Clone)]
struct Answer {
    properties: BTreeMap<String, Option<String>>,
    items: BTreeMap<String, Vec<String>>,
}

struct Tree {
    _tmp: TempDir,
    /// The projects, by name.
    projects: Vec<(&'static str, PathBuf)>,
    /// Each working directory, by a label, as the oracle is started in it.
    working_dirs: Vec<(String, PathBuf)>,
    /// The directory the `symlink` working directory resolves to.
    real: PathBuf,
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

fn tree() -> Tree {
    let tmp = TempDir::new().unwrap();
    // Resolved, so that the project's own directory, as MSBuild spells it, is
    // the physical one a process started there reports.
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    let project_dir = root.join("proj");
    let app = project_dir.join("App.proj");
    let probes = project_dir.join("Probes.proj");
    write(&app, APP);
    write(&probes, PROBES);
    write(&project_dir.join("Imp.props"), IMPORTED);
    write(&project_dir.join("start.props"), START_PROPS);
    let project_link = root.join("project-link");
    std::os::unix::fs::symlink(&project_dir, &project_link).unwrap();
    let mut working_dirs = vec![
        ("project".to_owned(), project_dir),
        ("project-link".to_owned(), project_link),
    ];
    for spelling in SPELLINGS {
        let dir = root.join(spelling);
        write(&dir.join("start.props"), START_PROPS);
        working_dirs.push(((*spelling).to_owned(), dir));
    }
    let real = root.join("real");
    write(&real.join("start.props"), START_PROPS);
    let link = root.join("link");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    working_dirs.push(("symlink".to_owned(), link));
    Tree {
        _tmp: tmp,
        projects: vec![("App", app), ("Probes", probes)],
        working_dirs,
        real,
    }
}

/// MSBuild's evaluation of `project`, or `None` where it rejects it.
fn theirs(oracle: &mut Oracle, project: &Path) -> Option<Answer> {
    let answer = oracle.try_evaluated(project, &[], PROPERTIES, ITEMS, &[])?;
    let properties = PROPERTIES
        .iter()
        .map(|name| {
            let value = match &answer["properties"][*name] {
                Value::Null => None,
                Value::String(s) if s.is_empty() => None,
                Value::String(s) => Some(s.clone()),
                other => panic!("evaluated: {name} is {other}"),
            };
            ((*name).to_owned(), value)
        })
        .collect();
    let items = ITEMS
        .iter()
        .map(|item_type| {
            let identities = answer["items"][*item_type]
                .as_array()
                .unwrap_or_else(|| panic!("evaluated: no items for {item_type}"))
                .iter()
                .map(|item| item["identity"].as_str().unwrap().to_owned())
                .collect();
            ((*item_type).to_owned(), identities)
        })
        .collect();
    Some(Answer { properties, items })
}

/// MSBuild's answer for each project from each working directory, keyed by
/// project and working directory label.
fn msbuild_answers(tree: &Tree) -> BTreeMap<(&'static str, String), Option<Answer>> {
    let mut answers = BTreeMap::new();
    for (label, dir) in &tree.working_dirs {
        let mut oracle = Oracle::spawn_in_dir(dir);
        for (name, project) in &tree.projects {
            answers.insert((*name, label.clone()), theirs(&mut oracle, project));
        }
    }
    answers
}

/// What the walk commits: the properties it reads as a value (`None` for an
/// exact unset), and the item lists it reads exactly. A read that makes no
/// claim is absent.
struct Ours {
    properties: BTreeMap<String, Option<String>>,
    items: BTreeMap<String, Vec<String>>,
    /// The read of `MSBuildStartupDirectory` itself.
    startup: PropertyRead,
}

fn ours(project: &Path, startup_directory: Option<&Path>) -> Ours {
    let source = host_fs::read_to_string(project).unwrap();
    let probe = ReadProbe {
        properties: PROPERTIES.iter().map(|p| (*p).to_owned()).collect(),
        item_types: ITEMS.iter().map(|i| (*i).to_owned()).collect(),
        ..ReadProbe::default()
    };
    let (parsed, reads) = parse_fsproj_reads(
        &borzoi_msbuild::ProjectFile::buffer(project, &source)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
        startup_directory,
        &probe,
    )
    .expect("the project parses");
    let mut properties = BTreeMap::new();
    for name in PROPERTIES {
        let committed = match &reads.properties[*name] {
            PropertyRead::Value(value) if value.is_empty() => Some(None),
            PropertyRead::Value(value) => Some(Some(value.clone())),
            PropertyRead::Unset => Some(None),
            PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
        };
        if let Some(value) = committed {
            properties.insert((*name).to_owned(), value);
        }
    }
    let mut items = BTreeMap::new();
    // `Compile` lives in its own bucket, joined onto the project's directory,
    // and is committed unless the walk marks it uncertain.
    if !parsed.items_uncertain {
        let project_dir = project.parent().unwrap();
        let compile = parsed
            .items
            .iter()
            .filter(|item| item.kind == ItemKind::Compile)
            .map(|item| {
                let relative = item.include.strip_prefix(project_dir).unwrap_or_else(|_| {
                    panic!("{} is outside the project", item.include.display())
                });
                relative.to_str().unwrap().to_owned()
            })
            .collect();
        items.insert("Compile".to_owned(), compile);
    }
    for item_type in ITEMS.iter().filter(|t| **t != "Compile") {
        let read = &reads.items[*item_type];
        if read.exact {
            let identities = read
                .items
                .as_ref()
                .map(|rows| rows.iter().map(|row| row.identity.clone()).collect())
                .unwrap_or_default();
            items.insert((*item_type).to_owned(), identities);
        }
    }
    Ours {
        properties,
        items,
        startup: reads.properties["MSBuildStartupDirectory"].clone(),
    }
}

#[test]
fn a_supplied_startup_directory_reads_as_msbuild_reads_it() {
    let tree = tree();
    let answers = msbuild_answers(&tree);
    for (label, dir) in &tree.working_dirs {
        for (name, project) in &tree.projects {
            let walk = ours(project, Some(dir));
            match &answers[&(*name, label.clone())] {
                // Every read commits: the name is a fact of the process, and
                // nothing the projects do with it is beyond the walk.
                Some(msbuild) => {
                    assert_eq!(
                        walk.properties, msbuild.properties,
                        "{name} started in {label}: our properties (left) are not MSBuild's (right)"
                    );
                    assert_eq!(
                        walk.items, msbuild.items,
                        "{name} started in {label}: our items (left) are not MSBuild's (right)"
                    );
                }
                None => assert!(
                    walk.properties.is_empty() && walk.items.is_empty(),
                    "{name} started in {label}: MSBuild rejects the project, and we commit \
                     {:?} and {:?}",
                    walk.properties,
                    walk.items
                ),
            }
        }
    }
    // Not vacuous: the working directory moves what MSBuild reads, in each way
    // the spellings were chosen to show.
    let answer = |project: &'static str, label: &str| {
        answers[&(project, label.to_owned())]
            .clone()
            .unwrap_or_else(|| panic!("MSBuild rejects {project} started in {label}"))
    };
    let property = |project: &'static str, label: &str, name: &str| {
        answer(project, label).properties[name].clone()
    };
    assert_eq!(
        property("App", "project", "Arm").as_deref(),
        Some("project")
    );
    assert_eq!(
        property("App", "project-link", "Arm").as_deref(),
        Some("project"),
        "MSBuild reports the directory a link to the project's resolves to"
    );
    assert_eq!(
        property("App", "plain", "Arm").as_deref(),
        Some("elsewhere")
    );
    assert!(
        property("App", "pct%20enc", "Body")
            .unwrap()
            .ends_with("/pct enc"),
        "MSBuild splices the startup directory raw, so `%20` decodes"
    );
    assert_eq!(
        property("Probes", "pct%20enc", "FromStart").as_deref(),
        Some("no"),
        "the decoded path names no directory, so its start.props is not imported \
         and the self-default fills the name"
    );
    assert_eq!(
        property("Probes", "with space", "FromStart").as_deref(),
        Some("yes")
    );
    assert_eq!(
        answer("App", "semi;colon").items["Split"].len(),
        2,
        "a raw `;` splits an Include"
    );
    assert!(
        answers[&("Probes", "semi;colon".to_owned())].is_none(),
        "MSBuild rejects a `;` in the argument of a scalar function"
    );
    assert_eq!(
        property("App", "symlink", "Body").as_deref(),
        Some(tree.real.to_str().unwrap()),
        "MSBuild reports the physical directory"
    );
}

#[test]
fn without_a_startup_directory_nothing_that_moves_with_it_is_committed() {
    let tree = tree();
    let answers = msbuild_answers(&tree);
    for (name, project) in &tree.projects {
        let walk = ours(project, None);
        // `Probes` imports a path built from the name under an `Exists` of
        // it, which is true of a directory too: with the name unknown, the
        // import may be rejected, and that is why the name is inexact.
        let why_inexact = |read: &PropertyRead| match read {
            PropertyRead::UnsetInexact(InexactUnset::Toolset) => *name != "Probes",
            PropertyRead::UnsetInexact(InexactUnset::Rejected(rejection)) => {
                *name == "Probes"
                    && matches!(
                        **rejection,
                        borzoi_msbuild::Rejection {
                            certainty: borzoi_msbuild::RejectionCertainty::Possible,
                            cause: borzoi_msbuild::RejectionCause::Import {
                                why: borzoi_msbuild::UnloadableImport::PathUndecided,
                                ..
                            },
                            ..
                        }
                    )
            }
            _ => false,
        };
        assert!(
            why_inexact(&walk.startup),
            "{name}: without a startup directory the name is unset and inexact, not {:?}",
            walk.startup
        );
        for (label, _) in &tree.working_dirs {
            let Some(msbuild) = &answers[&(*name, label.clone())] else {
                assert!(
                    walk.properties.is_empty() && walk.items.is_empty(),
                    "{name}: MSBuild started in {label} rejects the project, and we commit \
                     {:?} and {:?} with no startup directory",
                    walk.properties,
                    walk.items
                );
                continue;
            };
            for (property, value) in &walk.properties {
                assert_eq!(
                    Some(value),
                    msbuild.properties.get(property),
                    "{name}: we commit {property} with no startup directory, and MSBuild \
                     started in {label} disagrees"
                );
            }
            for (item_type, identities) in &walk.items {
                assert_eq!(
                    Some(identities),
                    msbuild.items.get(item_type),
                    "{name}: we commit @({item_type}) with no startup directory, and MSBuild \
                     started in {label} disagrees"
                );
            }
        }
    }
    // Not vacuous: something in each channel does move with the directory.
    let moves = |project: &'static str, read: &dyn Fn(&Answer) -> String| {
        let seen: BTreeSet<String> = tree
            .working_dirs
            .iter()
            .filter_map(|(label, _)| answers[&(project, label.clone())].as_ref())
            .map(read)
            .collect();
        seen.len() > 1
    };
    for name in ["Body", "Arm", "FromImport"] {
        assert!(
            moves("App", &|a| format!("{:?}", a.properties[name])),
            "{name} does not move between MSBuild's working directories"
        );
    }
    for name in ["Present", "FromStart"] {
        assert!(
            moves("Probes", &|a| format!("{:?}", a.properties[name])),
            "{name} does not move between MSBuild's working directories"
        );
    }
    for item_type in ITEMS {
        assert!(
            moves("App", &|a| format!("{:?}", a.items[*item_type])),
            "@({item_type}) does not move between MSBuild's working directories"
        );
    }
}
