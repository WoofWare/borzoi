//! The grader of [`borzoi_msbuild::fsc::certified_compilation`] on trees of
//! projects joined by `ProjectReference`: **certainty implies exactness** for
//! the compiled name and for the reference assemblies fsc is handed for the
//! projects referenced, directly and transitively.
//!
//! Each case lays out two or three projects (a chain, a fan, a diamond),
//! perturbs one of them (an allowed property set to a line-break or
//! option-shaped value, the referenced project's directory named from
//! `hostile::name`, metadata on the reference, a multi-targeted or
//! unrestorable referenced project, a cycle), restores the referencing
//! project and asks the derivation. When it commits, a real build
//! ([`borzoi_oracle_harness::msbuild_oracle::fsc_args`]) must hand fsc
//! exactly that `-o:` name and exactly those reference paths among its `-r:`
//! arguments under the tree. The plain trees, and a referenced project
//! renamed by `AssemblyName`, must commit.
//!
//! The default run grades the must points and a seeded sample of the rest
//! (`BORZOI_FSC_TREE_SEED`, `BORZOI_FSC_TREE_CASES`); the ignored
//! `deep_every_tree` grades every case, and `deep_hostile_directories` every
//! hostile name as the referenced project's directory.

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use borzoi_msbuild::fsc::{ALLOWED_PROPERTIES, Certified, Grammar};
use borzoi_msbuild::observed::host_fs;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::hostile::{Dimension, coverage, name as hostile_name};
use borzoi_oracle_harness::msbuild_oracle::{
    BuildInputs, FscArgsDecline, FscArgsRequest, build_environment, fsc_args,
};
use common::SplitMix64;
use common::assembly_name::{self, Sdks};

/// The values an allowed property is set to in a project of the tree:
/// shaped to move fsc's output, and one plain one.
const VALUES: &[&str] = &[
    "Evil",
    "--out:obj/Evil.dll",
    "-r:/nonexistent/Evil.dll",
    "x\n--out:obj/Evil.dll",
    "x\r-r:Evil.dll",
    "x%0A-r%3AEvil.dll",
    "Evil$(_MSBUILDTLENABLED)",
];

/// A value of property `name` in `grammar` the build compiles with.
fn plain_value(name: &str, grammar: Grammar) -> &'static str {
    if name == "LangVersion" {
        return "latest";
    }
    match grammar {
        Grammar::Bool => "true",
        Grammar::OneOf(values) => values[0],
        Grammar::Framework | Grammar::Frameworks => "net10.0",
        Grammar::FileName => "Friend",
        Grammar::DottedIdentifier => "Debug",
        Grammar::Codes => "FS0040",
        Grammar::Version => "1.2.3",
        Grammar::Text => "Some text",
        Grammar::FscOptions => "--warnon:1182",
        Grammar::Path | Grammar::Paths => "/nonexistent/borzoi",
    }
}

/// One project of a tree.
#[derive(Debug, Clone)]
struct Project {
    /// Its directory's name, under the tree's root.
    dir: String,
    /// Its project file's stem.
    stem: &'static str,
    /// The projects it references, by index.
    references: Vec<usize>,
    /// Extra text in its first `<PropertyGroup>`.
    body: String,
    /// Extra attributes on each of its `<ProjectReference>` items.
    reference_attributes: String,
    /// Extra child elements of each of its `<ProjectReference>` items.
    reference_children: String,
    /// Extra text after its `<ItemGroup>` (an item definition, say).
    after: String,
    /// Its `TargetFrameworks` in place of its `TargetFramework`.
    frameworks: Option<String>,
    /// The language of its project file and source.
    language: Language,
}

/// A project's language.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Language {
    FSharp,
    CSharp,
}

impl Project {
    fn new(dir: &str, stem: &'static str, references: &[usize]) -> Project {
        Project {
            dir: dir.to_string(),
            stem,
            references: references.to_vec(),
            body: String::new(),
            reference_attributes: String::new(),
            reference_children: String::new(),
            after: String::new(),
            frameworks: None,
            language: Language::FSharp,
        }
    }
}

/// A tree of projects; the first is the one built and graded.
#[derive(Debug, Clone)]
struct Tree {
    label: String,
    projects: Vec<Project>,
    /// Global properties of the build.
    globals: Vec<(&'static str, &'static str)>,
    /// What the derivation must commit to: the name, and each project's
    /// reference assembly by its path under the root.
    must_commit: Option<(String, BTreeSet<String>)>,
    /// The derivation must decline.
    must_decline: bool,
}

/// The shapes: P→L, P→L→M, P→{L,M}, P→{L,M} with L→M.
fn shapes() -> Vec<(&'static str, Vec<Project>, BTreeSet<&'static str>)> {
    vec![
        (
            "pair",
            vec![Project::new("P", "P", &[1]), Project::new("L", "L", &[])],
            BTreeSet::from(["L"]),
        ),
        (
            "chain",
            vec![
                Project::new("P", "P", &[1]),
                Project::new("L", "L", &[2]),
                Project::new("M", "M", &[]),
            ],
            BTreeSet::from(["L", "M"]),
        ),
        (
            "fan",
            vec![
                Project::new("P", "P", &[1, 2]),
                Project::new("L", "L", &[]),
                Project::new("M", "M", &[]),
            ],
            BTreeSet::from(["L", "M"]),
        ),
        (
            "diamond",
            vec![
                Project::new("P", "P", &[1, 2]),
                Project::new("L", "L", &[2]),
                Project::new("M", "M", &[]),
            ],
            BTreeSet::from(["L", "M"]),
        ),
    ]
}

/// The reference assembly of the project in `dir` named `name`, built in
/// `configuration`, under the root.
fn ref_path(dir: &str, configuration: &str, name: &str) -> String {
    format!("{dir}/obj/{configuration}/net10.0/ref/{name}.dll")
}

/// The metadata names the derivation declines on a reference, among them
/// those `ALLOWED_METADATA` admits on other item types.
const REFERENCE_METADATA: &[&str] = &[
    "SetConfiguration",
    "SetTargetFramework",
    "AdditionalProperties",
    "Targets",
    "OutputItemType",
    "ReferenceOutputAssembly",
    "Private",
    "PrivateAssets",
    "ExcludeAssets",
    "IncludeAssets",
    "GlobalPropertiesToRemove",
    "SkipGetTargetFrameworkProperties",
];

/// A value for reference metadata `name` a build takes.
fn metadata_value(name: &str) -> &'static str {
    match name {
        "SetConfiguration" => "Configuration=Release",
        "SetTargetFramework" => "TargetFramework=net10.0",
        "AdditionalProperties" => "AssemblyName=Evil",
        "Targets" => "Build",
        "OutputItemType" => "Compile",
        "ReferenceOutputAssembly" => "false",
        "Private" => "false",
        "PrivateAssets" | "ExcludeAssets" | "IncludeAssets" => "compile",
        "GlobalPropertiesToRemove" => "Configuration",
        _ => "true",
    }
}

/// Every case, the must points first.
fn trees() -> Vec<Tree> {
    let mut trees = Vec::new();
    for (shape, projects, referenced) in shapes() {
        let refs = |configuration: &str, renamed: Option<&str>| -> BTreeSet<String> {
            referenced
                .iter()
                .map(|dir| {
                    let name = match renamed {
                        Some(name) if *dir == "L" => name,
                        _ => dir,
                    };
                    ref_path(dir, configuration, name)
                })
                .collect()
        };
        trees.push(Tree {
            label: format!("{shape} plain"),
            projects: projects.clone(),
            globals: vec![],
            must_commit: Some(("P".into(), refs("Debug", None))),
            must_decline: false,
        });
        let mut renamed = projects.clone();
        renamed[1].body = "<AssemblyName>Friend</AssemblyName>".into();
        trees.push(Tree {
            label: format!("{shape} L renamed"),
            projects: renamed,
            globals: vec![],
            must_commit: Some(("P".into(), refs("Debug", Some("Friend")))),
            must_decline: false,
        });
        trees.push(Tree {
            label: format!("{shape} Release"),
            projects: projects.clone(),
            globals: vec![("Configuration", "Release")],
            must_commit: Some(("P".into(), refs("Release", None))),
            must_decline: false,
        });
        // The globals the LSP evaluates under.
        trees.push(Tree {
            label: format!("{shape} under the LSP's globals"),
            projects: projects.clone(),
            globals: vec![("Configuration", "Debug"), ("Platform", "AnyCPU")],
            must_commit: Some(("P".into(), refs("Debug", None))),
            must_decline: false,
        });
    }
    // A referenced C# project: outside the domain, or its reference assembly
    // where the build hands it over.
    let mut csharp = shapes().remove(0).1;
    csharp[1].language = Language::CSharp;
    trees.push(Tree {
        label: "pair L is C#".into(),
        projects: csharp,
        globals: vec![],
        must_commit: None,
        must_decline: false,
    });
    let pair = || shapes().remove(0).1;
    // Metadata on the reference, every way it can be set.
    for name in REFERENCE_METADATA {
        let value = metadata_value(name);
        for way in ["attribute", "child", "definition"] {
            let mut projects = pair();
            match way {
                "attribute" => projects[0].reference_attributes = format!(" {name}=\"{value}\""),
                "child" => projects[0].reference_children = format!("<{name}>{value}</{name}>"),
                _ => {
                    projects[0].after = format!(
                        "<ItemDefinitionGroup><ProjectReference><{name}>{value}</{name}></ProjectReference></ItemDefinitionGroup>"
                    )
                }
            }
            trees.push(Tree {
                label: format!("pair {name} as {way}"),
                projects,
                globals: vec![],
                must_commit: None,
                must_decline: true,
            });
        }
    }
    // A referenced project that lists target frameworks, alone or beside
    // its `TargetFramework`: NuGet's nearest framework is not modelled.
    for (frameworks, alone) in [
        ("net10.0;net9.0", true),
        ("net10.0", true),
        ("net10.0", false),
    ] {
        let mut projects = pair();
        if alone {
            projects[1].frameworks = Some(frameworks.to_string());
        } else {
            projects[1].body = format!("<TargetFrameworks>{frameworks}</TargetFrameworks>");
        }
        trees.push(Tree {
            label: format!("pair L targets {frameworks:?} (alone {alone})"),
            projects,
            globals: vec![],
            must_commit: None,
            must_decline: true,
        });
    }
    // Properties off the lists that move the references.
    for (at, body) in [
        (
            0,
            "<DisableTransitiveProjectReferences>true</DisableTransitiveProjectReferences>",
        ),
        (
            1,
            "<ProduceReferenceAssembly>false</ProduceReferenceAssembly>",
        ),
    ] {
        let mut projects = shapes().remove(1).1;
        projects[at].body = body.into();
        trees.push(Tree {
            label: format!("chain {body}"),
            projects,
            globals: vec![],
            must_commit: None,
            must_decline: true,
        });
    }
    // A cycle, and a reference to a project that is not there.
    let mut cycle = pair();
    cycle[1].references = vec![0];
    trees.push(Tree {
        label: "pair cycle".into(),
        projects: cycle,
        globals: vec![],
        must_commit: None,
        must_decline: true,
    });
    let mut missing = pair();
    missing[1].dir = "Elsewhere".into();
    missing[0].references = vec![];
    missing[0].reference_children = String::new();
    missing[0].after =
        "<ItemGroup><ProjectReference Include=\"../Missing/Missing.fsproj\" /></ItemGroup>".into();
    trees.push(Tree {
        label: "pair missing reference".into(),
        projects: missing,
        globals: vec![],
        must_commit: None,
        must_decline: true,
    });
    // Each allowed property, in each project of a chain, at each value.
    for (name, grammar) in ALLOWED_PROPERTIES {
        for at in 0..3 {
            for value in VALUES.iter().copied().chain([plain_value(name, *grammar)]) {
                let mut projects = shapes().remove(1).1;
                projects[at].body = format!("<{name}>{}</{name}>", xml(value));
                trees.push(Tree {
                    label: format!("chain {} {name} = {value:?}", projects[at].dir),
                    projects,
                    globals: vec![],
                    must_commit: None,
                    must_decline: false,
                });
            }
        }
    }
    trees
}

/// `value` escaped for XML text or an attribute.
fn xml(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\n', "&#10;")
        .replace('\r', "&#13;")
}

/// `value` escaped for an item spec: MSBuild's special characters as `%XX`,
/// then for XML.
fn item_spec(value: &str) -> String {
    let mut out = String::new();
    for c in value.chars() {
        match c {
            '%' | ';' | '*' | '?' | '@' | '$' | '\'' | '(' | ')' => {
                out.push_str(&format!("%{:02X}", c as u32))
            }
            c => out.push(c),
        }
    }
    xml(&out)
}

/// Lay `tree` out under `root`; the referencing project's file, or `None`
/// when a directory cannot be made.
fn lay_out(tree: &Tree, root: &Path) -> Option<PathBuf> {
    for project in &tree.projects {
        let dir = root.join(&project.dir);
        if std::fs::create_dir_all(&dir).is_err() {
            return None;
        }
        let (source, text, extension) = match project.language {
            Language::FSharp => (
                format!("{}.fs", project.stem),
                format!("module {}\nlet x = 1\n", project.stem),
                "fsproj",
            ),
            Language::CSharp => (
                format!("{}.cs", project.stem),
                format!(
                    "namespace {0} {{ public static class C {{ public const int X = 1; }} }}\n",
                    project.stem
                ),
                "csproj",
            ),
        };
        std::fs::write(dir.join(&source), text).unwrap();
        let references: String = project
            .references
            .iter()
            .map(|&i| {
                let target = &tree.projects[i];
                format!(
                    "<ProjectReference Include=\"../{}/{}.{}\"{}>{}</ProjectReference>",
                    item_spec(&target.dir),
                    target.stem,
                    match target.language {
                        Language::FSharp => "fsproj",
                        Language::CSharp => "csproj",
                    },
                    project.reference_attributes,
                    project.reference_children
                )
            })
            .collect();
        // A C# project compiles its directory's sources by default.
        let compile = match project.language {
            Language::FSharp => format!("<Compile Include=\"{source}\" />"),
            Language::CSharp => String::new(),
        };
        std::fs::write(
            dir.join(format!("{}.{extension}", project.stem)),
            format!(
                "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>{}{}</PropertyGroup>\
                 <ItemGroup>{compile}{references}</ItemGroup>{}</Project>",
                match &project.frameworks {
                    Some(frameworks) =>
                        format!("<TargetFrameworks>{frameworks}</TargetFrameworks>"),
                    None => "<TargetFramework>net10.0</TargetFramework>".to_string(),
                },
                project.body,
                project.after
            ),
        )
        .unwrap();
    }
    let first = &tree.projects[0];
    Some(root.join(&first.dir).join(format!("{}.fsproj", first.stem)))
}

/// The build's inputs for `tree`.
fn inputs(tree: &Tree) -> BuildInputs {
    tree.globals
        .iter()
        .fold(BuildInputs::new(), |inputs, (name, value)| {
            inputs
                .global(name, value)
                .expect("a global the oracle takes")
        })
}

/// Restore the project at `project` in place under `inputs`, as the build
/// would; its references restore with it.
fn restore(project: &Path, inputs: &BuildInputs) {
    let mut cmd = std::process::Command::new("dotnet");
    cmd.current_dir(project.parent().unwrap())
        .args(["msbuild", "-nodeReuse:false", "-t:Restore"]);
    for (name, value) in inputs.globals() {
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(project).env_clear().envs(build_environment());
    cmd.envs(inputs.env_vars());
    BoundedCommand::new(cmd)
        .timeout(std::time::Duration::from_secs(900))
        .run()
        .unwrap_or_else(|e| panic!("restoring {}: {e}", project.display()));
}

/// What the derivation certifies for the project at `project` under
/// `inputs`.
fn ours(project: &Path, inputs: &BuildInputs) -> Result<Certified, String> {
    let globals: HashMap<String, String> = inputs
        .globals()
        .map(|(n, v)| (n.to_string(), v.to_string()))
        .collect();
    let mut environment: HashMap<String, String> = build_environment().into_iter().collect();
    environment.insert(
        "MSBuildUserExtensionsPath".to_string(),
        common::msbuild_user_extensions_path().to_string(),
    );
    environment.extend(inputs.env_vars());
    assembly_name::certify(
        project,
        &globals,
        &environment,
        &common::dotnet_root_from_env(),
        Sdks::Resolved,
    )
    .map_err(|decline| format!("{decline:?}"))
}

/// What one case came to.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Outcome {
    /// A directory of the tree cannot be made.
    Unmakeable,
    /// We declined, for this reason.
    Declined(String),
    /// We committed, and the build agreed.
    Agreed,
    /// We committed, and the oracle could not vouch for a compile.
    Unanswered,
}

/// Grade `tree`; `Err` with a failure message on a wrong commit or a missed
/// must.
fn grade(tree: &Tree) -> Result<Outcome, String> {
    let tmp = tempfile::TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap().join("tree");
    std::fs::create_dir(&root).unwrap();
    let Some(project) = lay_out(tree, &root) else {
        return Ok(Outcome::Unmakeable);
    };
    let inputs = inputs(tree);
    restore(&project, &inputs);
    let certified = match ours(&project, &inputs) {
        Ok(certified) => certified,
        Err(why) => {
            return match &tree.must_commit {
                Some(_) => Err(format!("{}: declined ({why}), must commit", tree.label)),
                None => Ok(Outcome::Declined(
                    why.split('(').next().unwrap_or_default().to_string(),
                )),
            };
        }
    };
    let under_root = |path: &Path| {
        path.strip_prefix(&root)
            .ok()
            .map(|p| p.to_string_lossy().into_owned())
    };
    let ours_refs: BTreeSet<String> = certified
        .project_references
        .iter()
        .map(|p| under_root(p).unwrap_or_else(|| p.display().to_string()))
        .collect();
    if tree.must_decline {
        return Err(format!(
            "{}: committed {:?} with {ours_refs:?}, must decline",
            tree.label, certified.name
        ));
    }
    if let Some((name, refs)) = &tree.must_commit
        && (name != &certified.name || refs != &ours_refs)
    {
        return Err(format!(
            "{}: committed {:?} with {ours_refs:?}, must commit {name:?} with {refs:?}",
            tree.label, certified.name
        ));
    }
    match fsc_args(&FscArgsRequest {
        project: &project,
        inputs: &inputs,
    }) {
        Ok(build) => {
            if tree.must_commit.is_some() && !build.succeeded {
                return Err(format!("{}: committed, but the build failed", tree.label));
            }
            for invocation in &build.invocations {
                let args = invocation
                    .arguments()
                    .map_err(|e| format!("{}: unreadable arguments {e:?}", tree.label))?;
                let theirs_refs: BTreeSet<String> = args
                    .references
                    .iter()
                    .filter_map(|r| under_root(Path::new(r)))
                    .collect();
                if args.assembly_name().as_deref() != Some(certified.name.as_str())
                    || theirs_refs != ours_refs
                {
                    return Err(format!(
                        "{}: WRONG COMMIT: we say {:?} with {ours_refs:?}; fsc is handed {:?} with {theirs_refs:?}\n{}",
                        tree.label,
                        certified.name,
                        args.assembly_name(),
                        invocation.response_file
                    ));
                }
            }
            Ok(Outcome::Agreed)
        }
        Err(decline) if tree.must_commit.is_some() => Err(format!(
            "{}: committed, but the oracle did not answer: {decline:?}",
            tree.label
        )),
        Err(FscArgsDecline::NoBuild(why) | FscArgsDecline::Unanswered(why)) => {
            eprintln!(
                "unanswered: {}: {}",
                tree.label,
                why.first()
                    .and_then(|w| w.lines().next())
                    .unwrap_or_default()
            );
            Ok(Outcome::Unanswered)
        }
    }
}

/// Grade `trees` on a few threads; the census, and every failure.
fn grade_all(trees: &[Tree]) -> (BTreeMap<Outcome, usize>, Vec<String>) {
    let next = AtomicUsize::new(0);
    let results = Mutex::new((BTreeMap::new(), Vec::new()));
    std::thread::scope(|scope| {
        let threads: usize = std::env::var("BORZOI_FSC_NAME_THREADS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(4);
        for _ in 0..threads.max(1) {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(tree) = trees.get(i) else { break };
                    let graded = grade(tree);
                    let mut results = results.lock().unwrap();
                    match graded {
                        Ok(outcome) => *results.0.entry(outcome).or_insert(0) += 1,
                        Err(failure) => results.1.push(failure),
                    }
                }
            });
        }
    });
    results.into_inner().unwrap()
}

fn run(trees: &[Tree]) {
    let (census, failures) = grade_all(trees);
    eprintln!("{} trees:", trees.len());
    for (outcome, count) in &census {
        eprintln!("  {outcome:?}: {count}");
    }
    assert!(
        failures.is_empty(),
        "{} of {} trees failed:\n{}",
        failures.len(),
        trees.len(),
        failures.join("\n")
    );
}

#[test]
fn certified_references_survive_perturbation() {
    let seed = std::env::var("BORZOI_FSC_TREE_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x1065_7ee5);
    let sample: usize = std::env::var("BORZOI_FSC_TREE_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(16);
    eprintln!(
        "seed {seed:#x}, {sample} sampled trees (BORZOI_FSC_TREE_SEED, BORZOI_FSC_TREE_CASES)"
    );
    let mut rng = SplitMix64(seed);
    let (mut chosen, mut rest): (Vec<Tree>, Vec<Tree>) = trees()
        .into_iter()
        .partition(|t| t.must_commit.is_some() || t.must_decline);
    for _ in 0..sample.min(rest.len()) {
        let i = rng.below(rest.len());
        chosen.push(rest.swap_remove(i));
    }
    run(&chosen);
}

#[test]
#[ignore = "every tree: about seven hundred, each a restore and most a build"]
fn deep_every_tree() {
    run(&trees());
}

/// Every hostile file name (`hostile::name`) as the referenced project's
/// directory in a pair, recording what became of each dimension in the
/// census `project_reference_directories`. The reference names it as an
/// item spec, MSBuild's special characters escaped.
#[test]
#[ignore = "every hostile name as a referenced project's directory: one build each that commits"]
fn deep_hostile_directories() {
    let census = coverage::open(
        file!(),
        "project_reference_directories",
        &[(
            Dimension::NonUtf8,
            "the derivation takes paths as UTF-8 text, as its caller reads them",
        )],
    );
    let mut cases = Vec::new();
    for entry in hostile_name::alphabet().entries() {
        let rendered = entry.value.render("Lib", "");
        let Some(dir) = rendered.component().ok().and_then(|c| c.to_str()) else {
            continue;
        };
        let mut projects = shapes().remove(0).1;
        projects[1].dir = dir.to_string();
        cases.push((
            Tree {
                label: format!("pair L in {dir:?}"),
                projects,
                globals: vec![],
                must_commit: None,
                must_decline: false,
            },
            entry.dimension,
        ));
    }
    let plain = trees()
        .into_iter()
        .find(|t| t.must_commit.is_some())
        .unwrap();
    let mut failures = Vec::new();
    match grade(&plain) {
        Ok(outcome) => census.reached(&BTreeSet::new(), &format!("{outcome:?}")),
        Err(failure) => failures.push(failure),
    }
    for (tree, dimension) in cases {
        match grade(&tree) {
            Ok(outcome) => {
                let outcome = format!("{outcome:?}");
                census.reached(
                    &BTreeSet::from([dimension]),
                    outcome.split('(').next().unwrap_or_default(),
                );
            }
            Err(failure) => failures.push(failure),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
         --test fsproj_project_reference_name_diff deep_hostile_directories -- --ignored",
    );
}

/// An evaluation whose `ProjectReference` items the walk is not certain of
/// (an `Update` it does not model) declines, whatever the caller hands for
/// the projects: even with none listed, the list may be short of one the
/// build has.
#[test]
fn an_uncertain_reference_list_declines_whatever_is_handed() {
    let tmp = tempfile::TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap().join("tree");
    std::fs::create_dir(&root).unwrap();
    let mut projects = shapes().remove(0).1;
    projects[0].references = vec![];
    projects[0].after =
        "<ItemGroup><ProjectReference Update=\"../L/L.fsproj\" /></ItemGroup>".into();
    let tree = Tree {
        label: "update only".into(),
        projects,
        globals: vec![],
        must_commit: None,
        must_decline: true,
    };
    let project = lay_out(&tree, &root).unwrap();
    let inputs = inputs(&tree);
    restore(&project, &inputs);
    let globals = HashMap::new();
    let mut environment: HashMap<String, String> = build_environment().into_iter().collect();
    environment.insert(
        "MSBuildUserExtensionsPath".to_string(),
        common::msbuild_user_extensions_path().to_string(),
    );
    let parsed = assembly_name::evaluate(
        &project,
        &globals,
        &environment,
        &common::dotnet_root_from_env(),
    )
    .unwrap();
    assert!(
        parsed.project_references_uncertain && parsed.project_references.is_empty(),
        "the case's premise: no item, and the walk not certain of that"
    );
    let (files, references, content) = assembly_name::gathered(&project, &parsed);
    let sdk = borzoi_msbuild::fsc::resolved_sdk_version(&parsed).unwrap();
    for handed in [
        borzoi_msbuild::fsc::ProjectReferences::Unread,
        borzoi_msbuild::fsc::ProjectReferences::Listed(vec![]),
    ] {
        let verdict = borzoi_msbuild::test_support::certified_compilation_grading(
            &sdk,
            &project,
            &parsed,
            &borzoi_msbuild::fsc::NameInputs {
                environment: &environment,
                globals: &globals,
                files: &files,
                references: &references,
                content: &content,
                project_references: &handed,
            },
        );
        assert!(
            matches!(
                &verdict,
                Err(borzoi_msbuild::fsc::NameDecline::ProjectReference(why)) if why.contains("not certain")
            ),
            "{handed:?}: {verdict:?}"
        );
    }
}

/// The globals a referenced project is evaluated under are the build's but
/// those the reference's protocol removes.
#[test]
fn reference_globals_drop_the_target() {
    let globals: HashMap<String, String> = [
        ("Configuration", "Release"),
        ("targetframework", "net10.0"),
        ("RuntimeIdentifier", "osx-arm64"),
        ("SelfContained", "true"),
    ]
    .into_iter()
    .map(|(n, v)| (n.to_string(), v.to_string()))
    .collect();
    let kept = borzoi_msbuild::fsc::reference_globals(&globals);
    assert_eq!(
        kept,
        HashMap::from([("Configuration".to_string(), "Release".to_string())])
    );
}
