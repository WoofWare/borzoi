//! How much of a real corpus [`borzoi_msbuild::fsc::compiled_assembly_name`]
//! commits for, and why it declines the rest: a report, not a gate.
//!
//! Every `.fsproj` under the directories `BORZOI_FSC_NAME_CENSUS_ROOTS`
//! (colon-separated; `bin/`, `obj/` and hidden directories skipped) is
//! evaluated as the LSP evaluates it (`Configuration=Debug`,
//! `Platform=AnyCPU`, `MSBuildUserExtensionsPath` seeded), under this
//! process's environment, as the LSP would run, and under the build's own
//! environment alone (`build_environment`). Printed:
//!
//! - each project's verdict under both;
//! - the census by the derivation's first decline cause, per environment;
//! - the census by *blocking fact*: every domain rule a project breaks that
//!   its evaluation shows (names off the lists, conditions, expansions, build
//!   code, values outside their grammars, response files, ungraded SDKs and
//!   manifests, …), counted once per project whatever the derivation's order,
//!   with the names off each list, and the derivation's own first decline
//!   beside them. This is the one that says what would have to change for
//!   the project to commit. The gates on the caller's inputs (the default
//!   item files, the reference set, the content files) show only as a first
//!   decline.
//!
//! ```sh
//! BORZOI_FSC_NAME_CENSUS_ROOTS=~/.cache/borzoi/project-corpus/v2/project-corpus:$BORZOI_CORPUS \
//! nix develop -c cargo test -p borzoi-msbuild --test fsc_name_census -- --ignored --nocapture
//! ```

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use borzoi_msbuild::AutoResponseFile;
use borzoi_msbuild::fsc::{
    ALLOWED_ITEM_TYPES, ALLOWED_METADATA, ALLOWED_PROPERTIES, BUILD_TIME_SITES,
    CompiledAssemblyName, Gate, NameDecline, RESTORE_ITEM_TYPES, RESTORE_METADATA,
    RESTORE_PROPERTIES, RESTORE_PROPERTY_PREFIX, classify_variable, environment_declines,
    resolved_sdk_version, restore_props, verified_manifests, verified_sdks,
};
use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::{ParsedProject, PropertyRead};
use borzoi_oracle_harness::msbuild_oracle::build_environment;
use common::assembly_name::{Sdks, derive_from, evaluate};

/// Every `.fsproj` under `dir`, but in `bin/`, `obj/` and hidden directories,
/// and behind a directory symlink (which could count a project twice, or
/// loop).
fn projects(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = host_fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        let Ok(kind) = host_fs::symlink_metadata(&path).map(|m| m.file_type()) else {
            continue;
        };
        if kind.is_symlink() {
            continue;
        }
        if kind.is_dir() {
            if !(name.starts_with('.')
                || name.eq_ignore_ascii_case("bin")
                || name.eq_ignore_ascii_case("obj"))
            {
                projects(&path, out);
            }
        } else if kind.is_file() && name.to_ascii_lowercase().ends_with(".fsproj") {
            out.push(path);
        }
    }
}

/// The cause a verdict counts under: `Known`, or the decline's variant.
fn cause(verdict: &CompiledAssemblyName) -> String {
    match verdict {
        CompiledAssemblyName::Known(_) => "Known".to_string(),
        CompiledAssemblyName::Unknown(why) => format!("{why:?}")
            .split('(')
            .next()
            .unwrap_or_default()
            .to_string(),
    }
}

fn on_list<'a>(list: impl IntoIterator<Item = &'a str>, name: &str) -> bool {
    list.into_iter().any(|n| n.eq_ignore_ascii_case(name))
}

/// Every domain rule the evaluation `parsed` of `project`, under
/// `environment`, breaks: `(rule, detail)`, the detail a name off a list or
/// empty.
fn blocking_facts(
    project: &Path,
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
) -> BTreeSet<(String, String)> {
    let mut facts = BTreeSet::new();
    let mut fact = |rule: &str, detail: &str| {
        facts.insert((rule.to_string(), detail.to_string()));
    };
    let restore = restore_props(project);
    let restore_targets = restore.as_deref().map(|p| p.with_extension("targets"));
    let is_restore_file =
        |file: &Path| Some(file) == restore.as_deref() || Some(file) == restore_targets.as_deref();
    // Names: from NuGet's props alone, as the derivation admits them.
    let only_restore = |files: &BTreeSet<PathBuf>| {
        files
            .iter()
            .all(|f| Some(f.as_path()) == restore.as_deref())
    };
    if !matches!(parsed.property("RestoreSuccess"), PropertyRead::Value(v) if v.eq_ignore_ascii_case("true"))
    {
        fact("unrestored", "");
    }
    if parsed.hidden_content.is_some() {
        fact("hidden content", "");
    }
    if parsed.is_outer_build() != Some(false) {
        fact("multi-targeting (outer build)", "");
    }
    let foreign = &parsed.foreign_definitions;
    if foreign.defines_build_code() || !foreign.build_time_properties.is_empty() {
        fact("build code outside the install", "");
    }
    if foreign.conditioned.iter().any(|f| !is_restore_file(f)) {
        fact("condition outside the install (#993)", "");
    }
    if foreign.expanding.iter().any(|f| !is_restore_file(f)) {
        fact("expansion outside the install (#1060)", "");
    }
    if !foreign.unlike_nuget.is_empty() && (foreign.unlike_nuget.iter().any(|f| is_restore_file(f)))
    {
        fact("restore file not as NuGet writes it", "");
    }
    if !foreign.globbing.is_empty() {
        fact("item wildcard outside the install", "");
    }
    for name in parsed.foreign_write_failures.keys() {
        fact("value outside its grammar", name);
    }
    if parsed.auto_response_file != AutoResponseFile::Absent {
        fact("response file", "");
    }
    if !parsed.workload_manifests_outside_install.is_empty() {
        fact("workload manifest outside the install", "");
    }
    if let Some(sdk) = resolved_sdk_version(parsed) {
        if !verified_sdks().any(|v| v == sdk) {
            fact("SDK not graded", &sdk);
        }
        for manifest in &parsed.workload_manifest_files {
            if !verified_manifests(&sdk).any(|m| m == manifest) {
                fact("workload manifest not graded", manifest);
            }
        }
    } else {
        fact("no canonical SDK resolved", "");
    }
    for site in BUILD_TIME_SITES
        .iter()
        .filter(|s| s.gate == Gate::NotImported)
    {
        if parsed.imported_sdk_files.contains(Path::new(site.file)) {
            fact("an SDK file the register holds unreached", site.file);
        }
    }
    if project.to_string_lossy().chars().any(char::is_control) {
        fact("control character in the project path", "");
    }
    for (name, files) in &foreign.properties {
        let restore_written = (on_list(RESTORE_PROPERTIES.iter().map(|(n, _)| *n), name)
            || name
                .to_ascii_lowercase()
                .starts_with(&RESTORE_PROPERTY_PREFIX.to_ascii_lowercase()))
            && only_restore(files);
        if !on_list(ALLOWED_PROPERTIES.iter().map(|(n, _)| *n), name) && !restore_written {
            fact("property off the list", name);
        }
    }
    for (name, files) in &foreign.items {
        let restore_written =
            on_list(RESTORE_ITEM_TYPES.iter().copied(), name) && only_restore(files);
        if !on_list(ALLOWED_ITEM_TYPES.iter().copied(), name) && !restore_written {
            if name.eq_ignore_ascii_case("ProjectReference") {
                fact("ProjectReference", "");
            } else {
                fact("item type off the list", name);
            }
        }
    }
    for (name, files) in &foreign.item_metadata {
        let restore_written =
            on_list(RESTORE_METADATA.iter().copied(), name) && only_restore(files);
        if !on_list(ALLOWED_METADATA.iter().copied(), name) && !restore_written {
            fact("metadata off the list", name);
        }
    }
    for name in environment.keys() {
        if !classify_variable(name).admitted() {
            fact("environment variable off the list", name);
        }
    }
    // The environment's other rules, under the SDK the evaluation resolved:
    // a toolchain value off its shape, two names of one property.
    if let Some(sdk) = resolved_sdk_version(parsed) {
        for decline in environment_declines(&sdk, environment) {
            match decline {
                NameDecline::Environment(why) if why.contains(": a value not of the shape") => {
                    fact("environment variable value off its shape", &why);
                }
                NameDecline::Environment(why) if why.ends_with("name one property") => {
                    fact("environment variables naming one property", &why);
                }
                NameDecline::UnscannedSdk(sdk) => {
                    fact("environment reads not pinned for the SDK", &sdk);
                }
                _ => {}
            }
        }
    }
    // A package's own build files: documents outside the install under the
    // restore's package folder.
    if let PropertyRead::Value(root) = parsed.property("NuGetPackageRoot") {
        let root = PathBuf::from(root);
        let documents = foreign
            .properties
            .values()
            .chain(foreign.items.values())
            .chain(foreign.item_metadata.values())
            .flatten()
            .chain(&foreign.conditioned)
            .chain(&foreign.expanding);
        for document in documents {
            if !root.as_os_str().is_empty() && document.starts_with(&root) {
                fact("package build files", "");
            }
        }
    }
    facts
}

#[test]
#[ignore = "a report over a corpus named by BORZOI_FSC_NAME_CENSUS_ROOTS"]
fn census() {
    let roots = std::env::var("BORZOI_FSC_NAME_CENSUS_ROOTS")
        .expect("BORZOI_FSC_NAME_CENSUS_ROOTS names the directories to walk");
    let mut all = Vec::new();
    for root in roots.split(':').filter(|r| !r.is_empty()) {
        let before = all.len();
        projects(Path::new(root), &mut all);
        eprintln!("{root}: {} projects", all.len() - before);
    }
    all.sort();
    let globals: HashMap<String, String> = [("Configuration", "Debug"), ("Platform", "AnyCPU")]
        .into_iter()
        .map(|(n, v)| (n.to_string(), v.to_string()))
        .collect();
    // MSBuild's own default for `MSBuildUserExtensionsPath`, unless the
    // environment spells the variable (in any case), which then chooses
    // which user extension files MSBuild imports.
    let seeded = |mut env: HashMap<String, String>| {
        if !env
            .keys()
            .any(|name| name.eq_ignore_ascii_case("MSBuildUserExtensionsPath"))
        {
            env.insert(
                "MSBuildUserExtensionsPath".to_string(),
                common::msbuild_user_extensions_path().to_string(),
            );
        }
        env
    };
    let columns = [
        // The census's own selector is the measurement's, not the
        // environment's.
        (
            "process env",
            seeded(
                std::env::vars()
                    .filter(|(name, _)| name != "BORZOI_FSC_NAME_CENSUS_ROOTS")
                    .collect(),
            ),
        ),
        (
            "build env",
            seeded(build_environment().into_iter().collect()),
        ),
    ];
    let dotnet_root = common::dotnet_root_from_env();
    let mut first_cause: BTreeMap<(&str, String), usize> = BTreeMap::new();
    let mut facts_census: BTreeMap<(&str, String), usize> = BTreeMap::new();
    let mut names: BTreeMap<(&str, String, String), usize> = BTreeMap::new();
    for project in &all {
        let restored = project
            .with_file_name("obj")
            .join("project.assets.json")
            .host_exists();
        let mut line = format!("{}\trestored={restored}", project.display());
        for (column, environment) in &columns {
            let (verdict, facts) = match evaluate(project, &globals, environment, &dotnet_root) {
                Ok(parsed) => (
                    derive_from(project, &parsed, &globals, environment, Sdks::Verified),
                    blocking_facts(project, &parsed, environment),
                ),
                Err(e) => (
                    CompiledAssemblyName::Unknown(borzoi_msbuild::fsc::NameDecline::Property(
                        format!("our evaluation failed: {e}"),
                    )),
                    BTreeSet::from([("evaluation failed".to_string(), String::new())]),
                ),
            };
            line.push_str(&format!("\t{column}: {verdict:?}"));
            // The derivation's own first cause is a fact too, so a gate the
            // fact scan cannot see (a response file, a value outside its
            // grammar) still shows.
            let mut facts = facts;
            if let CompiledAssemblyName::Unknown(_) = &verdict {
                facts.insert((format!("decline: {}", cause(&verdict)), String::new()));
            }
            *first_cause.entry((column, cause(&verdict))).or_default() += 1;
            let rules: BTreeSet<&String> = facts.iter().map(|(rule, _)| rule).collect();
            for rule in rules {
                *facts_census.entry((column, rule.clone())).or_default() += 1;
            }
            for (rule, detail) in facts.iter().filter(|(_, d)| !d.is_empty()) {
                *names
                    .entry((column, rule.clone(), detail.clone()))
                    .or_default() += 1;
            }
        }
        eprintln!("{line}");
    }
    eprintln!("{} projects; by the derivation's first cause:", all.len());
    for ((column, cause), count) in &first_cause {
        eprintln!("  {column}\t{cause}\t{count}");
    }
    eprintln!("by blocking fact (projects breaking each rule):");
    for ((column, rule), count) in &facts_census {
        eprintln!("  {column}\t{rule}\t{count}");
    }
    eprintln!("names off a list (projects naming each):");
    for ((column, rule, name), count) in &names {
        eprintln!("  {column}\t{rule}\t{name}\t{count}");
    }
}
