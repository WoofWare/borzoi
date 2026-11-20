//! [`borzoi_msbuild::fsc::compiled_assembly_name`] on a project on disk, with
//! its inputs gathered as the LSP would: the evaluation, the default item
//! files, and the restored assets file's package references and content
//! files. Shared by the derivation's grader and its corpus census.

use std::collections::HashMap;
use std::path::Path;

use borzoi_msbuild::fsc::DefaultItemFiles;
use borzoi_msbuild::fsc::{
    Certified, CompiledAssemblyName, ContentFiles, NameDecline, NameInputs, ProjectReferences,
    ReferencePaths, ReferencedProject, certified_compilation, default_item_files,
    reference_globals, resolved_sdk_version,
};
use borzoi_msbuild::observed::Observer;
use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::certified_compilation_grading;
use borzoi_msbuild::{ParsedProject, PropertyRead, glob_resolver, resolve_sdk, workloads};

/// What the restored assets file `assets` names for the target framework
/// `tfm`: the package compile assets, as absolute paths (the
/// packages' part of the reference set the LSP builds its assembly env from;
/// the targeting pack's lie inside the install, fixed per SDK), and the
/// packages' content files with their build actions. Unread when there is no
/// assets file, it is not a regular file or not JSON, it holds no target for
/// `tfm`, or it names more than one package folder (a fallback folder, whose
/// choice among the folders this does not model). A project library (a
/// referenced project) is not a package: its assets are the derivation's to
/// certify through the reference ([`ProjectReferences`]).
pub fn package_assets(assets: &Path, tfm: &str) -> (ReferencePaths, ContentFiles) {
    let unread = (ReferencePaths::Unread, ContentFiles::Unread);
    if !assets.host_is_file() {
        return unread;
    }
    let Ok(text) = host_fs::read_to_string(assets) else {
        return unread;
    };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else {
        return unread;
    };
    let Some(folder) = json["packageFolders"]
        .as_object()
        .filter(|folders| folders.len() == 1)
        .and_then(|folders| folders.keys().next())
    else {
        return unread;
    };
    let Some(target) = json["targets"][tfm].as_object() else {
        return (ReferencePaths::Unread, ContentFiles::Unread);
    };
    let mut paths = Vec::new();
    let mut content = Vec::new();
    for (library, target) in target {
        if json["libraries"][library]["type"].as_str() == Some("project") {
            continue;
        }
        let Some(path) = json["libraries"][library]["path"].as_str() else {
            continue;
        };
        for asset in target["compile"]
            .as_object()
            .into_iter()
            .flatten()
            .map(|(k, _)| k)
        {
            if !asset.ends_with("/_._") {
                paths.push(Path::new(folder).join(path).join(asset));
            }
        }
        for (file, entry) in target["contentFiles"].as_object().into_iter().flatten() {
            let action = entry["buildAction"]
                .as_str()
                .unwrap_or_default()
                .to_string();
            content.push((file.clone(), action));
        }
    }
    (ReferencePaths::Listed(paths), ContentFiles::Listed(content))
}

/// Which SDKs the derivation commits for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sdks {
    /// The one the evaluation resolved, as the grader grades it.
    Resolved,
    /// Only the verified ones, as a consumer gets it.
    Verified,
}

/// The derivation's verdict on the project at `project`, evaluated under
/// `globals` and `environment` with SDKs resolved from the .NET install at
/// `dotnet_root`.
pub fn derive(
    project: &Path,
    globals: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    dotnet_root: &Path,
    sdks: Sdks,
) -> CompiledAssemblyName {
    match evaluate(project, globals, environment, dotnet_root) {
        Ok(parsed) => derive_from(project, &parsed, globals, environment, dotnet_root, sdks),
        // MSBuild rejects it too, so there is nothing to name.
        Err(e) => CompiledAssemblyName::Unknown(NameDecline::Property(format!(
            "our evaluation failed: {e}"
        ))),
    }
}

/// The evaluation of the project at `project` under `globals` and
/// `environment`, with SDKs resolved from the .NET install at `dotnet_root`.
/// `Err` for a project file that is not a regular file, and for one under a
/// `global.json`, whose SDK selection this does not reproduce.
pub fn evaluate(
    project: &Path,
    globals: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    dotnet_root: &Path,
) -> Result<ParsedProject, String> {
    if !project.host_is_file() {
        return Err("not a regular file".to_string());
    }
    if let Some(global_json) = project
        .ancestors()
        .skip(1)
        .map(|dir| dir.join("global.json"))
        .find(|file| file.host_exists())
    {
        return Err(format!(
            "{} selects the SDK, which this does not reproduce",
            global_json.display()
        ));
    }
    // The workload context of a build under exactly `environment`.
    let (user_dotnet_root, overrides_present) = super::workload_env_from(environment);
    let resolver = |name: &str, observer: &Observer| {
        resolve_sdk(
            dotnet_root,
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: user_dotnet_root.as_deref(),
                overrides_present,
                global_json: Default::default(),
                process_architecture: None,
            },
            observer,
        )
    };
    let source = host_fs::read_to_string(project).map_err(|e| e.to_string())?;
    let file =
        borzoi_msbuild::ProjectFile::buffer(project, source).map_err(|e| format!("{e:?}"))?;
    super::parse_fsproj_with_imports(
        &file,
        globals,
        environment,
        Some(&resolver as &borzoi_msbuild::SdkResolver<'_>),
        Some(&glob_resolver::resolve as &borzoi_msbuild::GlobResolver<'_>),
    )
    .map_err(|e| e.to_string())
}

/// The derivation's verdict on the project at `project` from its evaluation
/// `parsed`, made under `globals` and `environment`, its referenced projects
/// evaluated from the .NET install at `dotnet_root`.
pub fn derive_from(
    project: &Path,
    parsed: &ParsedProject,
    globals: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    dotnet_root: &Path,
    sdks: Sdks,
) -> CompiledAssemblyName {
    match certify_from(project, parsed, globals, environment, dotnet_root, sdks) {
        Ok(certified) => CompiledAssemblyName::Known(certified.name),
        Err(decline) => CompiledAssemblyName::Unknown(decline),
    }
}

/// What the derivation certifies for the project at `project` (its name and
/// its referenced projects' reference assemblies), from its evaluation
/// `parsed`, made under `globals` and `environment`.
pub fn certify(
    project: &Path,
    globals: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    dotnet_root: &Path,
    sdks: Sdks,
) -> Result<Certified, NameDecline> {
    match evaluate(project, globals, environment, dotnet_root) {
        Ok(parsed) => certify_from(project, &parsed, globals, environment, dotnet_root, sdks),
        Err(e) => Err(NameDecline::Property(format!("our evaluation failed: {e}"))),
    }
}

/// [`certify`] from the evaluation `parsed`.
pub fn certify_from(
    project: &Path,
    parsed: &ParsedProject,
    globals: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    dotnet_root: &Path,
    sdks: Sdks,
) -> Result<Certified, NameDecline> {
    let (files, references, content) = gathered(project, parsed);
    let project_references = referenced_projects(parsed, globals, environment, dotnet_root, 0);
    let inputs = NameInputs {
        environment,
        globals,
        files: &files,
        references: &references,
        content: &content,
        project_references: &project_references,
    };
    match (sdks, resolved_sdk_version(parsed)) {
        (Sdks::Resolved, Some(sdk)) => {
            certified_compilation_grading(&sdk, project, parsed, &inputs)
        }
        _ => certified_compilation(project, parsed, &inputs),
    }
}

/// What the LSP reads beside the evaluation `parsed` of the project at
/// `project`: the default item files, and the reference set and content files
/// of the assets file the evaluation selected (`ProjectAssetsFile`, which
/// only NuGet's restore file may set), or none.
pub fn gathered(
    project: &Path,
    parsed: &ParsedProject,
) -> (DefaultItemFiles, ReferencePaths, ContentFiles) {
    let files = default_item_files(project, &Observer::new());
    let tfm = match parsed.property("TargetFramework") {
        PropertyRead::Value(tfm) => tfm,
        _ => String::new(),
    };
    let (references, content) = match parsed.property("ProjectAssetsFile") {
        PropertyRead::Value(assets) => package_assets(Path::new(&assets), &tfm),
        _ => (ReferencePaths::Unread, ContentFiles::Unread),
    };
    (files, references, content)
}

/// How deep [`referenced_projects`] follows references before it gives up
/// (the derivation declines a cycle; this bounds the walk that would find
/// one).
const REFERENCE_DEPTH: usize = 8;

/// The projects `parsed`'s `ProjectReference` items name, each evaluated
/// under the globals a build under `globals` hands it and the same
/// `environment`, with what the LSP reads beside each, recursively; Unread
/// when one cannot be evaluated or the references run deeper than
/// [`REFERENCE_DEPTH`].
fn referenced_projects(
    parsed: &ParsedProject,
    globals: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    dotnet_root: &Path,
    depth: usize,
) -> ProjectReferences {
    if depth > REFERENCE_DEPTH {
        return ProjectReferences::Unread;
    }
    let globals = reference_globals(globals);
    let mut listed = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for item in &parsed.project_references {
        if !seen.insert(item.include.clone()) {
            continue;
        }
        let Ok(referenced) = evaluate(&item.include, &globals, environment, dotnet_root) else {
            return ProjectReferences::Unread;
        };
        let (files, references, content) = gathered(&item.include, &referenced);
        let project_references =
            referenced_projects(&referenced, &globals, environment, dotnet_root, depth + 1);
        listed.push(ReferencedProject {
            path: item.include.clone(),
            parsed: referenced,
            globals: globals.clone(),
            files,
            references,
            content,
            project_references,
        });
    }
    ProjectReferences::Listed(listed)
}
