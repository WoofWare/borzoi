//! Test-only window onto the private `Condition` evaluator.
//!
//! Gated behind the `test-support` feature (see `Cargo.toml`) so it never
//! widens the crate's runtime public surface. It exists so the differential
//! integration tests (`tests/condition_diff.rs`, `tests/condition_properties.rs`)
//! can fuzz raw condition strings against the *real* MSBuild evaluator via
//! `tools/msbuild-condition-oracle` and assert the "certain-implies-exact"
//! property: whenever our evaluator commits to [`Outcome::True`] or
//! [`Outcome::False`], MSBuild agrees with that exact boolean; when we return
//! [`Outcome::Unsupported`] we make no claim (our conservative fail-safe).
//!
//! Only the pieces the differential needs are re-exported. [`evaluate`] treats
//! a reached `Exists` as [`Outcome::Unsupported`] (no file system);
//! [`evaluate_with_exists`] answers it from the file system, as the walk does.

pub use crate::condition::{Eval, Judgement, MAX_CONDITION_NESTING, Outcome, Throws, evaluate};

/// The condition module's `judge` with no file system: what MSBuild makes of
/// `condition` without the values of the properties `uncertain` names.
pub fn judge(condition: &str, props: &PropertyMap, uncertain: &dyn Fn(&str) -> bool) -> Judgement {
    crate::condition::judge(
        condition,
        props,
        None,
        crate::condition::Site::ItemPass,
        uncertain,
    )
}
pub use crate::properties::MAX_EXPRESSION_NESTING;
pub use crate::properties::escaping::{escape, unescape};
pub use crate::properties::path_fixup::worlds as path_fixup_worlds;
pub use crate::properties::{Issue, PropertyMap};
pub use crate::sdk_resolver::global_json::GLOBAL_JSON_MAX_DEPTH;

/// The walker's hand-rolled stand-in for an SDK `'$(Prop)' == 'true'` gate.
///
/// Exposed because a *reimplementation* of an MSBuild comparison is only as
/// good as the comparison it reproduces, and nothing about its call sites makes
/// that checkable: the walker reaches this predicate exactly when the SDK chain
/// is unavailable, which is exactly when there is no whole-project oracle to
/// diff against. Diffing the predicate itself against MSBuild's `==` is
/// therefore the only route — see `fsproj_directory_build_import_diff.rs`'s
/// `the_gate_predicate_matches_msbuild_equality`.
pub fn is_msbuild_true(value: &str) -> bool {
    crate::evaluator::is_msbuild_true(value)
}

/// Expand a property body and take the result to its **point of use** — i.e.
/// the string MSBuild's `Project.GetPropertyValue` hands back, which is
/// `UnescapeAll` of the value it stored (`ProjectProperty.cs:89`). That is the
/// quantity the `expand` oracle returns, so it is the one the differential
/// compares.
///
/// The escaped domain itself stays crate-private: a differential has no reason
/// to hold a half-evaluated value, and keeping `Escaped` unexported means no
/// consumer outside the evaluator can pick the wrong domain.
pub fn substitute(input: &str, props: &PropertyMap) -> (String, Vec<Issue>) {
    let (value, issues) = crate::properties::substitute(input, props);
    (value.into_ignoring_trust().unescape(), issues)
}

/// Names MSBuild computes for itself as initial properties — the predicate the
/// walker uses to decide that an undefined read of such a name is *not* exact.
///
/// Exposed so the SDK-chain decline attribution can classify blocking names
/// with the *same* rule production uses. A copy in the test would drift, and
/// its first drift is already known: `MSBuildIsRestoring` looks reserved by
/// prefix but is deliberately excluded, because build evaluation genuinely
/// leaves it unset.
pub fn is_toolset_initial_property_name(name: &str) -> bool {
    crate::evaluator::is_toolset_initial_property_name(&name.to_ascii_lowercase())
}

/// Whether MSBuild reserves `name` (case-insensitive): no document or
/// environment variable can set it. Exposed so the LSP's compiler-selector
/// coverage test exempts exactly the names nothing outside the SDK can write.
pub fn is_msbuild_reserved_name(name: &str) -> bool {
    crate::evaluator::is_msbuild_reserved_name(name)
}

/// The names MSBuild reserves, as MSBuild spells them: the list
/// [`is_msbuild_reserved_name`] and the rejection of a caller's reserved extra
/// property both read. Exposed so `tests/reserved_global_diff.rs` can hold it
/// to the installed MSBuild's own table in both directions.
pub const MSBUILD_RESERVED_NAMES: &[&str] = &crate::evaluator::MSBUILD_RESERVED_NAMES;

/// The names the walker takes MSBuild's toolset to define before evaluation
/// starts, lowercase. Exposed so `tests/toolset_predefined_names_diff.rs` can
/// hold the list to MSBuild in both directions.
pub const TOOLSET_PREDEFINED_NAMES: &[&str] = crate::evaluator::TOOLSET_PREDEFINED_NAMES;

/// Every property name `raw` references — the input to every trust scan in the
/// crate, exposed so `tests/property_reference_scan.rs` can hold it to the one
/// obligation that matters: it must never under-report relative to what
/// expansion actually reads.
pub fn property_references(raw: &str) -> Vec<&str> {
    crate::properties::property_references(raw).collect()
}

/// The `VisualStudioVersion` the walk seeds for the SDK in `version_dir`, or
/// `None` where it seeds none. Exposed so
/// `tests/toolset_visual_studio_version_diff.rs` can hold it to each installed
/// SDK's MSBuild.
pub fn toolset_visual_studio_version(version_dir: &std::path::Path) -> Option<&'static str> {
    crate::evaluator::toolset_visual_studio_version(version_dir)
}

/// The `MSBuildAssemblyVersion` the walk seeds for the SDK in `version_dir`,
/// or `None` where it seeds none. Exposed so
/// `tests/toolset_visual_studio_version_diff.rs` can hold it to each installed
/// SDK's MSBuild.
pub fn toolset_assembly_version(version_dir: &std::path::Path) -> Option<&'static str> {
    crate::evaluator::toolset_assembly_version(version_dir)
}

/// The feature band the workload locators take the host SDK `version` to be
/// in (`SdkFeatureBand`), or `None` where they decline. Exposed so
/// `tests/workload_locator_diff.rs` can hold it to the resolver's.
pub fn workload_feature_band(version: &str) -> Option<String> {
    crate::sdk_resolver::workloads::feature_band_of(version)
}

/// Whether the workload locators take `version` as a host SDK version, or
/// decline it. Exposed for the same differential.
pub fn workload_accepts_host_version(version: &str) -> bool {
    crate::sdk_resolver::workloads::accepts_host_version(version)
}

/// The order the workload locators put the feature bands of `a` and `b` in,
/// or `None` where either declines. Exposed for the same differential.
pub fn compare_workload_feature_bands(a: &str, b: &str) -> Option<std::cmp::Ordering> {
    crate::sdk_resolver::workloads::compare_feature_bands(a, b)
}

/// Whether the workload locators pick among manifest version directories
/// named `names` (more than one) rather than decline: each a name whose
/// comparison they certify, and no two tied at the top. Exposed for the same
/// differential.
pub fn workload_manifest_versions_are_told_apart(names: &[&str]) -> bool {
    crate::sdk_resolver::workloads::manifest_versions_are_told_apart(names)
}

/// Evaluate `condition` with `Exists('…')` answered from the file system,
/// relative paths resolved against `exists_dir`, as the walk answers it for
/// an element whose condition resolves there. Exposed so
/// `tests/condition_diff.rs` can hold `Exists()` to MSBuild over generated
/// trees of files, directories and symlinks.
pub fn evaluate_with_exists(
    condition: &str,
    props: &PropertyMap,
    exists_dir: &std::path::Path,
) -> Outcome {
    let observer = crate::observed::Observer::new();
    let exists = |path: &str| crate::evaluator::condition_exists(&observer, path, exists_dir);
    let probes = crate::condition::Probes {
        exists: &exists,
        observer: &observer,
    };
    crate::condition::evaluate_with_exists(condition, props, probes).outcome
}

pub use crate::evaluator::executor::{ExecutedItem, ExecutionProbe, ExecutionRead};
pub use crate::evaluator::reads::{
    EvaluationReads, InexactUnset, ItemRead, ItemRow, PropertyRead, ReadProbe, TargetDefinition,
    TargetRead,
};

/// [`crate::parse_fsproj_with_imports`], also reading `probe`'s properties and
/// item types at the end of the walk, as a target that runs on the evaluation
/// would read them. The restore-cone census reports these reads against
/// MSBuild's (stage A₁.3a of `docs/nuget-dgspec-boundary-plan.md`).
///
/// `startup_directory` is the working directory of the build process the
/// evaluation models, which MSBuild exposes as `MSBuildStartupDirectory`: the
/// directory the restore cone's `dotnet` starts in. `None` models a build
/// nobody launched, as the public entry points do, and leaves the name unset.
#[allow(clippy::too_many_arguments)]
pub fn parse_fsproj_reads(
    project: &crate::ProjectFile,
    extra_properties: &std::collections::HashMap<String, String>,
    environment: &std::collections::HashMap<String, String>,
    sdk_resolver: Option<&crate::SdkResolver<'_>>,
    glob_resolver: Option<&crate::GlobResolver<'_>>,
    startup_directory: Option<&std::path::Path>,
    probe: &ReadProbe,
) -> Result<(crate::ParsedProject, EvaluationReads), crate::ParseError> {
    let walked = crate::parse_fsproj_probed(
        project,
        extra_properties,
        environment,
        sdk_resolver,
        glob_resolver,
        startup_directory,
        Some(probe),
    )?;
    let reads = walked.reads.expect("a probed walk answers its probe");
    Ok((walked.project, reads))
}

/// Make `version_dir` (`{dotnet_root}/sdk/{version}`) an SDK the .NET host
/// counts as installed: the directory, and the `dotnet.dll` hostfxr requires
/// in it before it will run or select it (see the SDK resolver's
/// `host_sdk_versions`). Every fake dotnet root in the test suites lays its
/// SDK version directories out through this, so a test that builds one
/// models an install hostfxr would see.
pub fn install_host_sdk_dir(version_dir: &std::path::Path) {
    std::fs::create_dir_all(version_dir).expect("create the SDK version directory");
    std::fs::write(version_dir.join("dotnet.dll"), "").expect("write the SDK's dotnet.dll");
}

/// [`install_host_sdk_dir`] for the SDK version directory holding `sdk_root`,
/// a `{dotnet_root}/sdk/{version}/Sdks/{name}/Sdk` directory.
pub fn install_host_sdk_of(sdk_root: &std::path::Path) {
    let version_dir = sdk_root
        .ancestors()
        .nth(3)
        .filter(|dir| dir.parent().is_some_and(|sdk| sdk.ends_with("sdk")))
        .unwrap_or_else(|| {
            panic!(
                "{} is no {{dotnet_root}}/sdk/{{version}}/Sdks/{{name}}/Sdk",
                sdk_root.display()
            )
        });
    install_host_sdk_dir(version_dir);
}

/// [`crate::fsc::compiled_assembly_name`] with the SDK whose version directory
/// is `sdk`, and every workload manifest it loads, counted as graded, whether
/// or not they are on [`crate::fsc::verified_sdks`] and
/// [`crate::fsc::verified_manifests`]: the grading run grades them before it
/// writes the list.
pub fn compiled_assembly_name_grading(
    sdk: &str,
    project_path: &std::path::Path,
    parsed: &crate::ParsedProject,
    inputs: &crate::fsc::NameInputs<'_>,
) -> crate::fsc::CompiledAssemblyName {
    crate::fsc::compiled_assembly_name_graded(
        project_path,
        parsed,
        inputs,
        &|version| version == sdk,
        &|_, _| true,
    )
}

/// What the walk reads as the inline task body of the first `<UsingTask>` in
/// `xml` (its `<Task>`), unexpanded, where it reproduces MSBuild's reading
/// (`ProjectUsingTaskBodyElement.TaskBody`); `None` where it declines, or
/// where there is none. Held to MSBuild's by `tests/inline_task_body_diff.rs`.
pub fn inline_task_body(xml: &str) -> Option<String> {
    let document = crate::document::parse(xml).ok()?;
    let task = document
        .root_element()
        .children()
        .filter(|node| node.is_element() && node.tag_name().name() == "UsingTask")
        .flat_map(|using_task| using_task.children())
        .find(|node| node.is_element() && node.tag_name().name() == "Task")?;
    crate::evaluator::inline_task_body(task)
}
