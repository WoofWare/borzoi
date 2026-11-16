//! Unit tests for workload locator resolution over synthetic on-disk
//! layouts. Behaviours mirror the ground-truth probes recorded in
//! docs/completed/sdk-chain-exactness-plan.md (2026-07-09): known-list ordering,
//! descending band fallback, silent skipping of absent ids, and a
//! degrade for every layout shape outside the envelope.

use crate::observed::Observer;
use crate::observed::host_fs;
use std::fs;
use std::path::{Path, PathBuf};

use tempfile::TempDir;

use super::*;
use crate::SdkResolution;

const TARGETS: &str = super::WORKLOAD_MANIFEST_TARGETS_LOCATOR;
const AUTO: &str = super::WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR;

/// The smallest manifest the workload resolver loads: `version` is its one
/// required key.
const MANIFEST: &str = r#"{"version": "1.0.0"}"#;

fn no_user_env() -> WorkloadEnvironment<'static> {
    WorkloadEnvironment {
        user_dotnet_root: None,
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    }
}

fn write(path: &Path, content: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, content).unwrap();
}

/// Build a dotnet root with one host SDK version dir and a known-list.
fn host_sdk(root: &Path, version: &str, known: &[&str]) -> PathBuf {
    let version_dir = root.join("sdk").join(version);
    crate::test_support::install_host_sdk_dir(&version_dir);
    write(
        &version_dir.join("KnownWorkloadManifests.txt"),
        &known.join("\n"),
    );
    version_dir
}

/// Install a versioned manifest `{root}/sdk-manifests/{band}/{id}/{version}`
/// with both the json and targets files.
fn manifest(root: &Path, band: &str, id: &str, version: &str) -> PathBuf {
    let dir = root.join("sdk-manifests").join(band).join(id).join(version);
    write(&dir.join("WorkloadManifest.json"), MANIFEST);
    write(&dir.join("WorkloadManifest.targets"), "<Project/>");
    dir
}

fn resolve_targets(
    root: &Path,
    version_dir: &Path,
    env: &WorkloadEnvironment<'_>,
) -> Result<SdkResolution, SdkResolveError> {
    resolve_workload_locator(TARGETS, root, version_dir, env, &Observer::new())
}

#[test]
fn manifest_targets_locator_returns_known_list_order() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    // Known list deliberately NOT alphabetical: the import order is the
    // file's order (pinned against `dotnet msbuild -preprocess`).
    let version_dir = host_sdk(root, "10.0.300", &["zeta.workload", "alpha.workload"]);
    let zeta = manifest(root, "10.0.100", "zeta.workload", "1.0.0");
    let alpha = manifest(root, "10.0.100", "alpha.workload", "2.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![zeta, alpha]));
}

#[test]
fn manifest_id_missing_on_disk_is_skipped() {
    // `samsung.net.sdk.tizen` behaviour: in the known list, nothing on
    // disk, silently skipped.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["present.workload", "absent.workload"]);
    let present = manifest(root, "10.0.100", "present.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![present]));
}

#[test]
fn flat_manifest_layout_resolves_to_id_dir() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["flat.workload"]);
    let id_dir = root
        .join("sdk-manifests")
        .join("10.0.100")
        .join("flat.workload");
    write(&id_dir.join("WorkloadManifest.json"), MANIFEST);
    write(&id_dir.join("WorkloadManifest.targets"), "<Project/>");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![id_dir]));
}

#[test]
fn band_fallback_prefers_newest_band_not_above_host() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    // Present under three bands; 11.0.100 is above the host band and
    // must be ignored, 10.0.100 beats 9.0.100.
    manifest(root, "9.0.100", "w.workload", "1.0.0");
    let expected = manifest(root, "10.0.100", "w.workload", "2.0.0");
    manifest(root, "11.0.100", "w.workload", "3.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn exact_host_band_dir_wins_over_older() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    let expected = manifest(root, "10.0.300", "w.workload", "2.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn multiple_manifest_versions_pick_the_latest() {
    // ResolveManifestDirectory (dotnet/sdk): highest version wins.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    let latest = manifest(root, "10.0.100", "w.workload", "1.0.1");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![latest]));
}

#[test]
fn prerelease_manifest_versions_order_by_semver_not_lexically() {
    // SdkVersion implements SemVer 2.0.0 paragraph 11.4 (numeric
    // prerelease identifiers compare numerically — pinned by
    // `prerelease_numeric_identifiers_compared_numerically` in the
    // sdk_resolver tests), so preview.10 beats preview.2 exactly as
    // MSBuild's comparer would.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "10.0.0-preview.2");
    let latest = manifest(root, "10.0.100", "w.workload", "10.0.0-preview.10");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![latest]));
}

#[test]
fn an_uncertified_manifest_version_directory_beside_another_degrades() {
    // The resolver compares the candidates, and a name `System.Version`
    // cannot parse throws there; one `ManifestVersion` does not certify
    // declines.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "not a version!");
    manifest(root, "10.0.100", "w.workload", "1.0.0");

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn a_lone_manifest_version_directory_wins_whatever_its_name() {
    // The resolver folds the candidates, so with one it compares nothing.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let only = manifest(root, "10.0.100", "w.workload", "not a version!");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![only]));
}

#[test]
fn manifest_version_directories_the_resolver_cannot_tell_apart_degrade() {
    // `1.0.0` and `01.0.0` compare equal, and the later one listed wins.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    manifest(root, "10.0.100", "w.workload", "01.0.0");

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn manifest_without_targets_file_is_silently_excluded() {
    // CachingWorkloadResolver keeps only directories containing the
    // targets file; a manifest without one contributes no import.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let dir = root
        .join("sdk-manifests")
        .join("10.0.100")
        .join("w.workload")
        .join("1.0.0");
    write(&dir.join("WorkloadManifest.json"), MANIFEST);
    // No WorkloadManifest.targets.

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(Vec::new()));
}

/// A `workloadsets` directory holding no set selects nothing.
#[test]
fn an_empty_host_band_workloadsets_dir_changes_nothing() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let w = manifest(root, "10.0.100", "w.workload", "1.0.0");
    fs::create_dir_all(root.join("sdk-manifests/10.0.300/workloadsets/10.0.300")).unwrap();

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

/// A host-band workload set is selected by default (`ShouldUseWorkloadSets`
/// is `UseWorkloadSets ?? true`), and its manifests override the scanned ones;
/// the install state's `useWorkloadSets: false`, under the build process's
/// architecture, opts out.
#[test]
fn a_host_band_workload_set_is_selected_unless_the_install_state_opts_out() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let old = manifest(root, "10.0.300", "w.workload", "1.0.0");
    let new = manifest(root, "10.0.300", "w.workload", "2.0.0");
    write_set(
        root,
        "10.0.300",
        "10.0.300",
        &[("x.workloadset.json", r#"{"W.Workload": "1.0.0"}"#)],
    );
    let env = WorkloadEnvironment {
        process_architecture: Some(ProcessArchitecture::X64),
        ..no_user_env()
    };
    assert_eq!(
        resolve_targets(root, &version_dir, &env).unwrap(),
        SdkResolution::Roots(vec![old])
    );
    write(
        &root.join("metadata/workloads/X64/10.0.300/InstallState/default.json"),
        r#"{"useWorkloadSets": false,}"#,
    );
    assert_eq!(
        resolve_targets(root, &version_dir, &env).unwrap(),
        SdkResolution::Roots(vec![new])
    );
    // Without the architecture, the install state cannot be found.
    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn an_empty_host_band_workload_set_in_the_user_root_changes_nothing() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    let w = manifest(&root, "10.0.300", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");
    write_set(
        &user,
        "10.0.300",
        "10.0.300",
        &[("set.workloadset.json", "{}")],
    );
    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        ..no_user_env()
    };

    let result = resolve_targets(&root, &version_dir, &env).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

/// `{root}/sdk-manifests/{band}/workloadsets/{set}/` holding `files`.
fn write_set(root: &Path, band: &str, set: &str, files: &[(&str, &str)]) -> PathBuf {
    let dir = root
        .join("sdk-manifests")
        .join(band)
        .join("workloadsets")
        .join(set);
    fs::create_dir_all(&dir).unwrap();
    for (name, content) in files {
        write(&dir.join(name), content);
    }
    dir
}

/// The baseline set a current SDK installer drops under 8.0.100 is selected
/// only through a `global.json` or install-state version, so with neither the
/// answer is the one the bare layout gives (#549, #499).
#[test]
fn baseline_workload_set_does_not_change_the_answer() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.401", &["w.workload"]);
    let w = manifest(root, "10.0.400", "w.workload", "1.0.0");
    let bare = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(bare, SdkResolution::Roots(vec![w]));

    manifest(root, "10.0.400", "w.workload", "2.0.0");
    let with_set_target = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    // A set naming the *older* manifest: were it selected, the answer would
    // move back to 1.0.0.
    write_set(
        root,
        "8.0.100",
        "10.0.401",
        &[(
            "baseline.workloadset.json",
            "{\n  \"w.workload\": \"1.0.0/10.0.400\",\n  \"other\": \"2.0.0-rc.1.2\"\n}",
        )],
    );
    write_set(
        root,
        "8.0.100",
        "9.0.203.1",
        &[
            ("a.workloadset.json", "{\"x\": \"1.2.3\"}"),
            ("b.WorkloadSet.json", "{\"y\": \"1.2.3\"}"),
        ],
    );
    assert_eq!(
        resolve_targets(root, &version_dir, &no_user_env()).unwrap(),
        with_set_target
    );
    assert_eq!(
        resolve_workload_locator(AUTO, root, &version_dir, &no_user_env(), &Observer::new())
            .unwrap(),
        SdkResolution::Roots(Vec::new())
    );
}

/// Sets in a band that is neither the host's nor the baseline's are never
/// read without a pin, however malformed.
#[test]
fn workload_set_of_an_unscanned_band_is_never_read() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let w = manifest(root, "10.0.100", "w.workload", "1.0.0");
    write_set(
        root,
        "10.0.100",
        "not a version",
        &[("x.workloadset.json", "{")],
    );

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

/// `GetAvailableWorkloadSets(8.0.100)` runs unconditionally and throws on a
/// set it cannot load, failing the real evaluation; each shape here is one
/// the loader is not certified to survive.
#[test]
fn baseline_workload_set_that_may_not_load_degrades() {
    let cases: &[(&str, &[(&str, &str)])] = &[
        ("10.0.400", &[("s.workloadset.json", "{")]),
        ("10.0.400", &[("s.workloadset.json", "null")]),
        ("10.0.400", &[("s.workloadset.json", "[]")]),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": null}")]),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": 1}")]),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": \"\"}")]),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": \"1.0\"}")]),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": \"1.0.0/\"}")]),
        (
            "10.0.400",
            &[("s.workloadset.json", "{\"w\": \"1.0.0/10.0.400/x\"}")],
        ),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": \"01.0.0\"}")]),
        (
            "10.0.400",
            &[("s.workloadset.json", "{\"w\": \"1.0.0+build\"}")],
        ),
        ("10.0.400", &[("s.workloadset.json", "{\"w\": \"1.0.0\",}")]),
        // Comments are refused outright: System.Text.Json ends a `//`
        // comment at a lone `\r`, so this one throws on `not-json` there.
        ("10.0.400", &[("s.workloadset.json", "{}//c\rnot-json")]),
        ("10.0.400", &[("s.workloadset.json", "{}// c\u{2028}")]),
        ("10.0.400", &[("s.workloadset.json", "{/* c */}")]),
        (
            "10.0.400",
            &[(
                "s.workloadset.json",
                "{\"w\": \"1.0.0\",\u{c}\"x\": \"1.0.0\"}",
            )],
        ),
        (
            "10.0.400",
            &[("s.workloadset.json", "{\"w\": \"1.0.0\", \"W\": \"1.0.0\"}")],
        ),
        (
            "10.0.400",
            &[("s.workloadset.json", "{\"\u{212a}\": \"1.0.0\"}")],
        ),
        (
            "10.0.400",
            &[
                ("a.workloadset.json", "{\"w\": \"1.0.0\"}"),
                ("b.workloadset.json", "{\"W\": \"1.0.0\"}"),
            ],
        ),
        ("10.0", &[("s.workloadset.json", "{}")]),
        ("10.0.400.1.2", &[("s.workloadset.json", "{}")]),
        ("v10.0.400", &[("s.workloadset.json", "{}")]),
        ("10.0.400+build", &[("s.workloadset.json", "{}")]),
        ("10.0.400-", &[("s.workloadset.json", "{}")]),
    ];
    for (set, files) in cases {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path();
        let version_dir = host_sdk(root, "10.0.401", &["w.workload"]);
        manifest(root, "10.0.400", "w.workload", "1.0.0");
        write_set(root, "8.0.100", set, files);

        let result = resolve_targets(root, &version_dir, &no_user_env());
        assert!(
            matches!(result, Err(SdkResolveError::UnsupportedLayout { .. })),
            "set {set:?} with {files:?} resolved: {result:?}"
        );
    }
}

/// A set directory with no set file loads as no set, so its name is never
/// parsed; a directory *named* like a set file is not a file.
#[test]
fn baseline_set_directory_shapes() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.401", &["w.workload"]);
    let w = manifest(root, "10.0.400", "w.workload", "1.0.0");
    write_set(root, "8.0.100", "not a version", &[("README", "x")]);
    assert_eq!(
        resolve_targets(root, &version_dir, &no_user_env()).unwrap(),
        SdkResolution::Roots(vec![w])
    );

    let set = write_set(root, "8.0.100", "10.0.401", &[]);
    fs::create_dir_all(set.join("s.workloadset.json")).unwrap();
    assert!(matches!(
        resolve_targets(root, &version_dir, &no_user_env()),
        Err(SdkResolveError::UnsupportedLayout { .. })
    ));
}

#[test]
fn plain_version_grammar() {
    for ok in [
        "0.0.0",
        "10.0.400",
        "9.0.100-rc.1.24452.12",
        "1.2.3-alpha-1.x",
    ] {
        assert!(is_plain_release_version(ok), "{ok}");
        assert!(is_plain_workload_set_version(ok), "{ok}");
    }
    assert!(is_plain_workload_set_version("10.0.105.1"));
    assert!(is_plain_workload_set_version("10.0.105.1-preview.2"));
    for bad in [
        "",
        "1",
        "1.2",
        "1.2.3.4",
        "01.2.3",
        "1.2.3-",
        "1.2.3-a..b",
        "1.2.3-01",
        "1.2.3+b",
        "1.2.x",
        "1234567890.0.0",
        " 1.2.3",
        "1.2.3-a_b",
    ] {
        assert!(!is_plain_release_version(bad), "{bad}");
    }
    for bad in ["1.2.3.4.5", "1.2.3.04", "1.2.3.4-"] {
        assert!(!is_plain_workload_set_version(bad), "{bad}");
    }
}

#[test]
fn install_state_pin_degrades() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(
        &root.join("metadata/workloads/10.0.300/InstallState/default.json"),
        "{}",
    );

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn arch_scoped_install_state_pin_degrades() {
    // The real file-based path carries a process-architecture segment
    // (WorkloadInstallType.GetInstallStateFolder); any arch dir counts.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(
        &root.join("metadata/workloads/Arm64/10.0.300/InstallState/default.json"),
        "{}",
    );

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn msi_installer_type_marker_degrades() {
    // MSI-based installs keep their install state under ProgramData,
    // outside anything we are handed.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(
        &root.join("metadata/workloads/10.0.300/installertype/msi"),
        "",
    );

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn fallback_passes_over_unresolvable_bands() {
    // A newer band has the id directory but no resolvable manifest; an
    // older band has a valid one. MSBuild filters unresolvable
    // candidates before picking the highest band, so the older band's
    // manifest is imported.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    fs::create_dir_all(root.join("sdk-manifests/10.0.200/w.workload")).unwrap();
    let older = manifest(root, "9.0.100", "w.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![older]));
}

#[test]
fn userlocal_marker_without_user_root_degrades() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn userlocal_marker_that_is_a_directory_is_not_a_marker() {
    // CLR `File.Exists` is false for a directory, so `IsUserLocal` reads a
    // `userlocal` *directory* as "no marker" — a global install that resolves
    // normally, not a present marker that would degrade or consult a user root.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let w = manifest(root, "10.0.100", "w.workload", "1.0.0");
    fs::create_dir_all(root.join("metadata/workloads/10.0.300/userlocal")).unwrap();

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

#[test]
fn stray_non_version_directory_under_sdk_manifests_degrades() {
    // `FallbackForMissingManifest` runs `new SdkFeatureBand(dirName)` over every
    // directory under `sdk-manifests`, with no try/catch — a non-version name
    // throws a `FormatException` and fails the real resolution. We must degrade,
    // not silently skip it and return a supposedly-exact result.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    // A known id absent from the host band forces the fallback enumeration.
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    fs::create_dir_all(root.join("sdk-manifests/10.0.300")).unwrap();
    fs::create_dir_all(root.join("sdk-manifests/not-a-band")).unwrap();

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(
        matches!(err, SdkResolveError::UnsupportedLayout { .. }),
        "got {err:?}"
    );
}

#[test]
fn stray_non_version_directory_does_not_degrade_when_nothing_is_missing() {
    // The band enumeration (and its throw) only runs when a known id is missing,
    // mirroring MSBuild's per-missing-id `FallbackForMissingManifest`. When the
    // whole known set resolves in the primary pass, a stray directory alongside
    // is never enumerated, so it must not degrade an otherwise-exact result.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let w = manifest(root, "10.0.300", "w.workload", "1.0.0");
    fs::create_dir_all(root.join("sdk-manifests/not-a-band")).unwrap();

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

#[test]
fn stray_file_under_sdk_manifests_is_ignored_like_get_directories() {
    // `Directory.GetDirectories` returns only directories, so a regular file
    // such as `.DS_Store` under `sdk-manifests` is invisible to the real band
    // enumeration. It must neither be parsed as a feature band (spurious
    // degrade) nor treated as an id directory; the fallback here still resolves
    // the missing id from a lower band.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    // `w.workload` is absent from the host band, present in a lower band.
    let w = manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(&root.join("sdk-manifests/.DS_Store"), "");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

#[test]
#[cfg(unix)]
fn symlinked_manifest_id_directory_is_followed_like_get_directories() {
    // `Directory.GetDirectories` includes a symlink to a directory (package
    // managers and user-local layouts create them). The band enumeration must
    // follow the link, not skip it as a non-directory — otherwise a valid
    // manifest is dropped and an incomplete set is certified as exact.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    // The real manifest content lives outside sdk-manifests; the id directory in
    // the host band is a symlink to it.
    let real = root.join("real-w");
    write(&real.join("1.0.0/WorkloadManifest.json"), MANIFEST);
    write(&real.join("1.0.0/WorkloadManifest.targets"), "<Project/>");
    fs::create_dir_all(root.join("sdk-manifests/10.0.300")).unwrap();
    std::os::unix::fs::symlink(&real, root.join("sdk-manifests/10.0.300/w.workload")).unwrap();

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(
        result,
        SdkResolution::Roots(vec![root.join("sdk-manifests/10.0.300/w.workload/1.0.0")])
    );
}

#[test]
fn known_manifest_list_with_a_leading_bom_still_resolves() {
    // `File.ReadAllLines` strips a leading UTF-8 BOM; we must too, or the first
    // known id carries U+FEFF, fails the safe-id check in band fallback, and
    // degrades a valid layout. The id here is absent from the host band, so it
    // is resolved through the known-list-driven fallback.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = root.join("sdk").join("10.0.300");
    write(
        &version_dir.join("KnownWorkloadManifests.txt"),
        "\u{feff}w.workload\n",
    );
    let w = manifest(root, "10.0.100", "w.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![w]));
}

#[test]
fn user_root_participates_in_the_primary_band_only() {
    // Per SdkDirectoryWorkloadManifestProvider: the user root joins the
    // *current-band* enumeration only; band fallback consults the
    // dotnet root alone. The real-machine shape: dotnet ships the id
    // under 10.0.100 (fallback), the user root's older 9.0.100 copies —
    // including a user-only id — are invisible to a 10.0.300 host.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["shared.workload", "useronly.workload"]);
    let shared = manifest(&root, "10.0.100", "shared.workload", "2.0.0");
    manifest(&user, "9.0.100", "shared.workload", "1.0.0");
    manifest(&user, "9.0.100", "useronly.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result = resolve_targets(&root, &version_dir, &env).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![shared]));
}

#[test]
fn user_root_shadows_dotnet_root_in_the_current_band() {
    // Same-named id dir in both roots' *current* band: the user root
    // wins (dotnet/sdk: "take the first one" over [user, dotnet]).
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    manifest(&root, "10.0.300", "w.workload", "1.0.0");
    let user_copy = manifest(&user, "10.0.300", "w.workload", "2.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result = resolve_targets(&root, &version_dir, &env).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![user_copy]));
}

#[test]
fn user_root_shadows_by_name_even_when_it_holds_no_valid_manifest() {
    // The user root claims an id *by directory name* before its contents are
    // validated (MSBuild overwrites `directoriesWithManifests` by name, then
    // `ProbeDirectory` skips a directory that resolves to nothing). So an empty
    // user id-dir shadows the dotnet root's same-band copy in the primary
    // pass. The id is then missing, and the fallback finds that copy: it
    // searches the dotnet root's bands below the host band *and* the host's
    // release band, which for a release host is the host band itself. Every
    // graded SDK's resolver answers so (10.0.112, 10.0.401,
    // 11.0.100-rc.1.26425.128).
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    // dotnet has a valid current-band manifest that would resolve if not shadowed.
    manifest(&root, "10.0.300", "w.workload", "1.0.0");
    // The user root's same-band id-dir exists but is empty (no version subdir).
    fs::create_dir_all(user.join("sdk-manifests/10.0.300/w.workload")).unwrap();
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result = resolve_targets(&root, &version_dir, &env).unwrap();
    assert_eq!(
        result,
        SdkResolution::Roots(vec![root.join("sdk-manifests/10.0.300/w.workload/1.0.0")]),
        "the empty user id-dir shadows dotnet's same-band copy in the primary \
         pass, and the fallback finds it in the host's release band"
    );
}

#[test]
fn user_root_equal_to_dotnet_root_participates_once() {
    // A user-local dotnet install: DOTNET_ROOT is ~/.dotnet, so the
    // user root *is* the dotnet root. It must not be consulted twice
    // (which would look like a same-band collision).
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let expected = manifest(root, "10.0.300", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(root),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result = resolve_targets(root, &version_dir, &env).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn known_manifests_file_missing_means_current_band_only() {
    // No KnownWorkloadManifests.txt / IncludedWorkloadManifests.txt:
    // there is no fallback pass and no preferential order — the current
    // band's directory enumeration alone drives the result.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = root.join("sdk").join("10.0.300");
    fs::create_dir_all(&version_dir).unwrap();
    let current = manifest(root, "10.0.300", "b.workload", "1.0.0");
    manifest(root, "10.0.100", "old-band.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![current]));
}

#[test]
fn prerelease_host_sdk_resolves_in_its_own_band() {
    // `11.0.100-rc.1.26425.128` is band `11.0.100-rc.1`, the directory
    // its manifests are installed under.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "11.0.100-rc.1.26425.128", &["w.workload"]);
    let expected = manifest(root, "11.0.100-rc.1", "w.workload", "1.0.0");
    manifest(root, "11.0.100", "w.workload", "2.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn host_version_with_build_metadata_degrades() {
    // `WorkloadResolver.Create` hands the raw version to
    // `WorkloadFileBasedInstall.IsUserLocal`, whose `System.Version` parse of
    // `10.0.300+abc` throws whenever a user profile is known.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300+abc", &["w.workload"]);
    manifest(root, "10.0.300", "w.workload", "1.0.0");

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn prerelease_host_falls_back_to_earlier_previews_and_its_release_band() {
    // The fallback's candidates are the bands below the host band and the
    // host's release band, which a prerelease host *precedes*. The highest
    // that resolves wins: here the release band, above the earlier preview.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(
        root,
        "11.0.100-rc.1.26425.128",
        &["a.workload", "b.workload"],
    );
    manifest(root, "11.0.100-preview.6", "a.workload", "1.0.0");
    let a = manifest(root, "11.0.100", "a.workload", "1.0.0");
    let b = manifest(root, "11.0.100-preview.6", "b.workload", "1.0.0");
    // Above the host band, and not its release band: never a candidate.
    manifest(root, "11.0.100-rc.2", "b.workload", "1.0.0");
    manifest(root, "11.0.200", "b.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![a, b]));
}

#[test]
fn a_fallback_band_is_looked_up_under_its_own_name() {
    // `FallbackForMissingManifest` reads each directory name as the feature
    // band it spells and builds the path from the band, so a directory named
    // with a build suffix stands for a band directory that may not exist.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.200-preview.3.25123.4", "w.workload", "2.0.0");
    let expected = manifest(root, "10.0.100", "w.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn a_missing_outdated_id_still_enumerates_the_fallback_bands() {
    // An outdated id is skipped wherever it is found, so it is always
    // missing, and its fallback enumerates the band directories: a stray
    // name among them fails the real resolution.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(
        root,
        "10.0.300",
        &["w.workload", "microsoft.net.workload.ios"],
    );
    manifest(root, "10.0.300", "w.workload", "1.0.0");
    fs::create_dir_all(root.join("sdk-manifests/not-a-band")).unwrap();

    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn env_overrides_present_degrade() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");

    let env = WorkloadEnvironment {
        user_dotnet_root: None,
        overrides_present: true,
        global_json: Default::default(),
        process_architecture: None,
    };
    let err = resolve_targets(root, &version_dir, &env).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn host_band_derives_from_patch_hundreds() {
    // 10.0.301 belongs to band 10.0.300: a marker under the *band* dir
    // (not the literal version) is what gates user-local consultation.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.301", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    // Marker under 10.0.300 must be honoured for host 10.0.301.
    let err = resolve_targets(root, &version_dir, &no_user_env()).unwrap_err();
    assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
}

#[test]
fn auto_import_returns_empty_when_no_pack_ships_auto_import_props() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    // A packs tree exists but nothing ships AutoImport.props.
    write(
        &root.join("packs/Microsoft.NETCore.App.Ref/10.0.0/data/FrameworkList.xml"),
        "",
    );

    let result =
        resolve_workload_locator(AUTO, root, &version_dir, &no_user_env(), &Observer::new())
            .unwrap();
    assert_eq!(result, SdkResolution::Roots(Vec::new()));
}

/// Install manifest `id` at `1.0.0` in band `10.0.300` defining one SDK pack,
/// `Fake.Workload.Sdk` at `1.0.0`.
fn manifest_with_sdk_pack(root: &Path, id: &str) {
    let dir = root.join("sdk-manifests/10.0.300").join(id).join("1.0.0");
    write(
        &dir.join("WorkloadManifest.json"),
        r#"{"version": "1.0.0", "packs": {"Fake.Workload.Sdk": {"kind": "Sdk", "version": "1.0.0"}}}"#,
    );
}

#[test]
fn auto_import_ignores_a_pack_no_manifest_defines() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");
    write(
        &root.join("packs/Fake.Workload.Sdk/1.0.0/Sdk/AutoImport.props"),
        "<Project/>",
    );

    let result =
        resolve_workload_locator(AUTO, root, &version_dir, &no_user_env(), &Observer::new())
            .unwrap();
    assert_eq!(result, SdkResolution::Roots(Vec::new()));
}

#[test]
fn unknown_manifest_in_current_band_is_included_after_known_ids() {
    // The primary pass is directory-driven: a third-party manifest in
    // the current band that is absent from the known list is still
    // imported, ordered after every known-list id.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["zeta.workload"]);
    let zeta = manifest(root, "10.0.300", "zeta.workload", "1.0.0");
    let third_party = manifest(root, "10.0.300", "acme.thirdparty.workload", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![zeta, third_party]));
}

#[test]
fn unknown_manifests_order_alphabetically_after_known() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["known.workload"]);
    let known = manifest(root, "10.0.300", "known.workload", "1.0.0");
    let b = manifest(root, "10.0.300", "b.extra", "1.0.0");
    let a = manifest(root, "10.0.300", "a.extra", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![known, a, b]));
}

#[test]
fn outdated_manifest_ids_are_skipped() {
    // SdkDirectoryWorkloadManifestProvider skips a hardcoded outdated
    // set wherever it appears.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let expected = manifest(root, "10.0.300", "w.workload", "1.0.0");
    manifest(root, "10.0.300", "microsoft.net.workload.android", "1.0.0");

    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn auto_import_returns_the_sdk_folder_of_an_installed_sdk_pack() {
    // The layout CachingWorkloadResolver imports from:
    // packs/{id}/{version}/Sdk/AutoImport.props; one beside `Sdk` is not
    // looked for.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest_with_sdk_pack(root, "w.workload");
    let pack = root.join("packs/Fake.Workload.Sdk/1.0.0");
    write(&pack.join("AutoImport.props"), "<Project/>");
    let observe = || {
        resolve_workload_locator(AUTO, root, &version_dir, &no_user_env(), &Observer::new())
            .unwrap()
    };
    assert_eq!(observe(), SdkResolution::Roots(Vec::new()));

    write(&pack.join("Sdk/AutoImport.props"), "<Project/>");
    assert_eq!(observe(), SdkResolution::Roots(vec![pack.join("Sdk")]));
}

#[test]
fn auto_import_finds_user_packs_even_without_user_manifests() {
    // WorkloadResolver.Create gates the *pack* roots only on the user
    // profile directory existing — not on it containing sdk-manifests
    // (that gate belongs to SdkDirectoryWorkloadManifestProvider). A
    // user-local pack is installed even when the user root holds no
    // manifests.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    manifest_with_sdk_pack(&root, "w.workload");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");
    let pack = user.join("packs/Fake.Workload.Sdk/1.0.0");
    write(&pack.join("Sdk/AutoImport.props"), "<Project/>");

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result =
        resolve_workload_locator(AUTO, &root, &version_dir, &env, &Observer::new()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![pack.join("Sdk")]));
}

#[test]
fn manifestless_user_root_still_resolves_targets_from_dotnet() {
    // A user root with packs but no sdk-manifests joins pack scanning
    // only; the manifest enumeration stays dotnet-root-exact.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    let expected = manifest(&root, "10.0.100", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");
    write(
        &user.join("packs/Microsoft.NETCore.App.Ref/10.0.0/data/FrameworkList.xml"),
        "",
    );

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result = resolve_targets(&root, &version_dir, &env).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn auto_import_empty_when_manifestless_user_root_ships_no_props() {
    // The user root exists and is consulted for packs, but neither root
    // holds an AutoImport.props candidate: the empty result stays exact.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    manifest(&root, "10.0.100", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");
    fs::create_dir_all(user.join("packs")).unwrap();

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result =
        resolve_workload_locator(AUTO, &root, &version_dir, &env, &Observer::new()).unwrap();
    assert_eq!(result, SdkResolution::Roots(Vec::new()));
}

#[test]
fn nonexistent_user_root_participates_nowhere() {
    // Directory.Exists(userProfileDir) is false upstream: the user root
    // joins neither manifest enumeration nor pack scanning, and
    // resolution proceeds against the dotnet root alone.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path().join("dotnet");
    let user = tmp.path().join("missing-user-dotnet");
    let version_dir = host_sdk(&root, "10.0.300", &["w.workload"]);
    let expected = manifest(&root, "10.0.100", "w.workload", "1.0.0");
    write(&root.join("metadata/workloads/10.0.300/userlocal"), "");

    let env = WorkloadEnvironment {
        user_dotnet_root: Some(&user),
        overrides_present: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let result = resolve_targets(&root, &version_dir, &env).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![expected]));
}

#[test]
fn a_global_json_pin_of_a_missing_workload_set_degrades_both_locators() {
    // An sdk.workloadVersion in the governing global.json selects a
    // workload set, and fails the real evaluation when the set is missing.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");

    let env = WorkloadEnvironment {
        user_dotnet_root: None,
        overrides_present: false,
        global_json: crate::GlobalJsonWorkloads::Reads {
            workload_version: Some("10.0.300".to_owned()),
            use_workload_sets: None,
        },
        process_architecture: None,
    };
    for locator in [TARGETS, AUTO] {
        let err = resolve_workload_locator(locator, root, &version_dir, &env, &Observer::new())
            .unwrap_err();
        assert!(matches!(err, SdkResolveError::UnsupportedLayout { .. }));
    }
}

#[test]
fn locator_under_rejecting_spec_reports_version_not_satisfied() {
    // A global.json spec that excludes every installed host SDK keeps
    // the same diagnostic split as ordinary SDK resolution: the
    // available-version list survives, rather than collapsing to
    // NotFound.
    use super::super::version_spec::{RollForward, VersionSpec};

    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.100", "w.workload", "1.0.0");

    let pin = crate::SdkVersion::parse("9.0.100").unwrap();
    let spec = VersionSpec::with_version(pin, RollForward::Disable, false);
    let err = crate::resolve_sdk(
        root,
        None,
        TARGETS,
        Some(&spec),
        None,
        &no_user_env(),
        &Observer::new(),
    )
    .unwrap_err();
    let SdkResolveError::VersionNotSatisfied { available, .. } = err else {
        panic!("expected VersionNotSatisfied, got {err:?}");
    };
    assert_eq!(available.len(), 1);
    assert_eq!(available[0].to_string(), "10.0.300");
}

#[test]
fn resolve_sdk_routes_locators_and_ordinary_names() {
    // End-to-end through the public entry point: an ordinary SDK
    // resolves Single, the locator resolves Roots against the same
    // host SDK selection.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    let expected = manifest(root, "10.0.100", "w.workload", "1.0.0");
    let sdk_dir = version_dir.join("Sdks/Some.Sdk/Sdk");
    write(&sdk_dir.join("Sdk.props"), "<Project/>");
    write(&sdk_dir.join("Sdk.targets"), "<Project/>");

    let ordinary = crate::resolve_sdk(
        root,
        None,
        "Some.Sdk",
        None,
        None,
        &no_user_env(),
        &Observer::new(),
    )
    .unwrap();
    assert!(matches!(ordinary, SdkResolution::Single(_)));

    let locator = crate::resolve_sdk(
        root,
        None,
        TARGETS,
        None,
        None,
        &no_user_env(),
        &Observer::new(),
    )
    .unwrap();
    assert_eq!(locator, SdkResolution::Roots(vec![expected]));
}

/// Run `f` with `dir`'s permissions set to `mode`, restoring them
/// afterwards so `TempDir` cleanup can delete the tree.
#[cfg(unix)]
fn with_dir_mode<R>(dir: &Path, mode: u32, f: impl FnOnce() -> R) -> R {
    use std::os::unix::fs::PermissionsExt;
    let original = host_fs::metadata(dir).unwrap().permissions();
    fs::set_permissions(dir, fs::Permissions::from_mode(mode)).unwrap();
    let result = f();
    fs::set_permissions(dir, original).unwrap();
    result
}

#[cfg(unix)]
#[test]
fn unreadable_band_directory_degrades() {
    // The dotnet provider enumerates the band directory after a
    // Directory.Exists guard; a permission failure there throws and
    // fails the evaluation. Returning the empty enumeration instead
    // would certify a wrong import set as exact.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.300", "w.workload", "1.0.0");
    let band_dir = root.join("sdk-manifests/10.0.300");

    let result = with_dir_mode(&band_dir, 0o000, || {
        resolve_targets(root, &version_dir, &no_user_env())
    });
    // Root bypasses permission bits; only assert degrade when the
    // chmod actually bit (it does everywhere we run tests).
    if host_fs::read_dir(&band_dir).is_err() {
        assert!(matches!(
            result.unwrap_err(),
            SdkResolveError::UnsupportedLayout { .. }
        ));
    }
}

#[cfg(unix)]
#[test]
fn a_pack_under_an_unsearchable_directory_is_not_installed() {
    // `Directory.Exists` answers false where its `stat` fails, so the
    // resolver passes such a pack over rather than throw.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest_with_sdk_pack(root, "w.workload");
    let packs = root.join("packs");
    write(
        &packs.join("Fake.Workload.Sdk/1.0.0/Sdk/AutoImport.props"),
        "<Project/>",
    );

    let (searchable, result) = with_dir_mode(&packs, 0o000, || {
        (
            host_fs::metadata(packs.join("Fake.Workload.Sdk")).is_ok(),
            resolve_workload_locator(AUTO, root, &version_dir, &no_user_env(), &Observer::new()),
        )
    });
    // Root bypasses permission bits.
    let expected = if searchable {
        vec![packs.join("Fake.Workload.Sdk/1.0.0/Sdk")]
    } else {
        Vec::new()
    };
    assert_eq!(result.unwrap(), SdkResolution::Roots(expected));
}

#[cfg(unix)]
#[test]
fn unreadable_known_manifests_file_degrades() {
    // Upstream File.ReadAllLines would throw; treating the list as
    // absent would silently change ordering and band fallback.
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["w.workload"]);
    manifest(root, "10.0.300", "w.workload", "1.0.0");
    let known = version_dir.join("KnownWorkloadManifests.txt");

    use std::os::unix::fs::PermissionsExt;
    let original = host_fs::metadata(&known).unwrap().permissions();
    fs::set_permissions(&known, fs::Permissions::from_mode(0o000)).unwrap();
    let result = resolve_targets(root, &version_dir, &no_user_env());
    let unreadable = host_fs::read_to_string(&known).is_err();
    fs::set_permissions(&known, original).unwrap();
    if unreadable {
        assert!(matches!(
            result.unwrap_err(),
            SdkResolveError::UnsupportedLayout { .. }
        ));
    }
}

/// Two manifests in the host band, one of which degrades: what the
/// resolution observes before it degrades must not depend on the order a
/// `HashMap` yields them in, or two equal evaluations would record different
/// read sets.
#[test]
fn what_resolution_observes_does_not_depend_on_hash_order() {
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["a.workload", "b.workload"]);
    manifest(root, "10.0.300", "a.workload", "1.0.0");
    manifest(root, "10.0.300", "b.workload", "not a version!");
    manifest(root, "10.0.300", "b.workload", "1.0.0");
    let observe = || {
        let observer = Observer::new();
        let result =
            resolve_workload_locator(TARGETS, root, &version_dir, &no_user_env(), &observer);
        assert!(matches!(
            result,
            Err(SdkResolveError::UnsupportedLayout { .. })
        ));
        observer.finish()
    };
    let first = observe();
    for _ in 0..64 {
        assert_eq!(observe(), first);
    }
}

#[test]
fn a_relative_root_declines() {
    // The resolver's `File.Exists` takes a relative path against a working
    // directory we cannot see.
    let result = resolve_targets(
        Path::new("dotnet"),
        Path::new("dotnet/sdk/10.0.300"),
        &no_user_env(),
    );
    assert!(
        matches!(result, Err(SdkResolveError::UnsupportedLayout { .. })),
        "{result:?}"
    );
}

#[cfg(unix)]
#[test]
fn a_dangling_targets_link_keeps_its_directory() {
    // CLR `File.Exists` finds a dangling link, so the resolver keeps the
    // directory and MSBuild's import of the targets then fails
    // (`workload_locator_diff` grades it).
    let tmp = TempDir::new().unwrap();
    let root = tmp.path();
    let version_dir = host_sdk(root, "10.0.300", &["alpha.workload"]);
    let alpha = manifest(root, "10.0.300", "alpha.workload", "1.0.0");
    fs::remove_file(alpha.join("WorkloadManifest.targets")).unwrap();
    std::os::unix::fs::symlink("missing", alpha.join("WorkloadManifest.targets")).unwrap();
    let result = resolve_targets(root, &version_dir, &no_user_env()).unwrap();
    assert_eq!(result, SdkResolution::Roots(vec![alpha]));
}

#[test]
fn the_known_list_splits_as_read_all_lines_splits() {
    assert_eq!(super::read_all_lines("a\nb\r\nc\rd"), ["a", "b", "c", "d"]);
    assert_eq!(super::read_all_lines("a\n\nb\n"), ["a", "", "b"]);
    assert_eq!(super::read_all_lines(" a \r\n"), [" a "]);
    assert!(super::read_all_lines("").is_empty());
}

/// A dotnet root whose running SDK (10.0.300) has one manifest defining the
/// pack `Contoso.Pack` (`packs` is its `packs` object), and a NuGet folder
/// holding a restored `Contoso.Pack` 2.0.0, which `msbuild-sdks` pins.
struct PackOrLayout {
    _tmp: TempDir,
    root: PathBuf,
    nuget: PathBuf,
    pins: std::collections::BTreeMap<String, crate::SdkVersion>,
}

impl PackOrLayout {
    fn new(packs: &str) -> PackOrLayout {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path().join("dotnet");
        let nuget = tmp.path().join("nuget");
        let version_dir = host_sdk(&root, "10.0.300", &["contoso.one"]);
        write(
            &version_dir.join("NETCoreSdkRuntimeIdentifierChain.txt"),
            "linux-x64\nany\n",
        );
        write(
            &root.join("sdk-manifests/10.0.300/contoso.one/1.0.0/WorkloadManifest.json"),
            &format!(r#"{{"version": "1.0.0", "packs": {packs}}}"#),
        );
        let package = nuget.join("contoso.pack/2.0.0");
        write(&package.join(".nupkg.metadata"), "{}");
        write(&package.join("Sdk/Sdk.props"), "<Project/>");
        write(&package.join("Sdk/Sdk.targets"), "<Project/>");
        let pins = std::collections::BTreeMap::from([(
            "Contoso.Pack".to_owned(),
            crate::SdkVersion::parse("2.0.0").unwrap(),
        )]);
        PackOrLayout {
            _tmp: tmp,
            root,
            nuget,
            pins,
        }
    }

    fn resolve(
        &self,
        name: &str,
        env: &WorkloadEnvironment<'_>,
    ) -> Result<SdkResolution, SdkResolveError> {
        crate::resolve_sdk(
            &self.root,
            Some(&self.nuget),
            name,
            None,
            Some(&self.pins),
            env,
            &Observer::new(),
        )
    }

    fn root_of(&self, name: &str, env: &WorkloadEnvironment<'_>) -> PathBuf {
        match self.resolve(name, env) {
            Ok(SdkResolution::Single(paths)) => paths.root,
            other => panic!("{name} resolves to {other:?}"),
        }
    }
}

const CONTOSO_PACK: &str = r#"{"Contoso.Pack": {"kind": "Sdk", "version": "1.0.0"}}"#;

#[test]
fn a_name_the_running_sdk_ships_is_never_looked_up_as_a_pack() {
    // MSBuild asks its default resolver, the running SDK's `Sdks`, first; the
    // workload resolver is asked only where that misses, so not even a
    // workload state that declines reaches the name.
    let layout = PackOrLayout::new(CONTOSO_PACK);
    let shipped = layout.root.join("sdk/10.0.300/Sdks/Contoso.Pack/Sdk");
    write(&shipped.join("Sdk.props"), "<Project/>");
    write(&shipped.join("Sdk.targets"), "<Project/>");
    fs::create_dir_all(layout.root.join("packs/Contoso.Pack/1.0.0")).unwrap();
    let declining = WorkloadEnvironment {
        overrides_present: true,
        ..no_user_env()
    };
    assert_eq!(layout.root_of("Contoso.Pack", &no_user_env()), shipped);
    assert_eq!(layout.root_of("Contoso.Pack", &declining), shipped);
}

#[test]
fn a_workload_pack_is_served_ahead_of_nuget() {
    // The workload resolver (priority 4000) answers before NuGet's (6000),
    // for the name in any case.
    let layout = PackOrLayout::new(CONTOSO_PACK);
    let pack = layout.root.join("packs/Contoso.Pack/1.0.0");
    fs::create_dir_all(&pack).unwrap();
    assert_eq!(
        layout.root_of("Contoso.Pack", &no_user_env()),
        pack.join("Sdk")
    );
    assert_eq!(
        layout.root_of("contoso.PACK", &no_user_env()),
        pack.join("Sdk")
    );
}

#[test]
fn a_name_no_pack_has_for_the_host_goes_on_to_nuget() {
    // An alias naming none of the host's runtime identifiers is no pack: the
    // workload resolver returns null, and NuGet serves its pinned copy.
    let layout = PackOrLayout::new(
        r#"{"Contoso.Pack": {"kind": "Sdk", "version": "1.0.0", "alias-to": {"win-x64": "Contoso.Pack.Win"}}}"#,
    );
    fs::create_dir_all(layout.root.join("packs/Contoso.Pack.Win/1.0.0")).unwrap();
    assert_eq!(
        layout.root_of("Contoso.Pack", &no_user_env()),
        layout.nuget.join("contoso.pack/2.0.0/Sdk")
    );
}

#[test]
fn a_missing_workload_pack_declines() {
    // The resolver succeeds with no path and a `MissingWorkloadPack` item,
    // which the walk does not model; NuGet is never asked.
    let layout = PackOrLayout::new(CONTOSO_PACK);
    let err = layout.resolve("Contoso.Pack", &no_user_env()).unwrap_err();
    assert!(
        matches!(&err, SdkResolveError::UnsupportedLayout { reason } if reason.contains("MissingWorkloadPack")),
        "{err:?}"
    );
}

#[test]
fn a_workload_state_we_cannot_resolve_declines_a_name_the_running_sdk_lacks() {
    // Every name the running SDK does not ship reaches the workload resolver,
    // which loads its manifests before answering; a state we cannot resolve
    // exactly declines even a name NuGet would serve.
    let layout = PackOrLayout::new("{}");
    assert_eq!(
        layout.root_of("Contoso.Pack", &no_user_env()),
        layout.nuget.join("contoso.pack/2.0.0/Sdk")
    );
    let declining = WorkloadEnvironment {
        overrides_present: true,
        ..no_user_env()
    };
    assert!(matches!(
        layout.resolve("Contoso.Pack", &declining),
        Err(SdkResolveError::UnsupportedLayout { .. })
    ));
}
