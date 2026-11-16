//! The directory an SDK reference resolves to, held to `dotnet msbuild`.
//!
//! `locate_dotnet_sdk` stands for two resolvers. For a name with no version,
//! MSBuild's default resolver serves `$(MSBuildSDKsPath)/{name}/Sdk` of the
//! SDK that runs, on `Directory.Exists` alone; for a name `global.json`'s
//! `msbuild-sdks` pins, NuGet's resolver serves the restored package's `Sdk/`
//! where `Directory.Exists` finds it and `sdk/` otherwise. Neither looks at
//! `Sdk.props` or `Sdk.targets` before MSBuild imports them, and neither tries
//! another version. For a name NuGet has a version for, the default resolver
//! still goes first: it serves the running SDK's copy whatever the version,
//! and NuGet's is read only where the running SDK has none
//! (`the_running_sdk_s_copy_is_served_before_nuget_s`).
//!
//! Each test builds a layout, puts one shape at a path a resolver probes (the
//! SDK directory, either file in it, the package's restore markers), and asks
//! the real build which `Sdk.props` it imported: each one sets `Picked` to a
//! name for its copy. Certain-implies-exact: a directory we commit to must be
//! the one MSBuild imports from, and a `NotFound` must be a build that fails.
//! A decline makes no claim.
//!
//! The default resolver's half needs SDK directories to put shapes in, so it
//! runs on a copy of the devshell's dotnet root: the muxer and each SDK's
//! `dotnet.dll` copied (the SDK directory MSBuild reports is where those load
//! from), everything else linked. A FIFO is placed only where neither the
//! resolver nor MSBuild opens it, since a read of one never returns; where
//! one is opened, our side alone is held to a decline.
//!
//! Unix only: the shapes are links and special files.
#![cfg(unix)]

mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::host_fs::HostPath as _;
use borzoi_msbuild::observed::{Observer, host_fs};
use borzoi_msbuild::{SdkResolveError, SdkVersion, locate_dotnet_sdk};
use borzoi_oracle_harness::BoundedCommand;
use common::odd_entry::{self, Odd};

const SDK: &str = "Contoso.Sdk";

/// The workload environment of every build here, which runs with
/// `MSBuildEnableWorkloadResolver=false` ([`base_environment`]): the workload
/// resolver serves no name.
fn no_workloads() -> borzoi_msbuild::workloads::WorkloadEnvironment<'static> {
    borzoi_msbuild::workloads::WorkloadEnvironment {
        user_dotnet_root: None,
        overrides_present: false,
        resolver_switched_off: true,
        global_json: Default::default(),
        process_architecture: None,
    }
}

fn props(name: &str) -> String {
    format!("<Project><PropertyGroup><Picked>{name}</Picked></PropertyGroup></Project>")
}

const TARGETS: &str = "<Project />";

/// Write a complete SDK directory at `dir` whose `Sdk.props` names `name`.
fn complete(dir: &Path, name: &str) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("Sdk.props"), props(name)).unwrap();
    std::fs::write(dir.join("Sdk.targets"), TARGETS).unwrap();
}

/// What the real build did: the `Picked` its imported `Sdk.props` set, or
/// that it failed, or that it never finished.
#[derive(Debug, PartialEq, Eq)]
enum Built {
    Picked(String),
    Failed(String),
    Hung,
}

/// `dotnet msbuild -getProperty:Picked` of a project whose `Sdk` attribute is
/// `sdk_ref`, in `project_dir`, under `dotnet` with `env` (the scrubbed
/// environment plus what the case sets).
fn build(
    dotnet: &Path,
    project_dir: &Path,
    sdk_ref: &str,
    env: &BTreeMap<String, String>,
) -> Built {
    std::fs::write(
        project_dir.join("p.proj"),
        format!(r#"<Project Sdk="{sdk_ref}"></Project>"#),
    )
    .unwrap();
    let mut cmd = Command::new(dotnet);
    cmd.current_dir(project_dir).env_clear().envs(env).args([
        "msbuild",
        "-nologo",
        "-getProperty:Picked",
        "p.proj",
    ]);
    match BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(120))
        .run()
    {
        Ok(out) if out.status.success() => {
            Built::Picked(String::from_utf8_lossy(&out.stdout).trim().to_owned())
        }
        Ok(out) => {
            let text = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            let code = text
                .split_whitespace()
                .find(|w| w.starts_with("MSB") && w.len() >= 7)
                .unwrap_or("no MSB code")
                .trim_end_matches(':')
                .to_owned();
            Built::Failed(code)
        }
        Err(_) => Built::Hung,
    }
}

/// The environment every `dotnet` child runs under: enough to find the
/// toolchain and a home, and nothing that redirects SDK resolution.
fn base_environment() -> BTreeMap<String, String> {
    let mut env = BTreeMap::new();
    for (key, value) in std::env::vars() {
        let keep = matches!(key.as_str(), "PATH" | "HOME" | "TMPDIR")
            || (key.starts_with("DOTNET_") && !key.starts_with("DOTNET_MSBUILD_SDK_RESOLVER"))
            || key.starts_with("NUGET_");
        if keep {
            env.insert(key, value);
        }
    }
    env.insert(
        "MSBuildEnableWorkloadResolver".to_owned(),
        "false".to_owned(),
    );
    env
}

/// Hold our answer for `layout` to the real build's, returning whether we
/// committed (to a directory, or to the build failing).
fn grade(
    case: &str,
    ours: Result<borzoi_msbuild::SdkPaths, SdkResolveError>,
    name_of: impl Fn(&Path) -> String,
    theirs: &Built,
    failures: &mut Vec<String>,
) -> bool {
    let verdict = match (&ours, theirs) {
        (Ok(paths), Built::Picked(picked)) if &name_of(&paths.root) == picked => None,
        (Ok(paths), _) => Some(format!(
            "we resolve to {} ({}), the build {theirs:?}",
            paths.root.display(),
            name_of(&paths.root)
        )),
        (
            Err(SdkResolveError::NotFound | SdkResolveError::VersionNotSatisfied { .. }),
            Built::Failed(_),
        ) => None,
        (
            Err(err @ (SdkResolveError::NotFound | SdkResolveError::VersionNotSatisfied { .. })),
            _,
        ) => Some(format!("we say {err:?}, the build {theirs:?}")),
        (Err(SdkResolveError::UnsupportedLayout { .. }), _) => None,
    };
    println!(
        "{case}: ours {}, the build {theirs:?}",
        match &ours {
            Ok(paths) => name_of(&paths.root),
            Err(SdkResolveError::UnsupportedLayout { .. }) => "decline".to_owned(),
            Err(err) => format!("{err:?}"),
        }
    );
    if let Some(verdict) = verdict {
        failures.push(format!("{case}: {verdict}"));
    }
    !matches!(ours, Err(SdkResolveError::UnsupportedLayout { .. }))
}

// ---------------------------------------------------------------------------
// The default resolver: `{sdk}/Sdks/{name}/Sdk` of the SDK that runs.

/// A copy of `real` (a dotnet root) whose SDK directories can be changed: the
/// muxer and each SDK's `dotnet.dll` copied, each SDK's `Sdks` a directory of
/// links, and everything else linked.
fn copy_dotnet_root(real: &Path, fake: &Path) {
    use std::os::unix::fs::symlink;
    std::fs::create_dir_all(fake.join("sdk")).unwrap();
    std::fs::copy(real.join("dotnet"), fake.join("dotnet")).unwrap();
    for entry in host_fs::read_dir(real).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name != "sdk" && name != "dotnet" {
            symlink(entry.path(), fake.join(&name)).unwrap();
        }
    }
    for version in host_fs::read_dir(real.join("sdk")).unwrap() {
        let version = version.unwrap().path();
        let ours = fake.join("sdk").join(version.file_name().unwrap());
        std::fs::create_dir_all(ours.join("Sdks")).unwrap();
        for entry in host_fs::read_dir(&version).unwrap() {
            let entry = entry.unwrap();
            let name = entry.file_name();
            if name == "dotnet.dll" {
                std::fs::copy(entry.path(), ours.join(&name)).unwrap();
            } else if name != "Sdks" {
                symlink(entry.path(), ours.join(&name)).unwrap();
            }
        }
        for sdk in host_fs::read_dir(version.join("Sdks")).unwrap() {
            let sdk = sdk.unwrap();
            symlink(sdk.path(), ours.join("Sdks").join(sdk.file_name())).unwrap();
        }
    }
}

/// Where a default-resolver case puts its shape, in the highest SDK.
#[derive(Clone, Copy, Debug)]
enum Site {
    /// `Sdks/{name}/Sdk` itself, with `Sdks/{name}` present.
    Directory,
    /// `Sdk.props` in an otherwise complete SDK directory.
    Props,
    /// `Sdk.targets` in an otherwise complete SDK directory.
    Targets,
}

/// What a default-resolver case puts at its site.
#[derive(Clone, Copy, Debug)]
enum Shape {
    Complete,
    Absent,
    Odd(Odd),
}

fn default_resolver_cases() -> Vec<(Site, Shape)> {
    let mut cases = vec![
        (Site::Directory, Shape::Complete),
        (Site::Directory, Shape::Absent),
    ];
    for &odd in Odd::ALL {
        cases.push((Site::Directory, Shape::Odd(odd)));
    }
    for site in [Site::Props, Site::Targets] {
        cases.push((site, Shape::Absent));
        for &odd in Odd::OPENABLE {
            cases.push((site, Shape::Odd(odd)));
        }
        // A FIFO here is opened by MSBuild's import, which never returns.
        cases.push((site, Shape::Odd(Odd::Fifo)));
    }
    cases
}

/// The real dotnet root's SDK versions, highest last.
fn installed_versions(real: &Path) -> Vec<(SdkVersion, String)> {
    let mut versions: Vec<(SdkVersion, String)> = host_fs::read_dir(real.join("sdk"))
        .unwrap()
        .filter_map(|entry| {
            let entry = entry.unwrap();
            let name = entry.file_name().into_string().ok()?;
            entry
                .path()
                .join("dotnet.dll")
                .host_is_file()
                .then_some(())?;
            Some((SdkVersion::parse(&name)?, name))
        })
        .collect();
    versions.sort();
    versions
}

#[test]
fn the_default_resolver_serves_the_running_sdk_s_directory() {
    let real = PathBuf::from(
        std::env::var_os("DOTNET_ROOT").expect("DOTNET_ROOT is set; run under nix develop"),
    );
    let versions = installed_versions(&real);
    assert!(
        versions.len() >= 2,
        "the devshell's dotnet root must hold two SDKs for the highest to lack a name a lower \
         one has: {versions:?}"
    );
    let high = &versions[versions.len() - 1].1;
    let low = &versions[versions.len() - 2].1;
    let scratch = tempfile::TempDir::new().unwrap();
    let fake = scratch.path().join("dotnet");
    copy_dotnet_root(&real, &fake);
    let aside = scratch.path().join("aside");
    let project = scratch.path().join("project");
    std::fs::create_dir_all(&project).unwrap();
    // Stops hostfxr's walk for a `global.json` above the project: with no
    // `sdk` member, the highest SDK runs, as an unconstrained spec selects.
    std::fs::write(project.join("global.json"), "{}").unwrap();
    let mut env = base_environment();
    env.insert(
        "DOTNET_ROOT".to_owned(),
        fake.to_string_lossy().into_owned(),
    );

    let sdk_dir = |version: &str| fake.join("sdk").join(version).join("Sdks").join(SDK);
    let name_of = |root: &Path| {
        if root.starts_with(sdk_dir(high)) {
            "high".to_owned()
        } else if root.starts_with(sdk_dir(low)) {
            "low".to_owned()
        } else {
            format!("elsewhere: {}", root.display())
        }
    };
    let mut failures = Vec::new();
    let mut committed = 0;
    let cases = default_resolver_cases();
    for (site, shape) in &cases {
        for version in [high, low] {
            let _ = std::fs::remove_dir_all(sdk_dir(version));
        }
        complete(&sdk_dir(low).join("Sdk"), "low");
        let high_sdk = sdk_dir(high).join("Sdk");
        match (site, shape) {
            (_, Shape::Complete) => complete(&high_sdk, "high"),
            (Site::Directory, Shape::Absent) => std::fs::create_dir_all(sdk_dir(high)).unwrap(),
            (Site::Directory, Shape::Odd(odd)) => {
                odd_entry::place(*odd, &high_sdk, "", &aside);
                if *odd == Odd::DirLink {
                    complete(&host_fs::read_link(&high_sdk).unwrap(), "high");
                }
            }
            (Site::Props | Site::Targets, shape) => {
                complete(&high_sdk, "high");
                let (file, content) = match site {
                    Site::Props => ("Sdk.props", props("high")),
                    _ => ("Sdk.targets", TARGETS.to_owned()),
                };
                match shape {
                    Shape::Absent => std::fs::remove_file(high_sdk.join(file)).unwrap(),
                    Shape::Odd(odd) => {
                        odd_entry::place(*odd, &high_sdk.join(file), &content, &aside)
                    }
                    Shape::Complete => unreachable!(),
                }
            }
        }
        let case = format!("{site:?} as {shape:?}");
        let ours = locate_dotnet_sdk(
            &fake,
            None,
            SDK,
            None,
            None,
            &no_workloads(),
            &Observer::new(),
        );
        if matches!(shape, Shape::Odd(Odd::Fifo)) && !matches!(site, Site::Directory) {
            assert!(
                matches!(ours, Err(SdkResolveError::UnsupportedLayout { .. })),
                "{case}: MSBuild's read of a FIFO never returns, so we must decline: {ours:?}"
            );
            continue;
        }
        let theirs = build(&fake.join("dotnet"), &project, SDK, &env);
        if grade(&case, ours, name_of, &theirs, &mut failures) {
            committed += 1;
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        committed >= 6,
        "the sweep committed only {committed} answers of {}",
        cases.len()
    );
}

// ---------------------------------------------------------------------------
// NuGet's resolver: the restored package's `Sdk/`, else its `sdk/`.

/// What a NuGet case lays out in the package's version directory.
#[derive(Clone, Copy, Debug)]
enum Package {
    /// `Sdk/` complete, `sdk/` complete.
    Both,
    /// `sdk/` complete only.
    LowerOnly,
    /// Neither inner directory.
    Neither,
    /// `Sdk/` as the shape, `sdk/` complete.
    Upper(Odd),
    /// `Sdk/` empty, `sdk/` complete.
    UpperEmpty,
    /// `Sdk/` complete but its `Sdk.props` the shape, `sdk/` complete.
    UpperProps(Odd),
    /// `Sdk/` complete; the restore markers absent.
    NoMarker,
    /// `Sdk/` complete; the only restore marker, `.nupkg.metadata`, the shape.
    Marker(Odd),
    /// `Sdk/` complete; the only restore marker the `.nupkg.sha512`.
    HashOnly,
}

impl Package {
    /// Whether the case puts different entries at `Sdk` and `sdk`, which a
    /// case-insensitive file system cannot hold.
    fn needs_distinct_spellings(self) -> bool {
        matches!(
            self,
            Package::Upper(_) | Package::UpperEmpty | Package::UpperProps(_)
        )
    }
}

/// The `Picked` that `root`'s `Sdk.props` sets, or why there is none.
fn picked_in(root: &Path) -> String {
    match host_fs::read_to_string(root.join("Sdk.props")) {
        Ok(text) => text
            .split_once("<Picked>")
            .and_then(|(_, rest)| rest.split_once("</Picked>"))
            .map_or_else(
                || format!("no Picked in {}", root.display()),
                |(name, _)| name.to_owned(),
            ),
        Err(err) => format!("unreadable {}: {err}", root.display()),
    }
}

fn nuget_cases() -> Vec<Package> {
    let mut cases = vec![
        Package::Both,
        Package::LowerOnly,
        Package::Neither,
        Package::UpperEmpty,
        Package::NoMarker,
        Package::HashOnly,
    ];
    for &odd in Odd::ALL {
        cases.push(Package::Upper(odd));
        cases.push(Package::Marker(odd));
    }
    for &odd in Odd::OPENABLE {
        cases.push(Package::UpperProps(odd));
    }
    cases
}

#[test]
fn nuget_serves_the_package_s_sdk_directory() {
    let scratch = tempfile::TempDir::new().unwrap();
    let aside = scratch.path().join("aside");
    let project = scratch.path().join("project");
    let empty_root = scratch.path().join("no-dotnet");
    std::fs::create_dir_all(&project).unwrap();
    std::fs::create_dir_all(&empty_root).unwrap();
    std::fs::write(
        project.join("global.json"),
        format!(r#"{{"msbuild-sdks":{{"{SDK}":"1.0.0"}}}}"#),
    )
    .unwrap();
    // No package source: NuGet cannot download what the folder lacks.
    std::fs::write(
        project.join("nuget.config"),
        "<configuration><packageSources><clear /></packageSources></configuration>",
    )
    .unwrap();
    let case_sensitive = {
        let probe = scratch.path().join("Case");
        std::fs::create_dir(&probe).unwrap();
        !scratch.path().join("case").host_is_dir()
    };
    let pins: BTreeMap<String, SdkVersion> =
        [(SDK.to_owned(), SdkVersion::parse("1.0.0").unwrap())].into();
    let mut failures = Vec::new();
    let mut committed = 0;
    let cases = nuget_cases();
    for (index, package) in cases.iter().enumerate() {
        if !case_sensitive && package.needs_distinct_spellings() {
            println!("{package:?}: skipped, `Sdk` and `sdk` are one directory here");
            continue;
        }
        let packages = scratch.path().join(format!("packages{index}"));
        let version = packages.join(SDK.to_ascii_lowercase()).join("1.0.0");
        std::fs::create_dir_all(&version).unwrap();
        let metadata = version.join(".nupkg.metadata");
        let hash = version.join(format!("{}.1.0.0.nupkg.sha512", SDK.to_ascii_lowercase()));
        let marker_json = r#"{"version":2,"contentHash":"x","source":null}"#;
        match package {
            Package::NoMarker => {}
            Package::HashOnly => std::fs::write(&hash, "x").unwrap(),
            Package::Marker(odd) => odd_entry::place(*odd, &metadata, marker_json, &aside),
            _ => std::fs::write(&metadata, marker_json).unwrap(),
        }
        let upper = version.join("Sdk");
        let lower = version.join("sdk");
        match package {
            Package::Both => {
                complete(&upper, "upper");
                complete(&lower, "lower");
            }
            Package::LowerOnly => complete(&lower, "lower"),
            Package::Neither => {}
            Package::Upper(odd) => {
                odd_entry::place(*odd, &upper, "", &aside);
                if *odd == Odd::DirLink {
                    complete(&host_fs::read_link(&upper).unwrap(), "upper");
                }
                complete(&lower, "lower");
            }
            Package::UpperEmpty => {
                std::fs::create_dir_all(&upper).unwrap();
                complete(&lower, "lower");
            }
            Package::UpperProps(odd) => {
                complete(&upper, "upper");
                odd_entry::place(*odd, &upper.join("Sdk.props"), &props("upper"), &aside);
                complete(&lower, "lower");
            }
            Package::NoMarker | Package::Marker(_) | Package::HashOnly => {
                complete(&upper, "upper");
            }
        }
        // Named by what the directory's `Sdk.props` says, which is what the
        // build reports: on a case-insensitive file system `Sdk` and `sdk`
        // are one directory, whichever spelling names it.
        let name_of = |root: &Path| picked_in(root);
        let case = format!("{package:?}");
        let ours = locate_dotnet_sdk(
            &empty_root,
            Some(&packages),
            SDK,
            None,
            Some(&pins),
            &no_workloads(),
            &Observer::new(),
        );
        let mut env = base_environment();
        env.insert(
            "NUGET_PACKAGES".to_owned(),
            packages.to_string_lossy().into_owned(),
        );
        let theirs = build(Path::new("dotnet"), &project, SDK, &env);
        if grade(&case, ours, name_of, &theirs, &mut failures) {
            committed += 1;
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        committed >= 6,
        "the sweep committed only {committed} answers of {}",
        cases.len()
    );
}

// ---------------------------------------------------------------------------
// The order between them, for a name NuGet has a version for.

/// What a resolver-order case puts in the running (highest) SDK's
/// `Sdks/{name}`.
#[derive(Clone, Copy, Debug)]
enum Running {
    Absent,
    Complete,
    /// An empty `Sdk` directory: served, and then the import fails.
    Empty,
}

/// What a resolver-order case puts in the NuGet folder.
#[derive(Clone, Copy, Debug)]
enum Restored {
    Absent,
    /// The pinned version.
    Pinned,
    /// Another version only.
    Other,
}

/// Where the version comes from.
#[derive(Clone, Copy, Debug)]
enum PinForm {
    /// `global.json`'s `msbuild-sdks`.
    GlobalJson,
    /// The reference's own `Name/Version`.
    PerImport,
}

/// Which version is pinned.
#[derive(Clone, Copy, Debug)]
enum PinVersion {
    /// One no installed SDK is named by.
    Unrelated,
    /// The lower installed SDK's version.
    LowerSdk,
}

#[derive(Clone, Copy, Debug)]
struct OrderCase {
    running: Running,
    lower_has_it: bool,
    restored: Restored,
    form: PinForm,
    pin: PinVersion,
}

fn order_cases() -> Vec<OrderCase> {
    let mut cases = Vec::new();
    for running in [Running::Absent, Running::Complete, Running::Empty] {
        for lower_has_it in [false, true] {
            for restored in [Restored::Absent, Restored::Pinned, Restored::Other] {
                for form in [PinForm::GlobalJson, PinForm::PerImport] {
                    for pin in [PinVersion::Unrelated, PinVersion::LowerSdk] {
                        cases.push(OrderCase {
                            running,
                            lower_has_it,
                            restored,
                            form,
                            pin,
                        });
                    }
                }
            }
        }
    }
    cases
}

/// Lay `case` out under `dir` and return our answer and the build's, each
/// directory we resolve to named by the `Picked` its `Sdk.props` sets.
fn run_order_case(
    case: OrderCase,
    real: &Path,
    high: &str,
    low: &str,
    dir: &Path,
) -> (Result<String, SdkResolveError>, Built) {
    let fake = dir.join("dotnet");
    copy_dotnet_root(real, &fake);
    let sdk_dir = |version: &str| fake.join("sdk").join(version).join("Sdks").join(SDK);
    match case.running {
        Running::Absent => {}
        Running::Complete => complete(&sdk_dir(high).join("Sdk"), "running"),
        Running::Empty => std::fs::create_dir_all(sdk_dir(high).join("Sdk")).unwrap(),
    }
    if case.lower_has_it {
        complete(&sdk_dir(low).join("Sdk"), "lower");
    }
    let pin = match case.pin {
        PinVersion::Unrelated => "1.0.0",
        PinVersion::LowerSdk => low,
    };
    let packages = dir.join("packages");
    let id_dir = packages.join(SDK.to_ascii_lowercase());
    let restore = |version: &str, name: &str| {
        let version_dir = id_dir.join(version);
        complete(&version_dir.join("Sdk"), name);
        std::fs::write(version_dir.join(".nupkg.metadata"), "{}").unwrap();
    };
    match case.restored {
        Restored::Absent => std::fs::create_dir_all(&packages).unwrap(),
        Restored::Pinned => restore(pin, "nuget"),
        Restored::Other => restore("2.0.0", "nuget-other"),
    }
    let project = dir.join("project");
    std::fs::create_dir_all(&project).unwrap();
    // No package source: NuGet cannot download what the folder lacks.
    std::fs::write(
        project.join("nuget.config"),
        "<configuration><packageSources><clear /></packageSources></configuration>",
    )
    .unwrap();
    let (sdk_ref, global_json, pins) = match case.form {
        PinForm::GlobalJson => (
            SDK.to_owned(),
            format!(r#"{{"msbuild-sdks":{{"{SDK}":"{pin}"}}}}"#),
            Some(BTreeMap::from([(
                SDK.to_owned(),
                SdkVersion::parse(pin).unwrap(),
            )])),
        ),
        PinForm::PerImport => (format!("{SDK}/{pin}"), "{}".to_owned(), None),
    };
    // Also stops hostfxr's walk above the project: with no `sdk` member, the
    // highest SDK runs, as an unconstrained spec selects.
    std::fs::write(project.join("global.json"), global_json).unwrap();
    let ours = locate_dotnet_sdk(
        &fake,
        Some(&packages),
        &sdk_ref,
        None,
        pins.as_ref(),
        &no_workloads(),
        &Observer::new(),
    );
    let mut env = base_environment();
    env.insert(
        "DOTNET_ROOT".to_owned(),
        fake.to_string_lossy().into_owned(),
    );
    env.insert(
        "NUGET_PACKAGES".to_owned(),
        packages.to_string_lossy().into_owned(),
    );
    let theirs = build(&fake.join("dotnet"), &project, &sdk_ref, &env);
    (ours.map(|paths| picked_in(&paths.root)), theirs)
}

/// A name NuGet has a version for, in both of its forms, against an installed
/// SDK that ships it or not and a NuGet folder that holds it or not: MSBuild
/// serves the running SDK's copy wherever `Directory.Exists` finds it,
/// whatever the version, and consults NuGet only otherwise.
#[test]
fn the_running_sdk_s_copy_is_served_before_nuget_s() {
    let real = PathBuf::from(
        std::env::var_os("DOTNET_ROOT").expect("DOTNET_ROOT is set; run under nix develop"),
    );
    let versions = installed_versions(&real);
    assert!(
        versions.len() >= 2,
        "the devshell's dotnet root must hold two SDKs: {versions:?}"
    );
    let high = versions[versions.len() - 1].1.clone();
    let low = versions[versions.len() - 2].1.clone();
    let scratch = tempfile::TempDir::new().unwrap();
    let cases = order_cases();
    // Each case has its own copy of the dotnet root, so a few run at once.
    let results: Vec<_> = cases
        .chunks(6)
        .enumerate()
        .flat_map(|(chunk, batch)| {
            std::thread::scope(|scope| {
                let handles: Vec<_> = batch
                    .iter()
                    .enumerate()
                    .map(|(i, &case)| {
                        let dir = scratch.path().join(format!("case{chunk}-{i}"));
                        let (real, high, low) = (&real, &high, &low);
                        scope.spawn(move || {
                            let result = run_order_case(case, real, high, low, &dir);
                            let _ = std::fs::remove_dir_all(&dir);
                            (case, result)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().unwrap())
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    let mut failures = Vec::new();
    let mut committed = 0;
    for (case, (ours, theirs)) in results {
        println!("{case:?}: ours {ours:?}, the build {theirs:?}");
        let verdict = match (&ours, &theirs) {
            (Ok(ours), Built::Picked(picked)) if ours == picked => None,
            (Ok(_), _) => Some("a resolution the build does not make"),
            (
                Err(SdkResolveError::NotFound | SdkResolveError::VersionNotSatisfied { .. }),
                Built::Failed(_),
            ) => None,
            (Err(SdkResolveError::NotFound | SdkResolveError::VersionNotSatisfied { .. }), _) => {
                Some("a failure the build does not have")
            }
            (Err(SdkResolveError::UnsupportedLayout { .. }), _) => None,
        };
        if !matches!(ours, Err(SdkResolveError::UnsupportedLayout { .. })) {
            committed += 1;
        }
        if let Some(verdict) = verdict {
            failures.push(format!(
                "{case:?}: {verdict}: ours {ours:?}, the build {theirs:?}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        committed >= cases.len() / 2,
        "the sweep committed only {committed} answers of {}",
        cases.len()
    );
}

// ---------------------------------------------------------------------------
// Which installed SDK runs.

/// What a host-selection case puts at `dotnet.dll` in a stray version
/// directory that outranks every real SDK.
#[derive(Clone, Copy, Debug)]
enum StrayDll {
    Absent,
    Regular,
    Odd(Odd),
}

/// The SDK directory hostfxr resolved, from its trace, running `dotnet
/// --version` in `project` under the dotnet root `fake`.
fn hostfxr_resolved_sdk(fake: &Path, project: &Path, trace: &Path) -> Option<PathBuf> {
    let mut cmd = Command::new(fake.join("dotnet"));
    cmd.current_dir(project)
        .env_clear()
        .envs(base_environment())
        .env("DOTNET_ROOT", fake)
        .env("COREHOST_TRACE", "1")
        .env("COREHOST_TRACEFILE", trace)
        .arg("--version");
    // The stray SDK cannot run; only hostfxr's choice, in the trace, counts.
    let _ = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(120))
        .run();
    let text = host_fs::read_to_string(trace).expect("hostfxr writes its trace");
    std::fs::remove_file(trace).unwrap();
    text.lines().find_map(|line| {
        line.strip_prefix("SDK path resolved to [")
            .and_then(|rest| rest.strip_suffix(']'))
            .map(PathBuf::from)
    })
}

/// hostfxr runs the highest installed SDK whose directory holds a
/// `dotnet.dll` that `access(F_OK)` finds: an SDK directory without one is
/// passed over, and so is one whose `dotnet.dll` is a dangling link or a
/// loop, while a directory, a socket or a FIFO of that name counts. The
/// resolver order then serves that SDK's copy of a name, so a stray version
/// directory decides which copy we commit to.
#[test]
fn hostfxr_runs_the_highest_sdk_holding_a_dotnet_dll() {
    let real = PathBuf::from(
        std::env::var_os("DOTNET_ROOT").expect("DOTNET_ROOT is set; run under nix develop"),
    );
    let versions = installed_versions(&real);
    let high = versions.last().expect("an installed SDK").1.clone();
    let scratch = tempfile::TempDir::new().unwrap();
    let aside = scratch.path().join("aside");
    let trace = scratch.path().join("trace.txt");
    let mut shapes = vec![StrayDll::Absent, StrayDll::Regular];
    shapes.extend(Odd::ALL.iter().map(|&odd| StrayDll::Odd(odd)));
    let mut failures = Vec::new();
    for (index, shape) in shapes.iter().enumerate() {
        let case_dir = scratch.path().join(format!("case{index}"));
        let fake = case_dir.join("dotnet");
        copy_dotnet_root(&real, &fake);
        let stray = fake.join("sdk").join("99.0.0");
        complete(&stray.join("Sdks").join(SDK).join("Sdk"), "stray");
        complete(
            &fake
                .join("sdk")
                .join(&high)
                .join("Sdks")
                .join(SDK)
                .join("Sdk"),
            "high",
        );
        let dll = stray.join("dotnet.dll");
        match shape {
            StrayDll::Absent => {}
            StrayDll::Regular => std::fs::write(&dll, "").unwrap(),
            StrayDll::Odd(odd) => odd_entry::place(*odd, &dll, "", &aside),
        }
        let project = case_dir.join("project");
        std::fs::create_dir_all(&project).unwrap();
        std::fs::write(project.join("global.json"), "{}").unwrap();
        let ours = locate_dotnet_sdk(
            &fake,
            None,
            SDK,
            None,
            None,
            &no_workloads(),
            &Observer::new(),
        )
        .map(|paths| picked_in(&paths.root));
        let theirs = hostfxr_resolved_sdk(&fake, &project, &trace).map(|dir| {
            if dir.ends_with("99.0.0") {
                "stray".to_owned()
            } else if dir.ends_with(&high) {
                "high".to_owned()
            } else {
                format!("elsewhere: {}", dir.display())
            }
        });
        println!("{shape:?}: ours {ours:?}, hostfxr ran {theirs:?}");
        if let Ok(ours) = &ours
            && Some(ours) != theirs.as_ref()
        {
            failures.push(format!(
                "{shape:?}: we serve {ours}, hostfxr runs {theirs:?}"
            ));
        }
        if ours.is_err() {
            failures.push(format!(
                "{shape:?}: we decline where both SDKs ship the name: {ours:?}"
            ));
        }
        let _ = std::fs::remove_dir_all(&case_dir);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
