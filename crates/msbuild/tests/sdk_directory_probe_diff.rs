//! The directory an SDK reference resolves to, held to `dotnet msbuild`.
//!
//! `locate_dotnet_sdk` stands for two resolvers. For a name with no version,
//! MSBuild's default resolver serves `$(MSBuildSDKsPath)/{name}/Sdk` of the
//! SDK that runs, on `Directory.Exists` alone; for a name `global.json`'s
//! `msbuild-sdks` pins, NuGet's resolver serves the restored package's `Sdk/`
//! where `Directory.Exists` finds it and `sdk/` otherwise. Neither looks at
//! `Sdk.props` or `Sdk.targets` before MSBuild imports them, and neither tries
//! another version.
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

/// `dotnet msbuild -getProperty:Picked` of a project referencing [`SDK`] in
/// `project_dir`, under `dotnet` with `env` (the scrubbed environment plus
/// what the case sets).
fn build(dotnet: &Path, project_dir: &Path, env: &BTreeMap<String, String>) -> Built {
    std::fs::write(
        project_dir.join("p.proj"),
        format!(r#"<Project Sdk="{SDK}"></Project>"#),
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
        let ours = locate_dotnet_sdk(&fake, None, SDK, None, None, &Observer::new());
        if matches!(shape, Shape::Odd(Odd::Fifo)) && !matches!(site, Site::Directory) {
            assert!(
                matches!(ours, Err(SdkResolveError::UnsupportedLayout { .. })),
                "{case}: MSBuild's read of a FIFO never returns, so we must decline: {ours:?}"
            );
            continue;
        }
        let theirs = build(&fake.join("dotnet"), &project, &env);
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
    let pins: BTreeMap<String, SdkVersion> =
        [(SDK.to_owned(), SdkVersion::parse("1.0.0").unwrap())].into();
    let mut failures = Vec::new();
    let mut committed = 0;
    let cases = nuget_cases();
    for (index, package) in cases.iter().enumerate() {
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
        let name_of = |root: &Path| {
            if root == upper || root.starts_with(&upper) {
                "upper".to_owned()
            } else if root == lower || root.starts_with(&lower) {
                "lower".to_owned()
            } else {
                format!("elsewhere: {}", root.display())
            }
        };
        let case = format!("{package:?}");
        let ours = locate_dotnet_sdk(
            &empty_root,
            Some(&packages),
            SDK,
            None,
            Some(&pins),
            &Observer::new(),
        );
        let mut env = base_environment();
        env.insert(
            "NUGET_PACKAGES".to_owned(),
            packages.to_string_lossy().into_owned(),
        );
        let theirs = build(Path::new("dotnet"), &project, &env);
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
