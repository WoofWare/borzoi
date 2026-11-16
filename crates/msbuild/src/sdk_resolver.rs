//! On-disk locator for the SDK files an MSBuild `<Project Sdk="…">`
//! attribute (or `<Import Sdk="…">` element) refers to.
//!
//! Phase 7b-v0 added the [`SdkResolver`](crate::SdkResolver) seam to
//! [`parse_fsproj_with_imports`](crate::parse_fsproj_with_imports). This
//! module fills the seam for two well-known on-disk layouts:
//!
//! - The shared SDK store under `$DOTNET_ROOT` —
//!   `{dotnet_root}/sdk/{version}/Sdks/{sdk_name}/Sdk/`. Ships with
//!   `Microsoft.NET.Sdk` and its in-box variants
//!   (`Microsoft.NET.Sdk.Web`, …).
//! - The per-user NuGet package cache —
//!   `{nuget_packages}/{name-lowercased}/{version}/{Sdk,sdk}/`. Where
//!   third-party SDKs (`Microsoft.DotNet.Arcade.Sdk`,
//!   `Microsoft.Build.NoTargets`, `MSBuild.Sdk.Extras`, …) actually
//!   live once restored. The inner directory's casing is
//!   package-defined (Microsoft's canonical convention is capital
//!   `Sdk/`; some packages ship lowercase `sdk/`) so the resolver
//!   probes both.
//!
//! ## Scope
//!
//! - Resolve as the resolvers MSBuild consults do, in the order it
//!   consults them (`sdk_directory_probe_diff` grades both rules and the
//!   order against `dotnet msbuild`):
//!   1. MSBuild's default resolver serves `Sdks/{name}/Sdk` of the SDK
//!      that runs wherever `Directory.Exists` finds it, whatever version
//!      the reference names. The running SDK is the host SDK
//!      [`VersionSpec`] selects (typically derived from `global.json` by
//!      [`global_json`]); no other installed version is asked.
//!   2. Otherwise NuGet's resolver serves the package at the version the
//!      reference names: its restored `Sdk/`, else its `sdk/`.
//!
//!   Either directory is taken on `Directory.Exists`; one whose
//!   `Sdk.props` or `Sdk.targets` is then no regular file declines, since
//!   MSBuild fails to import it ([`SdkPaths`] names both).
//! - The version NuGet looks for is a per-import pin `Sdk="Name/Version"`
//!   when present, else the name's entry in `global.json`'s top-level
//!   `msbuild-sdks` map. It selects the package version exactly, and
//!   never the host SDK: a reference to an SDK the running SDK ships is
//!   served from it at any version.
//! - **NuGet is only consulted when a version source is present.**
//!   Upstream's `Microsoft.Build.NuGetSdkResolver` refuses to scan
//!   the cache for a "best version" without one (the resource string
//!   is verbatim: "did not resolve this SDK because there was no
//!   version specified in the project or global.json"). Silently
//!   picking the highest restored copy would import a different
//!   SDK than MSBuild itself would, parsing against the wrong
//!   `Sdk.props`/`Sdk.targets`.
//! - Pure filesystem walk. No `$DOTNET_ROOT` / `$NUGET_PACKAGES`
//!   discovery here — the shell passes the paths in (dependency
//!   rejection).
//!
//! Custom-SDK entry stems other than `Sdk.{props,targets}` (e.g.
//! `Sdk.Web.props` referenced from
//! `<Import Sdk="X" Project="Sdk.Web.props"/>`) are handled by the
//! evaluator: it resolves them against [`SdkPaths::root`], which the
//! resolver populates with the directory containing the well-known
//! pair.

use std::cmp::Ordering;
use std::path::{Path, PathBuf};

use crate::dotnet_io;
use crate::observed::{self, Observer};
use crate::{SdkPaths, SdkResolution};
use version_spec::{RollForward, VersionSpec, select_sdk_version};

/// Why [`locate_dotnet_sdk`] (or any caller-supplied
/// [`crate::SdkResolver`]) failed to produce paths. Distinguishes
/// configuration-side failures so the evaluator can emit the right
/// diagnostic — `SdkNotFound` if the SDK itself isn't installed,
/// `SdkVersionNotSatisfied` if it is installed but no version matches
/// the [`VersionSpec`] from `global.json` (or an MSBuild `Sdk=
/// "Name/Version"` per-import pin).
///
/// The two variants are deliberately not collapsed into a single
/// "could not resolve" — a user with one SDK installed and a pinned
/// `global.json` they forgot to update gets a different remediation
/// path (install `9.0.300`) than one whose `.fsproj` names a nonexistent
/// `Microsoft.Build.MadeUp.Sdk` (check the spelling).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SdkResolveError {
    /// Neither root serves the named SDK: the host SDK the spec selects has
    /// no `Sdks/{name}/Sdk` directory, and NuGet has no restored copy.
    /// Also the catch-all for "dotnet_root doesn't exist" and "sdk_name
    /// has shape we refuse to splice into a filesystem path".
    NotFound,
    /// An installed version of the requested SDK exists, but none
    /// satisfies the [`VersionSpec`]. The caller can present
    /// `available` (sorted ascending) and `spec` to the user. The
    /// version strings are the raw directory names — preserving any
    /// prerelease suffix so the user sees what the resolver actually
    /// looked at.
    VersionNotSatisfied {
        spec: VersionSpec,
        available: Vec<SdkVersion>,
    },
    /// The SDK is a resolver-backed locator (the workload locators) and
    /// was recognised, but the on-disk state is outside the layout
    /// envelope [`workloads`] can resolve *exactly* — a workload set,
    /// an install-state pin, ambiguous manifest versions, a user-local
    /// install with no supplied root. Resolving approximately could
    /// import the wrong file set, so the resolver declines (the
    /// "degrade, don't guess" rule).
    UnsupportedLayout { reason: String },
}

impl std::fmt::Display for SdkResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SdkResolveError::NotFound => {
                write!(f, "no installed .NET SDK provides the requested name")
            }
            SdkResolveError::VersionNotSatisfied { spec, available } => {
                write!(f, "no installed .NET SDK satisfies the version spec (")?;
                match spec.version() {
                    Some(v) => write!(f, "pin={v}")?,
                    None => write!(f, "pin=<none>")?,
                }
                write!(
                    f,
                    ", roll_forward={:?}, allow_prerelease={}); available: [",
                    spec.roll_forward(),
                    spec.allow_prerelease(),
                )?;
                let mut first = true;
                for v in available {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    write!(f, "{v}")?;
                }
                f.write_str("]")
            }
            SdkResolveError::UnsupportedLayout { reason } => {
                write!(
                    f,
                    "the workload layout on disk is outside the envelope we \
                     resolve exactly: {reason}"
                )
            }
        }
    }
}

impl std::error::Error for SdkResolveError {}

/// Locate the SDK named `sdk_name` as MSBuild's resolvers do: the running
/// host SDK's own copy under `dotnet_root`, else the workload pack of that
/// id, else a restored copy in the per-user NuGet package cache.
///
/// The three, in the order MSBuild consults them:
///
/// - **`$DOTNET_ROOT`** —
///   `{dotnet_root}/sdk/{version}/Sdks/{sdk_name}/Sdk/Sdk.{props,targets}`.
///   Used by the in-box SDKs (`Microsoft.NET.Sdk`, `Microsoft.NET.Sdk.Web`,
///   …). `spec` (from `global.json`'s `sdk` block) selects the host SDK
///   version among all installed ones, and only that version is asked for
///   `sdk_name`. MSBuild's default resolver serves its copy wherever
///   `Directory.Exists` finds it, whatever version the reference names,
///   and before NuGet's resolver is asked; it never tries another installed
///   version.
/// - **Workload packs** — the workload SDK resolver (priority 4000, ahead of
///   NuGet's 6000) looks the name up as a workload pack id
///   ([`workloads::resolve_workload_pack`], under `workload_env`) wherever the
///   running SDK does not ship it. An installed pack serves its `Sdk` folder;
///   no pack of the name for the host passes the name on to NuGet. Its
///   manifests load before it answers, so a workload state we cannot resolve
///   exactly declines every name the running SDK does not ship.
/// - **NuGet package cache** —
///   `{nuget_packages_dir}/{sdk_name.to_ascii_lowercase()}/{version}/{Sdk,sdk}/Sdk.{props,targets}`.
///   Used by every NuGet-distributed SDK (`Microsoft.DotNet.Arcade.Sdk`,
///   `Microsoft.Build.NoTargets`, `MSBuild.Sdk.Extras`, …), and consulted
///   only when the host SDK does not ship `sdk_name` and a version source
///   names a version. NuGet's resolver serves the inner `Sdk/`
///   (Microsoft canonical) where it exists, and `sdk/` (used by
///   `Microsoft.DotNet.Arcade.Sdk` et al.) otherwise. A version counts only
///   where NuGet's restore marker is. Pass `None` to skip the NuGet probe
///   entirely; pass `Some(dir)` even if the directory doesn't yet exist.
///
/// **Version sources.** A per-import pin (`Sdk="Name/Version"`, e.g.
/// `Microsoft.Build.NoTargets/1.0.80`), else the name's entry in the
/// supplied `global.json` `msbuild-sdks` map, names the package version
/// NuGet looks for, exactly. Neither constrains the host SDK, and neither
/// keeps the host SDK's copy from being served. Without one, NuGet is not
/// consulted: upstream's `Microsoft.Build.NuGetSdkResolver` refuses to scan
/// the cache for a "best version", and `spec` is not a version source.
///
/// Failure modes:
///
/// - [`SdkResolveError::VersionNotSatisfied`] when host SDKs are installed
///   but `spec` admits none of them (the .NET host then runs no build), or
///   when the host SDK does not ship the name and NuGet has versions of it
///   but not the one named. `spec` and `available` are the host's, or the
///   pin and NuGet's versions respectively.
/// - [`SdkResolveError::NotFound`] when neither serves the name: the
///   selected host SDK has no `Sdks/{name}/Sdk`, and NuGet is not
///   consulted or has no version of it.
/// - [`SdkResolveError::UnsupportedLayout`] if the directory a resolver
///   serves lacks a regular `Sdk.props` or `Sdk.targets` (MSBuild then
///   fails the import), NuGet serves a directory that does not exist, the
///   NuGet folder NuGet would consult is a relative path, the workload
///   resolver's state is outside what [`workloads`] certifies, or the name is
///   a workload pack that is not installed (MSBuild then imports nothing and
///   adds a `MissingWorkloadPack` item, which the walk does not model).
///
/// The function does not canonicalise the returned paths; they are
/// `dotnet_root.join("sdk").join(...)`, a pack root's `packs/...` or
/// `nuget_packages_dir.join(lowercased_name)...` literally, so the
/// caller can tell which root won by inspecting the path components.
///
/// ```no_run
/// use std::path::PathBuf;
/// use borzoi_msbuild::{locate_dotnet_sdk, parse_fsproj_with_imports, workloads};
///
/// let dotnet_root = PathBuf::from("/usr/local/share/dotnet");
/// let nuget = PathBuf::from("/Users/me/.nuget/packages");
/// let workload_env = workloads::WorkloadEnvironment {
///     user_dotnet_root: None,
///     overrides_present: false,
///     global_json: Default::default(),
///     process_architecture: None,
/// };
/// let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
///     locate_dotnet_sdk(&dotnet_root, Some(&nuget), name, None, None, &workload_env, observer)
/// };
/// // pass `Some(&resolver)` to parse_fsproj_with_imports.
/// # let _ = resolver;
/// ```
pub fn locate_dotnet_sdk(
    dotnet_root: &Path,
    nuget_packages_dir: Option<&Path>,
    sdk_name: &str,
    spec: Option<&VersionSpec>,
    msbuild_sdks: Option<&std::collections::BTreeMap<String, SdkVersion>>,
    workload_env: &workloads::WorkloadEnvironment<'_>,
    observer: &Observer,
) -> Result<SdkPaths, SdkResolveError> {
    // MSBuild allows `Sdk="Name/Version"` (e.g.
    // `Sdk="Microsoft.Build.NoTargets/1.0.80"`): the version half names
    // the package version NuGet's resolver looks for.
    //
    // The version half is also *validated* — anything that isn't
    // SemVer-shape (`Foo/`, `Foo/../Bar`, multi-SDK joined strings
    // like `Foo/1.0;Other/2.0`) is rejected outright rather than
    // silently degenerated to a bare-name lookup. Better a
    // `NotFound` diagnostic on the caller side than a wrong
    // partial resolution.
    let (name, per_import_version) = match sdk_name.split_once('/') {
        Some((n, v)) => match SdkVersion::parse(v) {
            Some(parsed) => (n, Some(parsed)),
            None => return Err(SdkResolveError::NotFound),
        },
        None => (sdk_name, None),
    };

    // Refuse to interpolate anything that could escape either root's
    // containment via `PathBuf::join`. `join("/abs")` discards the
    // prefix; `..` climbs out. Real .NET SDK and NuGet package names
    // are dot-separated identifiers, so the strict filter doesn't
    // exclude any legitimate SDK.
    if !is_safe_sdk_name(name) {
        return Err(SdkResolveError::NotFound);
    }

    // 1. The running SDK's copy. The host SDK is chosen by `spec` alone and
    //    only then asked for `name`: MSBuild's default resolver serves
    //    `$(MSBuildSDKsPath)/{name}/Sdk` of the SDK that runs, at any
    //    version the reference names, ahead of NuGet.
    let host_versions = host_sdk_versions(dotnet_root, observer);
    let dotnet_versions: Vec<SdkVersion> = host_versions.iter().map(|(v, _)| v.clone()).collect();
    if !dotnet_versions.is_empty() {
        let Some(version) = select_sdk_version(&dotnet_versions, spec) else {
            // The .NET host finds no SDK to run, so no resolver runs.
            let mut available = dotnet_versions;
            available.sort();
            return Err(SdkResolveError::VersionNotSatisfied {
                spec: spec
                    .expect("with no spec, the max candidate is always selected when any exist")
                    .clone(),
                available,
            });
        };
        let idx = dotnet_versions
            .iter()
            .position(|v| v == version)
            .expect("selection returns a candidate from the slice");
        let host_dir = &host_versions[idx].1;
        let sdk_root = host_dir.join("Sdks").join(name).join("Sdk");
        if let Some(root) = sdk_directory(sdk_root, observer)? {
            return Ok(sdk_paths(root));
        }
        // 2. The workload SDK resolver of the running SDK. A locator name
        //    is [`resolve_sdk`]'s to route before it reaches here.
        if !workloads::is_workload_locator(name) {
            match workloads::resolve_workload_pack(
                name,
                dotnet_root,
                host_dir,
                workload_env,
                observer,
            )? {
                workloads::WorkloadPackResolution::NotAPack => {}
                workloads::WorkloadPackResolution::Installed(root) => {
                    return Ok(sdk_paths(root));
                }
                workloads::WorkloadPackResolution::Missing { version } => {
                    return Err(SdkResolveError::UnsupportedLayout {
                        reason: format!(
                            "the workload pack {name} {version} is not installed, so MSBuild \
                             imports nothing and adds a MissingWorkloadPack item, which is \
                             not modelled"
                        ),
                    });
                }
            }
        }
    }

    // 3. NuGet, only with a version source: the per-import version, else the
    //    `msbuild-sdks` entry. Upstream's `Microsoft.Build.NuGetSdkResolver`
    //    refuses to scan the cache for a "best version" without one, and
    //    picking the highest restored copy could import a different SDK
    //    than MSBuild would. The caller `spec` does not count.
    let Some(pin) = per_import_version.or_else(|| msbuild_sdks.and_then(|m| m.get(name).cloned()))
    else {
        return Err(SdkResolveError::NotFound);
    };
    let Some(nuget_packages_dir) = nuget_packages_dir else {
        return Err(SdkResolveError::NotFound);
    };
    // NuGet's `File.Exists` of a restore marker takes a relative folder
    // against the process's working directory, which we cannot see.
    if !nuget_packages_dir.has_root() {
        return Err(SdkResolveError::UnsupportedLayout {
            reason: "the NuGet package folder is a relative path".to_owned(),
        });
    }
    let pin_spec = VersionSpec::with_version(pin, RollForward::Disable, true);
    let nuget_candidates = collect_from_nuget(nuget_packages_dir, name, observer);
    let nuget_versions: Vec<SdkVersion> = nuget_candidates.iter().map(|(v, _)| v.clone()).collect();
    match select_sdk_version(&nuget_versions, Some(&pin_spec)) {
        Some(version) => {
            let idx = nuget_versions
                .iter()
                .position(|v| v == version)
                .expect("selection returns a candidate from the slice");
            nuget_served(nuget_candidates[idx].1.clone(), observer).map(sdk_paths)
        }
        None if nuget_versions.is_empty() => Err(SdkResolveError::NotFound),
        None => {
            let mut available = nuget_versions;
            available.sort();
            Err(SdkResolveError::VersionNotSatisfied {
                spec: pin_spec,
                available,
            })
        }
    }
}

/// The well-known pair in the SDK directory `root`.
fn sdk_paths(root: PathBuf) -> SdkPaths {
    SdkPaths {
        props: root.join("Sdk.props"),
        targets: root.join("Sdk.targets"),
        root,
    }
}

/// The installed SDK versions under `{dotnet_root}/sdk`, as hostfxr counts
/// them: every entry whose name parses as a version, that is a directory or
/// a link to one (Nix's wrapped .NET links each `sdk/{version}`), and that
/// holds a `dotnet.dll` `access(F_OK)` finds. That follows links and asks
/// nothing of the entry's kind, so a directory, a socket or a FIFO of that
/// name counts and a dangling link does not ([`observed::exists`];
/// `sdk_directory_probe_diff` grades it against hostfxr's trace). Empty when
/// `sdk/` cannot be listed.
fn host_sdk_versions(dotnet_root: &Path, observer: &Observer) -> Vec<(SdkVersion, PathBuf)> {
    let Ok(entries) = observed::read_dir(observer, &dotnet_root.join("sdk")) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for entry in entries.into_iter().flatten() {
        let Some(version) = entry.name.to_str().and_then(SdkVersion::parse) else {
            continue;
        };
        if observed::is_dir(observer, &entry.path)
            && observed::exists(observer, &entry.path.join("dotnet.dll"))
        {
            out.push((version, entry.path));
        }
    }
    out
}

/// What the resolver that found `sdk_root` serves: `Some(sdk_root)` when
/// `Directory.Exists` finds it and both `Sdk.props` and `Sdk.targets` in it
/// are regular files; `None` when `Directory.Exists` does not find it.
///
/// Both MSBuild's default resolver and NuGet's take the directory on
/// `Directory.Exists` alone. Where a file is then missing, a dangling link,
/// or no regular file, MSBuild fails the import (MSB4019, MSB4024), or never
/// finishes reading it (a FIFO); this declines that, rather than resolving
/// elsewhere (`sdk_directory_probe_diff` grades both resolvers' rule against
/// `dotnet msbuild`). `Directory.Exists` follows links (`stat`), and the
/// paths here hold no `..` for .NET to collapse, so it is
/// [`observed::is_dir`].
fn sdk_directory(
    sdk_root: PathBuf,
    observer: &Observer,
) -> Result<Option<PathBuf>, SdkResolveError> {
    if !observed::is_dir(observer, &sdk_root) {
        return Ok(None);
    }
    for file in ["Sdk.props", "Sdk.targets"] {
        if !observed::is_file(observer, &sdk_root.join(file)) {
            return Err(SdkResolveError::UnsupportedLayout {
                reason: format!(
                    "the SDK directory {} has no regular {file}, so MSBuild fails to import it",
                    sdk_root.display()
                ),
            });
        }
    }
    Ok(Some(sdk_root))
}

/// The directory NuGet's resolver serves, `sdk_root`, judged as
/// [`sdk_directory`] judges it. NuGet serves it whether or not it exists, so
/// its absence fails the import rather than letting another root answer.
fn nuget_served(sdk_root: PathBuf, observer: &Observer) -> Result<PathBuf, SdkResolveError> {
    match sdk_directory(sdk_root.clone(), observer)? {
        Some(root) => Ok(root),
        None => Err(SdkResolveError::UnsupportedLayout {
            reason: format!(
                "NuGet serves the SDK directory {}, which does not exist",
                sdk_root.display()
            ),
        }),
    }
}

/// The restored versions of the package `sdk_name` in
/// `{nuget_packages_dir}/{sdk_name.to_ascii_lowercase()}/`, each with the
/// directory NuGet's MSBuild SDK resolver serves for it.
///
/// **Name lowercasing.** NuGet stores packages in lowercased
/// directories regardless of the casing in the project file. We mirror
/// the `dotnet` CLI's normalisation so a `<Project
/// Sdk="Microsoft.DotNet.Arcade.Sdk">` resolves against the package
/// stored at `microsoft.dotnet.arcade.sdk/`.
///
/// **Installed.** NuGet takes a version as restored only where its
/// `.nupkg.metadata` or its `{id}.{version}.nupkg.sha512` exists (CLR
/// `File.Exists`); a version directory with neither is one it restores
/// again, so it is no candidate here.
///
/// **Inner directory casing.** The folder name inside the package is
/// package-defined — Microsoft.Build.NoTargets, Microsoft.NET.ILLink.Tasks,
/// Microsoft.Net.Sdk.WindowsDesktop, Microsoft.Build.Traversal etc. ship
/// `Sdk/` (capital, Microsoft's canonical convention); Microsoft.DotNet
/// .Arcade.Sdk and friends ship `sdk/` (lowercase). NuGet's resolver serves
/// `Sdk/` where `Directory.Exists` finds it and `sdk/` otherwise, whether or
/// not that exists, so [`sdk_directory`] judges the one it serves.
///
/// A missing or unreadable package directory yields an empty vector —
/// the same fall-through as an empty [`host_sdk_versions`].
fn collect_from_nuget(
    nuget_packages_dir: &Path,
    sdk_name: &str,
    observer: &Observer,
) -> Vec<(SdkVersion, PathBuf)> {
    let id = sdk_name.to_ascii_lowercase();
    let pkg_dir = nuget_packages_dir.join(&id);
    let Ok(entries) = observed::read_dir(observer, &pkg_dir) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for entry in entries.into_iter().flatten() {
        let Some(dir_name) = entry.name.to_str().map(str::to_owned) else {
            continue;
        };
        let Some(version) = SdkVersion::parse(&dir_name) else {
            continue;
        };
        let version_dir = entry.path;
        let installed = dotnet_io::file_exists(observer, &version_dir.join(".nupkg.metadata"))
            || dotnet_io::file_exists(
                observer,
                &version_dir.join(format!("{id}.{dir_name}.nupkg.sha512")),
            );
        if !installed {
            continue;
        }
        let upper = version_dir.join("Sdk");
        let sdk_root = if observed::is_dir(observer, &upper) {
            upper
        } else {
            version_dir.join("sdk")
        };
        out.push((version, sdk_root));
    }
    out
}

/// True if `name` is a safe single-component identifier we can splice
/// into a filesystem path without risking traversal. Allows ASCII
/// letters, digits, `.`, `-`, `_`. Real .NET SDK names
/// (`Microsoft.NET.Sdk`, `Microsoft.NET.Sdk.Web`, third-party SDKs
/// like `Microsoft.Build.NoTargets`) all fit, so the filter doesn't
/// reject any valid input.
///
/// Rejects empties, `..`, and anything containing `/`, `\`, NUL, or
/// other separators — values that would let `PathBuf::join` discard
/// the `{dotnet_root}/sdk/{version}/Sdks/` prefix (`join("/abs")`) or
/// climb out of it (`join("..")`).
fn is_safe_sdk_name(name: &str) -> bool {
    if name.is_empty() || name == ".." || name == "." {
        return false;
    }
    name.bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-' || b == b'_')
}

/// Parsed view of a .NET SDK version directory name. Lexicographic
/// comparison would mis-order `9.0.100` before `10.0.100`; this type
/// implements `Ord` so the highest-version pick is deterministic.
///
/// Comparison rule (matches the SemVer 2 "stable beats prerelease"
/// convention, simplified):
///
/// 1. Compare the numeric components element-wise. Missing trailing
///    components count as zero, so `8.0` < `8.0.1`.
/// 2. If the numeric components tie, a version *without* a prerelease
///    suffix is greater than one *with* a suffix. Within prereleases,
///    fall back to lexicographic comparison of the suffix — good
///    enough for the LSP's "pick the freshest" need, even though real
///    SemVer 2 dot-segments the prerelease.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SdkVersion {
    numeric: Vec<u64>,
    prerelease: Option<String>,
}

impl SdkVersion {
    /// First numeric component, or `0` if the version has none (which
    /// `parse` never produces but the type permits structurally).
    pub fn major(&self) -> u64 {
        self.numeric.first().copied().unwrap_or(0)
    }

    /// Second numeric component, zero-padded if missing.
    pub fn minor(&self) -> u64 {
        self.numeric.get(1).copied().unwrap_or(0)
    }

    /// "Feature band" of a .NET SDK version: the third numeric
    /// component integer-divided by 100. `9.0.100` → band 1.
    /// `9.0.401` → band 4. `8.0` → band 0 (third component zero-padded).
    /// Patches within a band share the band but differ in the last
    /// two digits.
    pub fn feature_band(&self) -> u64 {
        self.numeric.get(2).copied().unwrap_or(0) / 100
    }

    /// True iff the version carries a SemVer prerelease suffix.
    pub fn is_prerelease(&self) -> bool {
        self.prerelease.is_some()
    }

    /// Parse a directory-name string into a version, or return `None`
    /// if it doesn't look like a `\d+(\.\d+)*(-.*)?` form. Real .NET
    /// SDK names always do (`8.0.401`, `9.0.100-preview.1.24101.2`,
    /// `9.0.100-rc.2.24474.11`), so a stricter parse would be no
    /// better. Non-matching directories — `NuGetFallbackFolder`,
    /// hidden files — are filtered out by returning `None`.
    pub fn parse(name: &str) -> Option<SdkVersion> {
        let (numeric_part, prerelease) = match name.split_once('-') {
            Some((head, tail)) => (head, Some(tail.to_owned())),
            None => (name, None),
        };
        if numeric_part.is_empty() {
            return None;
        }
        // SemVer 2.0.0 prereleases are dot-separated identifiers
        // matching `[0-9A-Za-z-]+`. Beyond the alphabet, §9 requires
        // that each identifier be non-empty and that all-digit
        // identifiers carry no leading zeroes — otherwise `preview.01`
        // would parse to a distinct `SdkVersion` from `preview.1`,
        // but `cmp_prerelease_identifier` reports them `Equal` under
        // numeric comparison, breaking `a == b iff cmp(a,b) == Equal`.
        //
        // The alphabet check additionally matters because `parse`
        // doubles as the validator for the `Sdk="Name/Version"`
        // version half in `locate_dotnet_sdk`. Without it, a
        // multi-SDK string like `Foo/1.0.0-preview.1;Bar/2.0` would
        // parse cleanly (the tail after `-` swallowed opaquely) and
        // the resolver would silently splice only `Foo`.
        if let Some(suffix) = prerelease.as_deref() {
            if suffix.is_empty() {
                return None;
            }
            for ident in suffix.split('.') {
                if ident.is_empty() {
                    return None;
                }
                if !ident
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-')
                {
                    return None;
                }
                let all_digits = ident.bytes().all(|b| b.is_ascii_digit());
                if all_digits && ident.len() > 1 && ident.starts_with('0') {
                    return None;
                }
            }
        }
        let mut numeric = Vec::new();
        for component in numeric_part.split('.') {
            numeric.push(component.parse::<u64>().ok()?);
        }
        if numeric.is_empty() {
            return None;
        }
        // Strip trailing zeros so `8.0` and `8.0.0` compare equal under
        // both `Ord` (which zero-pads) and `PartialEq` (which is
        // derived structurally). Without this the two would disagree
        // and violate `a == b iff a.cmp(b) == Equal`.
        while numeric.len() > 1 && *numeric.last().unwrap() == 0 {
            numeric.pop();
        }
        Some(SdkVersion {
            numeric,
            prerelease,
        })
    }
}

impl std::fmt::Display for SdkVersion {
    /// Round-trips a `SdkVersion` to the directory-name form
    /// `parse` accepts. Trailing-zero stripping in `parse` means
    /// `parse("8.0.0")` produces the same `SdkVersion` as
    /// `parse("8.0")` and `Display` prints `"8.0"` — by design,
    /// since the two refer to the same on-disk SDK and we want
    /// equality and printed form to agree.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for n in &self.numeric {
            if !first {
                f.write_str(".")?;
            }
            first = false;
            write!(f, "{n}")?;
        }
        if let Some(suffix) = &self.prerelease {
            write!(f, "-{suffix}")?;
        }
        Ok(())
    }
}

impl Ord for SdkVersion {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_len = self.numeric.len();
        let other_len = other.numeric.len();
        for i in 0..self_len.max(other_len) {
            let a = self.numeric.get(i).copied().unwrap_or(0);
            let b = other.numeric.get(i).copied().unwrap_or(0);
            match a.cmp(&b) {
                Ordering::Equal => continue,
                non_eq => return non_eq,
            }
        }
        // Numeric tie. Stable (None) beats prerelease (Some).
        match (&self.prerelease, &other.prerelease) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater,
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => cmp_prerelease(a, b),
        }
    }
}

/// Compare two SemVer prerelease tails per spec §11.4:
///
/// - Split on `.` into identifiers.
/// - Identifiers consisting only of ASCII digits compare numerically.
/// - Identifiers containing any non-digit compare lexically (ASCII).
/// - Numeric identifiers have lower precedence than alphanumeric.
/// - When one tail is a strict prefix of the other, the shorter one
///   has lower precedence.
///
/// A naive `str::cmp` gets the numeric-identifier case wrong:
/// `preview.10` comes before `preview.2` lexically (because the digit
/// `1` precedes `2`), so the SDK resolver could prefer a strictly older
/// SDK.
fn cmp_prerelease(a: &str, b: &str) -> Ordering {
    let mut a_iter = a.split('.');
    let mut b_iter = b.split('.');
    loop {
        match (a_iter.next(), b_iter.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(ai), Some(bi)) => match cmp_prerelease_identifier(ai, bi) {
                Ordering::Equal => continue,
                non_eq => return non_eq,
            },
        }
    }
}

fn cmp_prerelease_identifier(a: &str, b: &str) -> Ordering {
    match (a.parse::<u64>().ok(), b.parse::<u64>().ok()) {
        (Some(x), Some(y)) => x.cmp(&y),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => a.cmp(b),
    }
}

impl PartialOrd for SdkVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// Pure version-selection types and logic. Public via this module so
// the `global_json` parser and out-of-crate callers can construct
// `VersionSpec` values to hand to `locate_dotnet_sdk`.
pub mod version_spec;

// `global.json` upward discovery + JSONC parsing; the module's own header
// documents it. An outer `///` here would merge with that header and resolve
// the whole merged doc — including the header's unqualified links — in *this*
// module's scope.
pub mod global_json;

/// Workload locator SDK resolution (Stage B of
/// `docs/completed/sdk-chain-exactness-plan.md`).
pub mod workloads;

/// Locator-aware resolution entry point: the workload locator names
/// route to [`workloads::resolve_workload_locator`] against the host
/// SDK version directory the spec selects; every other name is
/// [`locate_dotnet_sdk`] as before, wrapped as a single-root
/// [`SdkResolution`].
pub fn resolve_sdk(
    dotnet_root: &Path,
    nuget_packages_dir: Option<&Path>,
    sdk_name: &str,
    spec: Option<&VersionSpec>,
    msbuild_sdks: Option<&std::collections::BTreeMap<String, SdkVersion>>,
    workload_env: &workloads::WorkloadEnvironment<'_>,
    observer: &Observer,
) -> Result<SdkResolution, SdkResolveError> {
    if workloads::is_workload_locator(sdk_name) {
        let version_dir = running_sdk_dir(dotnet_root, spec, observer)?;
        return workloads::resolve_workload_locator(
            sdk_name,
            dotnet_root,
            &version_dir,
            workload_env,
            observer,
        );
    }
    locate_dotnet_sdk(
        dotnet_root,
        nuget_packages_dir,
        sdk_name,
        spec,
        msbuild_sdks,
        workload_env,
        observer,
    )
    .map(SdkResolution::from)
}

/// The version of `sdk_name` that [`resolve_sdk`] looks for in the NuGet
/// package folder: its per-import `Name/Version` pin, else its
/// `msbuild-sdks` entry (NuGet's MSBuild SDK resolver has no other version
/// source). `None` when it has neither, when the per-import version does not
/// parse (which [`locate_dotnet_sdk`] rejects outright), or when the name is
/// a workload locator (which never reaches NuGet). Then the resolution reads
/// no NuGet package folder at all: [`resolve_sdk`] answers the same whatever
/// folder it is handed, `None` included, so a caller that cannot say which
/// folder NuGet would use need decline only the names this returns `Some`
/// for.
pub fn nuget_package_version(
    sdk_name: &str,
    msbuild_sdks: Option<&std::collections::BTreeMap<String, SdkVersion>>,
) -> Option<SdkVersion> {
    if workloads::is_workload_locator(sdk_name) {
        return None;
    }
    match sdk_name.split_once('/') {
        Some((_, version)) => SdkVersion::parse(version),
        None => msbuild_sdks.and_then(|pins| pins.get(sdk_name).cloned()),
    }
}

/// The `{dotnet_root}/sdk/{version}` directory of the SDK hostfxr runs from
/// `dotnet_root` under `spec` (the highest installed version when
/// unconstrained): `host_sdk_versions`, selected by version alone, as
/// [`locate_dotnet_sdk`] selects it. It is the SDK whose
/// `KnownWorkloadManifests.txt` drives workload locator resolution, and,
/// across a `global.json`'s `sdk.paths`, hostfxr runs from the first root
/// where this is `Ok` (`sdk_paths_root_choice_diff`). No installed version
/// at all is `NotFound`; installed versions all rejected by the spec is
/// `VersionNotSatisfied` with the sorted available list, matching ordinary
/// SDK resolution's diagnostic split.
pub fn running_sdk_dir(
    dotnet_root: &Path,
    spec: Option<&VersionSpec>,
    observer: &Observer,
) -> Result<PathBuf, SdkResolveError> {
    let mut candidates = host_sdk_versions(dotnet_root, observer);
    if candidates.is_empty() {
        return Err(SdkResolveError::NotFound);
    }
    let versions: Vec<SdkVersion> = candidates.iter().map(|(v, _)| v.clone()).collect();
    let Some(chosen) = select_sdk_version(&versions, spec) else {
        let mut available = versions;
        available.sort();
        return Err(SdkResolveError::VersionNotSatisfied {
            spec: spec
                .expect("with no spec, the max candidate is always selected when any exist")
                .clone(),
            available,
        });
    };
    let index = versions
        .iter()
        .position(|v| v == chosen)
        .expect("selection returns a candidate from the slice");
    Ok(candidates.swap_remove(index).1)
}

#[cfg(test)]
mod tests;
