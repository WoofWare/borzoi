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
//! - Resolve as the resolvers MSBuild consults do: the `$DOTNET_ROOT`
//!   half picks the host SDK by version alone and then serves its
//!   `Sdks/{name}/Sdk` (MSBuild's default resolver), and the NuGet half
//!   serves a restored package's `Sdk/`, else its `sdk/` (NuGet's
//!   resolver). Both take the directory on `Directory.Exists`; one whose
//!   `Sdk.props` or `Sdk.targets` is then no regular file declines, since
//!   MSBuild fails to import it ([`SdkPaths`] names both).
//! - Apply an optional [`VersionSpec`]
//!   (typically derived from `global.json` by [`global_json`]) to the
//!   `$DOTNET_ROOT` candidate set only — `global.json`'s `sdk.version`
//!   constrains the host .NET SDK install, not third-party NuGet
//!   Project SDK packages.
//! - Honor a per-import pin `Sdk="Name/Version"` when present: the
//!   version half names a specific package version, applied to *both*
//!   roots with `Disable` semantics and overriding the caller's
//!   `spec` for this lookup. This is the canonical way to pin a
//!   NuGet-distributed Project SDK.
//! - Honor a `global.json` `msbuild-sdks` entry for the requested
//!   name when no per-import pin is present: same `Disable`
//!   semantics, same "applies to both roots, overrides caller `spec`"
//!   behaviour. Per-import pin wins when both sources apply.
//! - **NuGet is only consulted when a version source is present.**
//!   Upstream's `Microsoft.Build.NuGetSdkResolver` refuses to scan
//!   the cache for a "best version" without one (the resource string
//!   is verbatim: "did not resolve this SDK because there was no
//!   version specified in the project or global.json"). Silently
//!   picking the highest restored copy would import a different
//!   SDK than MSBuild itself would, parsing against the wrong
//!   `Sdk.props`/`Sdk.targets`. The recognised version sources are a
//!   per-import pin (`Sdk="Name/Version"`) and the top-level
//!   `msbuild-sdks` map in `global.json`.
//! - Among admitted candidates in each root, prefer the highest
//!   installed; among versions with the same numeric prefix, stable
//!   releases beat prereleases (any `-suffix`).
//! - When both roots produce a candidate, the `$DOTNET_ROOT` pick wins
//!   on tie or strict-higher; NuGet wins only when its max strictly
//!   exceeds the `$DOTNET_ROOT` pick. Under the current "NuGet only
//!   with per-import pin" rule both sides filter by the same exact
//!   version, so in practice cross-root divergence resolves to either
//!   a tie (DOTNET wins) or a one-sided hit — the strictly-higher
//!   branch is unreachable but kept structurally.
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

/// Locate the SDK named `sdk_name` under `dotnet_root`'s installed SDK
/// directories and (optionally) the per-user NuGet package cache,
/// subject to an optional [`VersionSpec`] constraint.
///
/// Two on-disk layouts are probed independently:
///
/// - **`$DOTNET_ROOT`** —
///   `{dotnet_root}/sdk/{version}/Sdks/{sdk_name}/Sdk/Sdk.{props,targets}`.
///   Used by the in-box SDKs (`Microsoft.NET.Sdk`, `Microsoft.NET.Sdk.Web`,
///   …). The `spec` (when supplied) selects the host SDK version among all
///   installed ones, and only that version is asked for `sdk_name`: MSBuild
///   serves the running SDK's copy or fails, and never tries another
///   version.
/// - **NuGet package cache** —
///   `{nuget_packages_dir}/{sdk_name.to_ascii_lowercase()}/{version}/{Sdk,sdk}/Sdk.{props,targets}`.
///   Used by every NuGet-distributed SDK (`Microsoft.DotNet.Arcade.Sdk`,
///   `Microsoft.Build.NoTargets`, `MSBuild.Sdk.Extras`, …). The inner
///   directory's casing is package-defined; NuGet's resolver serves
///   `Sdk/` (Microsoft canonical, used by `Microsoft.Build.NoTargets`
///   et al.) where it exists, and `sdk/` (used by
///   `Microsoft.DotNet.Arcade.Sdk` et al.) otherwise. A version counts
///   only where NuGet's restore marker is.
///   Pass `None` to skip the NuGet probe entirely; pass `Some(dir)`
///   even if the directory doesn't yet exist (the probe tolerates
///   that — same fall-through as a `$DOTNET_ROOT/sdk` that isn't there).
///
/// **Scope of `spec`.** `global.json`'s `sdk.version` constrains the
/// *.NET SDK install*, not third-party MSBuild Project SDK package
/// versions. So `spec` filters the `$DOTNET_ROOT` candidate set
/// (via `version_spec::select_sdk_version`)
/// and does **not** filter NuGet candidates.
///
/// **Per-import version pin.** If `sdk_name` has the
/// `"Name/Version"` shape (e.g. `Microsoft.Build.NoTargets/1.0.80`),
/// the version half names a specific package version and is honored
/// directly with `Disable` semantics: both roots are filtered to the
/// exact pin. The per-import pin overrides any caller `spec` for
/// this lookup — the project is making a specific request about
/// *this* SDK package, which is a different question from
/// `global.json`'s host-SDK version pin.
///
/// **`msbuild-sdks` pins.** The top-level `msbuild-sdks` map in
/// `global.json` (e.g. `"Microsoft.Build.NoTargets": "3.7.0"`) names
/// an exact version for the given SDK. When the project file does
/// *not* carry a per-import version pin, an entry matching `sdk_name`
/// in the supplied map is used as the pin — same `Disable` semantics
/// and same "applies to both roots, overrides caller spec" behaviour
/// as a per-import pin. A per-import pin takes precedence: it's the
/// more specific request, written directly at the import site. Pass
/// `None` to skip msbuild-sdks pin lookup entirely (the v1 behaviour
/// before this map was wired).
///
/// **NuGet requires a version source.** The NuGet cache is only
/// consulted when there's a pin — either a per-import pin
/// (`Sdk="Name/Version"`) or an `msbuild-sdks` entry. Without one,
/// NuGet candidates are not considered: upstream's
/// `Microsoft.Build.NuGetSdkResolver` refuses to scan the cache for
/// a "best version" without a version source, and silently picking
/// the highest restored copy could import a different SDK than
/// MSBuild itself would. The caller `spec` does *not* count as a
/// NuGet version source — its scope is the host .NET SDK only.
///
/// Returns the [`SdkPaths`] picked as follows:
///
/// - If only one root produces a candidate, that one wins.
/// - If both produce a candidate, the `$DOTNET_ROOT` pick wins on
///   tie or strict-higher (matching MSBuild's "shared over per-user"
///   preference). NuGet can only beat DOTNET when both filter by the
///   same per-import pin (the version source rule above) and DOTNET
///   doesn't have that version — in which case DOTNET's pick is
///   `None` and we land in the one-sided branch.
///
/// Failure modes:
///
/// - [`SdkResolveError::NotFound`] if neither root serves the requested
///   name: the selected host SDK has no `Sdks/{name}/Sdk`, and NuGet has
///   no restored copy the effective spec admits. Includes the case
///   of an unpinned reference to a NuGet-only SDK: upstream
///   matches.
/// - [`SdkResolveError::UnsupportedLayout`] if the directory a resolver
///   serves lacks a regular `Sdk.props` or `Sdk.targets` (MSBuild then
///   fails the import), or NuGet serves a directory that does not exist.
/// - [`SdkResolveError::VersionNotSatisfied`] when installed
///   versions exist but the effective spec admits none of them.
///   "Effective spec" is the per-import pin if set, otherwise the
///   caller `spec`. The returned `available` list is the sorted set
///   of versions the spec was consulted against: with per-import
///   set, the union across both roots; without, only the
///   `$DOTNET_ROOT` versions (NuGet is not consulted in the
///   unpinned case).
///
/// The function does not canonicalise the returned paths; they are
/// `dotnet_root.join("sdk").join(...)` or
/// `nuget_packages_dir.join(lowercased_name)...` literally, so the
/// caller can tell which root won by inspecting the path components.
///
/// ```no_run
/// use std::path::PathBuf;
/// use borzoi_msbuild::{locate_dotnet_sdk, parse_fsproj_with_imports};
///
/// let dotnet_root = PathBuf::from("/usr/local/share/dotnet");
/// let nuget = PathBuf::from("/Users/me/.nuget/packages");
/// let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
///     locate_dotnet_sdk(&dotnet_root, Some(&nuget), name, None, None, observer)
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
    observer: &Observer,
) -> Result<SdkPaths, SdkResolveError> {
    // MSBuild allows `Sdk="Name/Version"` (e.g.
    // `Sdk="Microsoft.Build.NoTargets/1.0.80"`). The per-import
    // version names a specific package version directly, which is the
    // canonical way to pin a NuGet-distributed Project SDK. We honour
    // it: when present, it constrains the lookup to that exact
    // version (`RollForward::Disable`) across *both* roots,
    // overriding any caller `spec` for this lookup. The caller spec
    // (from `global.json`) targets the host .NET SDK, not arbitrary
    // Project SDK packages — when the project file is itself
    // expressing a per-import pin, it's the more specific request.
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

    let host_versions = host_sdk_versions(dotnet_root, observer);
    let nuget_candidates = match nuget_packages_dir {
        Some(dir) => collect_from_nuget(dir, name, observer),
        None => Vec::new(),
    };

    // Two specs are at play, applied to different candidate sets:
    //
    // - The caller `spec` (from `global.json`'s `sdk` block)
    //   constrains the host .NET SDK install — `$DOTNET_ROOT` only.
    //   NuGet candidates are third-party Project SDK packages and
    //   aren't governed by `sdk.version`, so applying caller `spec`
    //   to them would wrongly reject e.g.
    //   `Microsoft.Build.NoTargets 3.7.134` just because
    //   `global.json` pins .NET SDK to `8.0.401`.
    //
    // - An **effective pin** for `name`: either the per-import
    //   version (`Sdk="Name/Version"`) or, if absent, the
    //   `msbuild-sdks[name]` entry from `global.json`. Per-import
    //   wins — it's the more specific request, written at the import
    //   site. Either source produces a `Disable(version)` spec that
    //   applies to *both* roots and overrides the caller spec for
    //   this lookup: the project / project-wide map is making an
    //   explicit version request about *this* SDK package, which is
    //   a different question from the host-SDK pin.
    //
    // NuGet is only consulted when an effective pin is present.
    // Without one, upstream's `Microsoft.Build.NuGetSdkResolver`
    // refuses to scan the cache and we mirror that: picking the
    // highest restored copy on its own could import a different SDK
    // than MSBuild itself would. The caller `spec` does not count as
    // a NuGet version source.
    let effective_pin: Option<SdkVersion> =
        per_import_version.or_else(|| msbuild_sdks.and_then(|m| m.get(name).cloned()));
    let pin_spec: Option<VersionSpec> =
        effective_pin.map(|v| VersionSpec::with_version(v, RollForward::Disable, true));
    let dotnet_spec_ref: Option<&VersionSpec> = pin_spec.as_ref().or(spec);
    // NuGet's `File.Exists` of a restore marker takes a relative folder
    // against the process's working directory, which we cannot see.
    if pin_spec.is_some() && nuget_packages_dir.is_some_and(|dir| !dir.has_root()) {
        return Err(SdkResolveError::UnsupportedLayout {
            reason: "the NuGet package folder is a relative path".to_owned(),
        });
    }

    // The host SDK is chosen by version alone, and only then asked for
    // `name`: MSBuild's default resolver serves
    // `$(MSBuildSDKsPath)/{name}/Sdk` of the SDK that runs, and fails
    // without trying another version when that SDK lacks it.
    let dotnet_versions: Vec<SdkVersion> = host_versions.iter().map(|(v, _)| v.clone()).collect();
    let dotnet_selected = select_sdk_version(&dotnet_versions, dotnet_spec_ref);
    let dotnet_chosen: Option<(&SdkVersion, PathBuf)> = match dotnet_selected {
        Some(version) => {
            let idx = dotnet_versions
                .iter()
                .position(|v| v == version)
                .expect("selection returns a candidate from the slice");
            let sdk_root = host_versions[idx].1.join("Sdks").join(name).join("Sdk");
            sdk_directory(sdk_root, observer)?.map(|root| (version, root))
        }
        None => None,
    };

    // NuGet half is gated on having a pin. Without one, we never
    // even look at the restored cache for picking purposes —
    // `nuget_versions` stays empty so neither the cross-root pick
    // nor the `available` diagnostic considers it.
    let nuget_versions: Vec<SdkVersion> = if pin_spec.is_some() {
        nuget_candidates.iter().map(|(v, _)| v.clone()).collect()
    } else {
        Vec::new()
    };
    let nuget_selected = if let Some(s) = pin_spec.as_ref() {
        select_sdk_version(&nuget_versions, Some(s))
    } else {
        None
    };
    let nuget_chosen: Option<(&SdkVersion, PathBuf)> = match nuget_selected {
        Some(version) => {
            let idx = nuget_versions
                .iter()
                .position(|v| v == version)
                .expect("selection returns a candidate from the slice");
            // NuGet's resolver serves this directory whether or not it
            // exists, so its absence fails the import rather than letting
            // another root answer.
            let sdk_root = nuget_candidates[idx].1.clone();
            let Some(root) = sdk_directory(sdk_root.clone(), observer)? else {
                return Err(SdkResolveError::UnsupportedLayout {
                    reason: format!(
                        "NuGet serves the SDK directory {}, which does not exist",
                        sdk_root.display()
                    ),
                });
            };
            Some((version, root))
        }
        None => None,
    };

    // Pick across the two roots. When both produce a candidate,
    // `$DOTNET_ROOT` wins ties or strict-higher; NuGet wins only when
    // its max strictly exceeds the spec-admitted `$DOTNET_ROOT` pick.
    // This preserves "shared store wins ties" while still picking up
    // a NuGet copy when DOTNET has nothing (or nothing the spec
    // admits).
    let sdk_dir = match (dotnet_chosen, nuget_chosen) {
        (Some((d, dotnet_root)), Some((n, nuget_root))) => {
            if d >= n {
                dotnet_root
            } else {
                nuget_root
            }
        }
        (Some((_, root)), None) | (None, Some((_, root))) => root,
        (None, None) => {
            // Both roots produced no candidate. We get here in four
            // sub-cases:
            //   - both roots physically empty                  → NotFound
            //   - the selected host SDK lacks `name`           → NotFound
            //   - DOTNET has versions but spec rejects all     → VersionNotSatisfied
            //   - effective pin set, neither root has the pin  → VersionNotSatisfied
            // The `available` list shows the user which versions *were*
            // on disk — those are the alternatives they could install
            // or pin against. With an effective pin (per-import or
            // `msbuild-sdks`), both roots are alternatives (the spec was
            // consulted against both); without one, only `$DOTNET_ROOT`
            // is filtered, so only those versions are alternatives.
            let dotnet_rejected = !dotnet_versions.is_empty() && dotnet_selected.is_none();
            let nuget_rejected = !nuget_versions.is_empty() && nuget_selected.is_none();
            if !dotnet_rejected && !nuget_rejected {
                return Err(SdkResolveError::NotFound);
            }
            let mut available = dotnet_versions;
            if pin_spec.is_some() {
                for v in nuget_versions {
                    if !available.contains(&v) {
                        available.push(v);
                    }
                }
            }
            available.sort();
            let effective_spec = match pin_spec {
                Some(s) => s,
                None => spec
                    .expect("with no spec or pin, max is always picked when candidates exist")
                    .clone(),
            };
            return Err(SdkResolveError::VersionNotSatisfied {
                spec: effective_spec,
                available,
            });
        }
    };
    Ok(SdkPaths {
        root: sdk_dir.clone(),
        props: sdk_dir.join("Sdk.props"),
        targets: sdk_dir.join("Sdk.targets"),
    })
}

/// The installed SDK versions under `{dotnet_root}/sdk`: every entry whose
/// name parses as a version and that is a directory or a link to one (Nix's
/// wrapped .NET links each `sdk/{version}`). Empty when `sdk/` cannot be
/// listed.
///
/// hostfxr also passes over a version directory without a `dotnet.dll`,
/// which this does not model (#910).
fn host_sdk_versions(dotnet_root: &Path, observer: &Observer) -> Vec<(SdkVersion, PathBuf)> {
    let Ok(entries) = observed::read_dir(observer, &dotnet_root.join("sdk")) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for entry in entries.into_iter().flatten() {
        let Some(version) = entry.name.to_str().and_then(SdkVersion::parse) else {
            continue;
        };
        if observed::is_dir(observer, &entry.path) {
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
        let version_dir = select_host_sdk_version_dir(dotnet_root, spec, observer)?;
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

/// The `{dotnet_root}/sdk/{version}` directory of the host SDK the spec
/// admits (highest installed version when unconstrained) — the SDK
/// whose `KnownWorkloadManifests.txt` drives workload locator
/// resolution: [`host_sdk_versions`], selected by version alone, as
/// [`locate_dotnet_sdk`] selects it. No installed version at all is `NotFound`;
/// installed versions all rejected by the spec is `VersionNotSatisfied`
/// with the sorted available list, matching ordinary SDK resolution's
/// diagnostic split.
fn select_host_sdk_version_dir(
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
