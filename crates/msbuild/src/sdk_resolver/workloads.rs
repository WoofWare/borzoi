//! Resolution of the two MSBuild **workload locator SDKs** —
//! `Microsoft.NET.SDK.WorkloadManifestTargetsLocator` and
//! `Microsoft.NET.SDK.WorkloadAutoImportPropsLocator` — and of **workload
//! packs named as SDKs**, against the canonical dotnet on-disk layout, under
//! the "resolve identically or degrade" policy of
//! `docs/completed/sdk-chain-exactness-plan.md` (D2).
//!
//! In MSBuild these names are claimed by the workload MSBuild SDK
//! resolver, which returns a *list* of directories; `<Import
//! Project="P" Sdk="…Locator"/>` then imports `P` relative to each (an
//! empty list means the import cleanly contributes nothing). The
//! algorithm here transcribes the authoritative dotnet/sdk sources —
//! `SdkDirectoryWorkloadManifestProvider.cs` and
//! `CachingWorkloadResolver.cs` (fetched 2026-07-09) — and was
//! additionally ground-truthed against `dotnet msbuild -preprocess` on
//! the nix dotnet 10.0.300 layout (probe record in
//! docs/completed/sdk-chain-exactness-plan.md):
//!
//! * The **primary pass** enumerates every id directory in the *host
//!   feature band*'s `sdk-manifests/{band}` directory — known-list
//!   membership is not required there. When a `userlocal` marker
//!   (`{dotnet}/metadata/workloads/{band}/userlocal`) is present and
//!   the user-local root has an `sdk-manifests` directory, that root
//!   participates too and *shadows* the dotnet root for same-named id
//!   directories. Pack scanning is gated differently: the user root's
//!   `packs` tree is consulted whenever the marker is present and the
//!   directory exists, with or without manifests
//!   (`WorkloadResolver.Create` vs the manifest provider).
//! * The host band is the host SDK version's `SdkFeatureBand` (`feature_band.rs`): a
//!   prerelease SDK has its own (`11.0.100-rc.1.26425.128` is band
//!   `11.0.100-rc.1`, whose directory is `sdk-manifests/11.0.100-rc.1`).
//! * Ids from `KnownWorkloadManifests.txt` (fallback filename
//!   `IncludedWorkloadManifests.txt`) that the primary pass did not
//!   find go through **band fallback**: the *dotnet* manifests root
//!   only (never the user-local root). Each directory under it is read
//!   as the feature band its name spells, and looked up under *that*
//!   band's name (so `11.0.100-rc.1.5` stands for `11.0.100-rc.1`);
//!   the candidates are the bands below the host band, and the host's
//!   own release band (so a prerelease host falls back to the release
//!   it precedes); highest band wins. An id found nowhere is silently
//!   skipped (`samsung.net.sdk.tizen` on the probed layout).
//! * Inside an id directory, versioned subdirectories containing
//!   `WorkloadManifest.json` take precedence over a flat manifest, and
//!   the **highest version wins** by the provider's own `VersionCompare`
//!   (`manifest_version.rs`); a directory resolving to no manifest is
//!   skipped. A hardcoded outdated-id set (and the
//!   `workloadsets` folder name) is skipped everywhere.
//! * Import order is known-list line order first, then the remaining
//!   ids ordinal-case-insensitively alphabetical — this matches the
//!   observed `-preprocess` import order. The known list is read as
//!   `File.ReadAllLines` reads it (every non-empty line, untrimmed, split
//!   at a lone `\r` too); a manifest takes the order of the line spelled
//!   exactly as its id, while it counts as found against a line spelled in
//!   any case.
//! * The targets locator keeps only manifest directories that contain
//!   `WorkloadManifest.targets`; the auto-import locator returns the
//!   `{pack}/Sdk` folders of installed SDK-kind packs whose
//!   `Sdk/AutoImport.props` exists (`GetInstalledWorkloadPacksOfKind`): the
//!   packs of every resolved manifest in composition order (manifest order,
//!   then each manifest's packs as its document lists them), an alias
//!   resolved to the target its `alias-to` names for the first runtime
//!   identifier of the host SDK's chain that it names, each installed where
//!   `{root}/packs/{id}/{version}` is a directory under the first pack root
//!   (the user-local one, then the dotnet root) that has it, and each folder
//!   once.
//! * Any other SDK name the running SDK does not ship reaches the same
//!   resolver (`TryGetPackInfo`, [`crate::workloads::resolve_workload_pack`]): the pack whose id
//!   it names, ignoring case, resolved as above, is looked up at its kind's
//!   location (`packs/{id}/{version}` for an SDK or framework pack,
//!   `tool-packs/{id}/{version}` for a tool pack, a lower-cased `.nupkg` under
//!   `template-packs` or `library-packs` for the others) under the first pack
//!   root holding it, else the first root, and the resolver serves that
//!   location's `Sdk` folder wherever `Directory.Exists` finds the location.
//!   Where it does not, the pack is missing: the resolver succeeds with no
//!   path and adds a `MissingWorkloadPack` item to the evaluation, which
//!   [`crate::resolve_sdk`] declines rather than model. No pack of the name for
//!   the host (none defined, or an alias naming none of the host's runtime
//!   identifiers) leaves the name to the next resolver.
//!
//! * A workload set, selected by `global.json`, by the install state or by
//!   default from the host band's, overrides the manifests it names, and
//!   so do the install state's own manifests (`workload_sets.rs`). Every set
//!   of the host band and of the 8.0.100 baseline band must load, whether
//!   or not it is selected.
//!
//! What still degrades with [`SdkResolveError::UnsupportedLayout`]
//! rather than resolving: a workload set, install state or `global.json`
//! outside what `workload_sets.rs` certifies (or one that selects a set
//! that is not installed, or names a manifest that is not), an install-state
//! file when the caller cannot say the build process's architecture, a
//! `userlocal` marker when the caller supplied no
//! user-local root (we cannot see what a real build would), a host
//! SDK version or band directory name outside the spellings
//! `SdkFeatureBand` (`feature_band.rs`) certifies, a host SDK version with
//! build metadata, workload environment overrides, manifest version
//! directories beside each other whose names `ManifestVersion` does not
//! certify or cannot tell apart (the reference may throw comparing them, or
//! pick by an order we cannot see), and any directory or
//! known-list file that exists but cannot be enumerated/read (the
//! real provider throws there; an empty answer would be wrongly
//! certified as exact), and any file the resolver reads (a known list,
//! the runtime identifier chain, a flat manifest, or for the auto-import
//! locator any manifest) that CLR `File.Exists` finds but that is no
//! regular file: a read of a dangling link or a socket throws, and one of a
//! FIFO never returns. A targets file that is a special file declines too,
//! since MSBuild's import of it (and the walk's) would read it, and so does a
//! relative root, which the resolver takes against a working directory we
//! cannot see.
//! The auto-import locator and a pack lookup also decline unless the workload
//! resolver certainly loads every resolved manifest (`manifest::load_manifests`:
//! the reader's grammar, the localization catalogs, and the composition's
//! `depends-on` and conflict checks), and where a pack they would look up has
//! a version that is no plain path component; the auto-import locator also
//! declines where an `AutoImport.props` it would return is a special file.
//!
//! Every existence probe asks what CLR `File.Exists` answers
//! (`dotnet_io::file_exists`), which `tools/workload-oracle` grades with a
//! dangling link, a link loop, a directory, a link to one, a socket and a FIFO
//! at each probed path (`workload_locator_diff`).

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::SdkResolveError;
use crate::SdkResolution;
use crate::dotnet_io;
use crate::observed::{self, EntryKind, Failure, Observer};

mod architecture;
mod feature_band;
mod manifest;
mod manifest_version;
mod workload_sets;
use super::global_json::GlobalJsonWorkloads;
use feature_band::FeatureBand;
use manifest_version::ManifestVersion;

pub use architecture::{EXECUTABLE_HEADER_BYTES, ProcessArchitecture};

pub const WORKLOAD_MANIFEST_TARGETS_LOCATOR: &str =
    "Microsoft.NET.SDK.WorkloadManifestTargetsLocator";
pub const WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR: &str =
    "Microsoft.NET.SDK.WorkloadAutoImportPropsLocator";

/// `SdkDirectoryWorkloadManifestProvider._outdatedManifestIds`: id
/// directories MSBuild skips wherever it encounters them.
const OUTDATED_MANIFEST_IDS: &[&str] = &[
    "microsoft.net.workload.android",
    "microsoft.net.workload.blazorwebassembly",
    "microsoft.net.workload.ios",
    "microsoft.net.workload.maccatalyst",
    "microsoft.net.workload.macos",
    "microsoft.net.workload.tvos",
    "microsoft.net.workload.mono.toolchain",
];

/// Whether `sdk_name` is one of the workload locator SDKs (MSBuild SDK
/// name comparisons are case-insensitive).
pub fn is_workload_locator(sdk_name: &str) -> bool {
    sdk_name.eq_ignore_ascii_case(WORKLOAD_MANIFEST_TARGETS_LOCATOR)
        || sdk_name.eq_ignore_ascii_case(WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR)
}

/// Host-supplied workload context. The msbuild crate never reads the
/// process environment itself (dependency rejection): the shell
/// snapshots what the real resolver would consult and passes it in.
pub struct WorkloadEnvironment<'a> {
    /// The user-local dotnet root (`{DOTNET_CLI_HOME ?? HOME}/.dotnet`),
    /// consulted only when the dotnet root carries a `userlocal`
    /// marker. `None` while the marker is present ⇒ degrade (a real
    /// build would consult manifests we cannot see).
    pub user_dotnet_root: Option<&'a Path>,
    /// True when any workload-resolution environment override is set
    /// (`DOTNETSDK_WORKLOAD_MANIFEST_ROOTS`,
    /// `DOTNETSDK_WORKLOAD_MANIFEST_IGNORE_DEFAULT_ROOTS`,
    /// `DOTNETSDK_WORKLOAD_PACK_ROOTS`), or the resolver is switched off
    /// (`MSBuildEnableWorkloadResolver=false`, which makes it answer nothing
    /// and leaves every name to the next resolver): those redirect resolution
    /// in ways we do not model, so their presence degrades.
    pub overrides_present: bool,
    /// What the workload reader reads of the `global.json` governing the
    /// evaluation (`GlobalJson::workloads`): MSBuild passes the discovered
    /// `global.json` path into its workload manifest provider, where an
    /// `sdk.workloadVersion` selects a workload set (or fails the evaluation
    /// when that set is not installed) and `sdk.workloads-update-mode` opts
    /// in or out of the default selection.
    pub global_json: GlobalJsonWorkloads,
    /// The architecture of the process a build resolves the locators in
    /// (`RuntimeInformation.ProcessArchitecture`): the install state lives
    /// under a directory of its name. A host reads it off the `dotnet` muxer
    /// it builds with ([`ProcessArchitecture::of_executable`]). `None` when
    /// the caller cannot say, which declines wherever an install-state file
    /// exists for any architecture.
    pub process_architecture: Option<ProcessArchitecture>,
}

fn unsupported(reason: impl Into<String>) -> SdkResolveError {
    SdkResolveError::UnsupportedLayout {
        reason: reason.into(),
    }
}

/// Enumerate the **subdirectories** of a directory, distinguishing
/// "absent" from "unreadable". Every upstream scan this mirrors uses
/// `Directory.GetDirectories`, which returns only directory entries — so a
/// regular file (`.DS_Store`, a stray manifest-shaped file) is *not* yielded
/// here: otherwise it would be parsed as a feature band (spurious degrade) or
/// treated as an id directory that shadows the real dotnet-root manifest.
///
/// A missing path (or a non-directory) yields an empty listing — the
/// dotnet provider guards its enumerations with `Directory.Exists`,
/// which reports false for those. Any other error (permissions, I/O)
/// degrades: upstream the enumeration would throw and fail the
/// evaluation, so treating the directory as empty could certify a
/// wrong import set as exact. (In the corner cases where CLR
/// `Directory.Exists` itself swallows the error and skips, degrading
/// is merely conservative.) Entry-iteration and per-entry type-probe
/// errors degrade for the same reason. The type probe follows symlinks
/// (`metadata`, not `file_type`), matching `Directory.GetDirectories`,
/// which includes a symlink to a directory and excludes one to a file, and
/// one it cannot follow (dangling, or a loop): to it that is no directory
/// (`workload_locator_diff` grades it).
fn read_dir_or_degrade(
    dir: &Path,
    observer: &Observer,
) -> Result<Vec<observed::DirEntry>, SdkResolveError> {
    use std::io::ErrorKind;
    let enumeration_failed =
        |err: Failure| unsupported(format!("cannot enumerate {}: {err}", dir.display()));
    let entries = match observed::read_dir(observer, dir) {
        Ok(entries) => entries,
        Err(err) if matches!(err.kind(), ErrorKind::NotFound | ErrorKind::NotADirectory) => {
            return Ok(Vec::new());
        }
        Err(err) => return Err(enumeration_failed(err)),
    };
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = entry.map_err(enumeration_failed)?;
        // A target-following `stat` (`observed::kind`), NOT the directory
        // entry's own type, which does not follow a symlink and would report
        // a symlink to a directory as a non-directory. `Directory.GetDirectories` includes a
        // symlinked directory (package-manager and user-local layouts create
        // them), so we must follow the link. A link that cannot be followed is
        // no directory to it, and is skipped; any other failure degrades.
        match observed::kind(observer, &entry.path) {
            Ok(EntryKind::Dir) => dirs.push(entry),
            Ok(_) => {}
            Err(err) => {
                if observed::link_kind(observer, &entry.path) != Ok(EntryKind::Symlink) {
                    return Err(enumeration_failed(err));
                }
            }
        }
    }
    Ok(dirs)
}

/// Resolve one locator SDK. `sdk_version_dir` is the host SDK version
/// directory the entry evaluation resolved against — the locators
/// answer relative to the *running* SDK, so the caller passes the same
/// directory its `Microsoft.NET.Sdk` resolution came from.
pub fn resolve_workload_locator(
    sdk_name: &str,
    dotnet_root: &Path,
    sdk_version_dir: &Path,
    env: &WorkloadEnvironment<'_>,
    observer: &Observer,
) -> Result<SdkResolution, SdkResolveError> {
    debug_assert!(is_workload_locator(sdk_name));
    let resolver = WorkloadResolver::create(dotnet_root, sdk_version_dir, env, observer)?;

    if sdk_name.eq_ignore_ascii_case(WORKLOAD_MANIFEST_TARGETS_LOCATOR) {
        // `CachingWorkloadResolver` keeps only the manifest directories
        // where CLR `File.Exists` finds the targets file (a dangling link
        // included: MSBuild then fails to import it); the rest are silently
        // skipped, not an error. A special file there is declined: MSBuild's
        // import of a FIFO never returns, and neither would the walk's.
        let mut with_targets = Vec::new();
        for resolved in resolver.manifests {
            let dir = resolved.directory;
            let targets = dir.join("WorkloadManifest.targets");
            if !dotnet_io::file_exists(observer, &targets) {
                continue;
            }
            if observed::kind(observer, &targets) == Ok(EntryKind::Other) {
                return Err(unsupported(format!(
                    "a workload's targets file is a special file: {}",
                    targets.display()
                )));
            }
            with_targets.push(dir);
        }
        return Ok(SdkResolution::Roots(with_targets));
    }

    let packs = resolver.load_packs(observer)?;
    auto_import_folders(
        &packs,
        &resolver.runtime_identifiers,
        &resolver.roots,
        observer,
    )
    .map(SdkResolution::Roots)
}

/// What `CachingWorkloadResolver` builds before it answers any request: the
/// manifest provider's resolved manifests (`SdkDirectoryWorkloadManifestProvider`,
/// whose construction selects the workload set) and `WorkloadResolver.Create`'s
/// runtime identifiers and pack roots.
struct WorkloadResolver {
    runtime_identifiers: Vec<String>,
    roots: WorkloadRoots,
    manifests: Vec<ResolvedManifest>,
}

impl WorkloadResolver {
    fn create(
        dotnet_root: &Path,
        sdk_version_dir: &Path,
        env: &WorkloadEnvironment<'_>,
        observer: &Observer,
    ) -> Result<WorkloadResolver, SdkResolveError> {
        if env.overrides_present {
            return Err(unsupported(
                "a workload environment override variable is set",
            ));
        }
        // The resolver's `File.Exists` takes a relative path against the
        // process's working directory, which we cannot see.
        if ![
            Some(dotnet_root),
            Some(sdk_version_dir),
            env.user_dotnet_root,
        ]
        .into_iter()
        .flatten()
        .all(Path::has_root)
        {
            return Err(unsupported("a workload root is a relative path"));
        }
        // `CachingWorkloadResolver` answers nothing (null, so MSBuild asks the
        // next resolver) when this sentinel sits in the SDK directory, where
        // CLR `File.Exists` finds it. No installed SDK ships one, and the
        // resolver reads it from its own directory, which the differential
        // cannot point at a generated layout, so it declines.
        let sentinel = sdk_version_dir.join("DisableWorkloadResolver.sentinel");
        if dotnet_io::file_exists(observer, &sentinel) {
            return Err(unsupported(format!(
                "the workload resolver is disabled by {}",
                sentinel.display()
            )));
        }
        let band = host_feature_band(sdk_version_dir)?;
        let runtime_identifiers = runtime_identifier_chain(sdk_version_dir, observer)?;
        let roots = workload_roots(dotnet_root, &band, env, observer)?;
        let manifests = enumerate_manifest_roots(sdk_version_dir, &band, &roots, env, observer)?;
        Ok(WorkloadResolver {
            runtime_identifiers,
            roots,
            manifests,
        })
    }

    /// The packs of every resolved manifest, in composition order, or the
    /// decline unless the workload resolver certainly loads them all
    /// (`InitializeManifests`, which every pack request runs first). A
    /// manifest that is no regular file (a dangling link, a socket) throws
    /// there, and a FIFO blocks for good; one it cannot read or compose
    /// throws too.
    fn load_packs(&self, observer: &Observer) -> Result<Vec<manifest::Pack>, SdkResolveError> {
        for resolved in &self.manifests {
            let manifest = resolved.directory.join("WorkloadManifest.json");
            if !observed::is_file(observer, &manifest) {
                return Err(unsupported(format!(
                    "the workload resolver would open a manifest that is no regular file: {}",
                    manifest.display()
                )));
            }
        }
        let resolved: Vec<manifest::Resolved<'_>> = self
            .manifests
            .iter()
            .map(|m| manifest::Resolved {
                id: &m.id,
                directory: &m.directory,
            })
            .collect();
        manifest::load_manifests(&resolved, observer)
    }
}

/// What the workload SDK resolver answers for an SDK name that is no locator
/// (`CachingWorkloadResolver.Resolve`'s last branch, which asks
/// `WorkloadResolver.TryGetPackInfo` for a workload pack of that id).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkloadPackResolution {
    /// No pack of the name resolves for the host: no manifest defines one, or
    /// it is an alias whose `alias-to` names none of the host's runtime
    /// identifiers. The resolver returns null and MSBuild asks the next one.
    NotAPack,
    /// The pack's directory exists: the resolver returns its `Sdk` folder,
    /// which an import's `Project` is resolved against.
    Installed(PathBuf),
    /// The pack's directory does not exist: the resolver succeeds with no
    /// path, and adds one `MissingWorkloadPack` item to the evaluation, its
    /// spec the SDK name as the import spells it and its `Version` metadata
    /// this version.
    Missing { version: String },
}

/// Resolve `sdk_name`, which is no locator, as the workload SDK resolver
/// does: the workload pack whose id it names, ignoring case, resolved for the
/// host's runtime identifiers, looked up under the pack roots.
pub fn resolve_workload_pack(
    sdk_name: &str,
    dotnet_root: &Path,
    sdk_version_dir: &Path,
    env: &WorkloadEnvironment<'_>,
    observer: &Observer,
) -> Result<WorkloadPackResolution, SdkResolveError> {
    debug_assert!(!is_workload_locator(sdk_name));
    let resolver = WorkloadResolver::create(dotnet_root, sdk_version_dir, env, observer)?;
    let packs = resolver.load_packs(observer)?;
    // `_packs` is keyed by `WorkloadPackId`, which compares as
    // `OrdinalIgnoreCase`; every pack id `load_manifests` admits is ASCII, so
    // ASCII folding is that comparison whatever the name holds.
    let Some(pack) = packs.iter().find(|p| p.id.eq_ignore_ascii_case(sdk_name)) else {
        return Ok(WorkloadPackResolution::NotAPack);
    };
    let Some(id) = pack.resolved_id(&resolver.runtime_identifiers) else {
        return Ok(WorkloadPackResolution::NotAPack);
    };
    if !is_pack_path_component(&pack.version) {
        return Err(unsupported(format!(
            "a workload pack version that is no plain path component: {} {:?}",
            pack.id, pack.version
        )));
    }
    // `GetPackPath`: the location under the first pack root where the
    // pack's kind finds it installed, else under the first root.
    let mut located = None;
    for root in resolver.roots.pack_roots() {
        let (path, is_file) = pack_location(root, id, &pack.version, pack.kind);
        let installed = if is_file {
            dotnet_io::file_exists(observer, &path)
        } else {
            dotnet_io::directory_exists(observer, &path)
        };
        let first = located.is_none();
        if installed || first {
            located = Some(path);
        }
        if installed {
            break;
        }
    }
    let path = located.expect("the dotnet root is always a pack root");
    // `CachingWorkloadResolver` then asks `Directory.Exists` of that location,
    // whatever the kind: an installed file-kind pack is missing to it.
    if dotnet_io::directory_exists(observer, &path) {
        Ok(WorkloadPackResolution::Installed(path.join("Sdk")))
    } else {
        Ok(WorkloadPackResolution::Missing {
            version: pack.version.clone(),
        })
    }
}

/// Where `GetPackPath` looks for a pack of `kind` resolved to `id` under
/// `root`, and whether it asks `File.Exists` of it (a `.nupkg`) rather than
/// `Directory.Exists`. The file name is the NuGet canonical id
/// (`ToLowerInvariant`, which is ASCII lowering on the ASCII ids and plain
/// versions admitted here) and the lowered version.
fn pack_location(
    root: &Path,
    id: &str,
    version: &str,
    kind: manifest::PackKind,
) -> (PathBuf, bool) {
    use manifest::PackKind;
    let nupkg = || {
        format!(
            "{}.{}.nupkg",
            id.to_ascii_lowercase(),
            version.to_ascii_lowercase()
        )
    };
    match kind {
        PackKind::Sdk | PackKind::Framework => (root.join("packs").join(id).join(version), false),
        PackKind::Tool => (root.join("tool-packs").join(id).join(version), false),
        PackKind::Template => (root.join("template-packs").join(nupkg()), true),
        PackKind::Library => (root.join("library-packs").join(nupkg()), true),
    }
}

/// The auto-import locator's answer: `CachingWorkloadResolver` asks
/// `WorkloadResolver.GetInstalledWorkloadPacksOfKind(Sdk)` for the installed
/// SDK packs, in composition order, and keeps the `Sdk` folder of each where
/// CLR `File.Exists` finds `Sdk/AutoImport.props`, each path once (`Distinct`,
/// since two aliases can name one pack).
///
/// A pack is resolved to its id for the host (`Pack::resolved_id`, against
/// the runtime identifier chain) and is installed where `Directory.Exists`
/// finds `{root}/packs/{id}/{version}` under the first pack root that holds
/// one (`GetPackPath`). A version that is no plain path component declines,
/// since the resolver's `Path.Combine` would make of it a path we do not
/// model, and so does an `AutoImport.props` that is a special file, since
/// MSBuild's import of a FIFO never returns, and neither would the walk's.
fn auto_import_folders(
    packs: &[manifest::Pack],
    runtime_identifiers: &[String],
    roots: &WorkloadRoots,
    observer: &Observer,
) -> Result<Vec<PathBuf>, SdkResolveError> {
    let mut folders: Vec<PathBuf> = Vec::new();
    for pack in packs {
        if pack.kind != manifest::PackKind::Sdk {
            continue;
        }
        let Some(id) = pack.resolved_id(runtime_identifiers) else {
            continue;
        };
        if !is_pack_path_component(&pack.version) {
            return Err(unsupported(format!(
                "a workload pack version that is no plain path component: {} {:?}",
                pack.id, pack.version
            )));
        }
        let Some(pack_dir) = roots
            .pack_roots()
            .map(|root| root.join("packs").join(id).join(&pack.version))
            .find(|dir| dotnet_io::directory_exists(observer, dir))
        else {
            continue;
        };
        let folder = pack_dir.join("Sdk");
        let props = folder.join("AutoImport.props");
        if !dotnet_io::file_exists(observer, &props) {
            continue;
        }
        if observed::kind(observer, &props) == Ok(EntryKind::Other) {
            return Err(unsupported(format!(
                "a workload pack's AutoImport.props is a special file: {}",
                props.display()
            )));
        }
        if !folders
            .iter()
            .any(|seen| seen.as_os_str() == folder.as_os_str())
        {
            folders.push(folder);
        }
    }
    Ok(folders)
}

/// The text of `path`, which CLR `File.Exists` found, or the decline where
/// the resolver's `File.ReadAllLines` of it throws (a dangling link, a socket,
/// a file it cannot open) or never returns (a FIFO). A file that is not UTF-8
/// declines too, though `ReadAllLines` would decode it with replacements.
fn read_existing_text(path: &Path, observer: &Observer) -> Result<String, SdkResolveError> {
    if !observed::is_file(observer, path) {
        return Err(unsupported(format!(
            "the workload resolver would read a file that is no regular file: {}",
            path.display()
        )));
    }
    observed::read_to_string(observer, path)
        .map_err(|err| unsupported(format!("cannot read {}: {err}", path.display())))
}

/// The host's runtime identifiers, most specific first, as
/// `WorkloadResolver.Create` (which both locators run) reads them: the
/// non-empty lines of the host SDK's `NETCoreSdkRuntimeIdentifierChain.txt`,
/// untrimmed, wherever CLR `File.Exists` finds it, and none where it does not.
/// They are the host the SDK was built for, read off disk, not the process's,
/// so nothing about the machine the evaluation runs on enters. A read that
/// throws fails the resolution of either locator.
fn runtime_identifier_chain(
    sdk_version_dir: &Path,
    observer: &Observer,
) -> Result<Vec<String>, SdkResolveError> {
    let path = sdk_version_dir.join("NETCoreSdkRuntimeIdentifierChain.txt");
    if !dotnet_io::file_exists(observer, &path) {
        return Ok(Vec::new());
    }
    let contents = read_existing_text(&path, observer)?;
    // `File.ReadAllLines` consumes a leading UTF-8 byte order mark.
    let contents = contents.strip_prefix('\u{feff}').unwrap_or(&contents);
    Ok(read_all_lines(contents)
        .into_iter()
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect())
}

/// The feature band of the host SDK (`10.0.301` → `10.0.300`,
/// `11.0.100-rc.1.26425.128` → `11.0.100-rc.1`): `SdkFeatureBand` of the
/// version directory's name. A name [`FeatureBand`] does not certify
/// degrades, and so does one with build metadata: `WorkloadResolver.Create`
/// hands the raw version to `WorkloadFileBasedInstall.IsUserLocal`, whose
/// `System.Version` parse of `10.0.100+abc` throws.
fn host_feature_band(sdk_version_dir: &Path) -> Result<FeatureBand, SdkResolveError> {
    let name = sdk_version_dir
        .file_name()
        .and_then(|n| n.to_str())
        .ok_or_else(|| unsupported("host SDK directory has a non-UTF-8 name"))?;
    if name.contains('+') {
        return Err(unsupported(format!(
            "host SDK version with build metadata: {name}"
        )));
    }
    FeatureBand::parse(name).ok_or_else(|| {
        unsupported(format!(
            "host SDK directory is not a version whose feature band we certify: {name}"
        ))
    })
}

/// The feature band [`resolve_workload_locator`] takes a host SDK version
/// to be in, or `None` where it declines. Exposed for the differential.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn feature_band_of(version: &str) -> Option<String> {
    FeatureBand::parse(version).map(|band| band.to_string())
}

/// Whether [`resolve_workload_locator`] takes `version` as a host SDK
/// version at all. Exposed for the differential.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn accepts_host_version(version: &str) -> bool {
    host_feature_band(Path::new(version)).is_ok()
}

/// Whether [`resolve_manifest_directory`] picks among version directories
/// named `names` rather than decline. Exposed for the differential.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn manifest_versions_are_told_apart(names: &[&str]) -> bool {
    let Some(versions) = names
        .iter()
        .map(|name| ManifestVersion::parse(name))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    versions.iter().all(|a| {
        versions
            .iter()
            .any(|b| b.compare(a) == std::cmp::Ordering::Greater)
            || versions
                .iter()
                .filter(|b| b.compare(a) == std::cmp::Ordering::Equal)
                .count()
                == 1
    })
}

/// The order of the feature bands of two versions, or `None` where either
/// band declines. Exposed for the differential.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn compare_feature_bands(a: &str, b: &str) -> Option<std::cmp::Ordering> {
    Some(FeatureBand::parse(a)?.cmp(&FeatureBand::parse(b)?))
}

/// The consultation roots. Manifest enumeration and pack scanning gate
/// the user-local root *differently* upstream, so the two views are
/// kept separate:
///
/// * `SdkDirectoryWorkloadManifestProvider` adds the user root to the
///   manifest roots only when `{user}/sdk-manifests` exists;
/// * `WorkloadResolver.Create` adds it to the pack roots whenever the
///   directory itself exists — a user profile can hold installed packs
///   without holding any manifests.
///
/// In the primary manifest pass the user root shadows the dotnet root;
/// band fallback only ever consults the dotnet root.
struct WorkloadRoots {
    /// The user-local root, present only when the `userlocal` marker
    /// gates it in and the directory exists on disk (and it is not the
    /// dotnet root itself — a user-local dotnet install resolves
    /// against itself once).
    user: Option<UserRoot>,
    dotnet_root: PathBuf,
}

struct UserRoot {
    path: PathBuf,
    /// Whether `{path}/sdk-manifests` exists — the extra gate
    /// `SdkDirectoryWorkloadManifestProvider` puts on manifest-root
    /// participation.
    participates_in_manifests: bool,
}

impl WorkloadRoots {
    /// Primary-pass manifest roots in *precedence* order (highest
    /// first): the user-local root when it participates, then the
    /// dotnet root.
    fn manifest_roots(&self) -> impl Iterator<Item = &Path> {
        self.user
            .as_ref()
            .filter(|user| user.participates_in_manifests)
            .map(|user| user.path.as_path())
            .into_iter()
            .chain(std::iter::once(self.dotnet_root.as_path()))
    }

    /// Roots under whose `packs` directory the auto-import locator looks
    /// for installed packs, precedence order (`WorkloadResolver.Create`'s
    /// root paths).
    fn pack_roots(&self) -> impl Iterator<Item = &Path> {
        self.user
            .as_ref()
            .map(|user| user.path.as_path())
            .into_iter()
            .chain(std::iter::once(self.dotnet_root.as_path()))
    }

    /// Every consulted root, for the conservative degrade sweeps
    /// (install-state pins, MSI markers, workload sets).
    fn all(&self) -> impl Iterator<Item = &Path> {
        self.pack_roots()
    }
}

fn workload_roots(
    dotnet_root: &Path,
    band: &FeatureBand,
    env: &WorkloadEnvironment<'_>,
    observer: &Observer,
) -> Result<WorkloadRoots, SdkResolveError> {
    // `WorkloadFileBasedInstall.IsUserLocal` keys the marker by the release
    // band (it derives `major.minor.hundreds` from any band with a `-`), and
    // `GetWorkloadInstallType` keys the MSI marker by
    // `ToStringWithoutPrerelease`; the install state is keyed by the band
    // itself.
    let release_band = band.without_prerelease().to_string();
    let band_name = band.to_string();
    let marker = dotnet_root
        .join("metadata")
        .join("workloads")
        .join(&release_band)
        .join("userlocal");
    let mut user = None;
    // `WorkloadFileBasedInstall.IsUserLocal` asks CLR `File.Exists`: a
    // `userlocal` directory (or a link to one) is no marker, and a dangling
    // link, a socket or a FIFO is one.
    if dotnet_io::file_exists(observer, &marker) {
        match env.user_dotnet_root {
            Some(user_root) => {
                // Both gates ask `Directory.Exists`.
                if user_root != dotnet_root && dotnet_io::directory_exists(observer, user_root) {
                    user = Some(UserRoot {
                        path: user_root.to_path_buf(),
                        participates_in_manifests: dotnet_io::directory_exists(
                            observer,
                            &user_root.join("sdk-manifests"),
                        ),
                    });
                }
            }
            None => {
                return Err(unsupported(
                    "userlocal workload marker present but no user-local \
                     root was supplied",
                ));
            }
        }
    }
    let roots = WorkloadRoots {
        user,
        dotnet_root: dotnet_root.to_path_buf(),
    };
    for root in roots.all() {
        let workloads_metadata = root.join("metadata").join("workloads");
        // An MSI-based install keeps its install state under
        // ProgramData, outside anything we are handed — degrade on the
        // marker (`GetWorkloadInstallType` in dotnet/sdk).
        let msi_marker = workloads_metadata
            .join(&release_band)
            .join("installertype")
            .join("msi");
        // `GetWorkloadInstallType` tests this marker with CLR `File.Exists`
        // too: a directory named `msi` is not the marker, and a dangling link
        // is.
        if dotnet_io::file_exists(observer, &msi_marker) {
            return Err(unsupported(format!(
                "MSI-based workload install: {}",
                msi_marker.display()
            )));
        }
        // The install state lives under the build process's architecture
        // (`metadata/workloads/{arch}/{band}/InstallState/default.json`,
        // `WorkloadInstallType.GetInstallStateFolder`), and
        // `workload_sets::select` reads it there. A caller that cannot say
        // which architecture that is declines on an install-state file
        // under any, and under the older arch-less location too.
        if env.process_architecture.is_some() {
            continue;
        }
        let mut candidates = vec![
            workloads_metadata
                .join(&band_name)
                .join("InstallState")
                .join("default.json"),
        ];
        for entry in read_dir_or_degrade(&workloads_metadata, observer)? {
            candidates.push(
                entry
                    .path
                    .join(&band_name)
                    .join("InstallState")
                    .join("default.json"),
            );
        }
        // `InstallStateContents.FromPath` reads the file wherever CLR
        // `File.Exists` finds one, and a read of a dangling link throws.
        for install_state in candidates {
            if dotnet_io::file_exists(observer, &install_state) {
                return Err(unsupported(format!(
                    "workload install-state pin present: {}",
                    install_state.display()
                )));
            }
        }
    }
    Ok(roots)
}

/// One resolved manifest directory plus the id MSBuild orders it by.
struct ResolvedManifest {
    id: String,
    directory: PathBuf,
}

/// Enumerate the workload manifest directories exactly as
/// `SdkDirectoryWorkloadManifestProvider.GetManifests` does: the
/// primary pass over the host band directory of every root (user root
/// shadowing dotnet), band fallback against the dotnet root for known
/// ids the primary pass missed, then known-list order followed by
/// alphabetical.
fn enumerate_manifest_roots(
    sdk_version_dir: &Path,
    band: &FeatureBand,
    roots: &WorkloadRoots,
    env: &WorkloadEnvironment<'_>,
    observer: &Observer,
) -> Result<Vec<ResolvedManifest>, SdkResolveError> {
    let band_name = band.to_string();
    // Known-id list: `KnownWorkloadManifests.txt`, falling back to the
    // older `IncludedWorkloadManifests.txt`, each tried where CLR
    // `File.Exists` finds it; a missing file just means no fallback pass and
    // no preferential ordering. A file that exists but cannot be read
    // degrades — upstream `File.ReadAllLines` would throw and fail the
    // evaluation, and treating the list as absent would silently change
    // ordering and fallback.
    let mut known_ids: Option<Vec<String>> = None;
    for name in [
        "KnownWorkloadManifests.txt",
        "IncludedWorkloadManifests.txt",
    ] {
        let path = sdk_version_dir.join(name);
        if !dotnet_io::file_exists(observer, &path) {
            continue;
        }
        let contents = read_existing_text(&path, observer)?;
        // Upstream reads this with `File.ReadAllLines`, whose BOM-detecting
        // `StreamReader` consumes a leading UTF-8 BOM, and keeps every
        // non-empty line as it is, untrimmed.
        let contents = contents.strip_prefix('\u{feff}').unwrap_or(&contents);
        let ids = read_all_lines(contents)
            .into_iter()
            .filter(|line| !line.is_empty())
            .map(str::to_owned)
            .collect::<Vec<_>>();
        // The known ids are keyed case-sensitively for their order but
        // matched against the manifests case-insensitively, so two spellings
        // of one id would make the outcome hang on dictionary order; and only
        // on ASCII is `OrdinalIgnoreCase` ASCII case folding.
        for (i, id) in ids.iter().enumerate() {
            if !id.is_ascii()
                || ids[..i]
                    .iter()
                    .any(|seen| seen != id && seen.eq_ignore_ascii_case(id))
            {
                return Err(unsupported(format!(
                    "a known manifest id we cannot fold, or spelled two ways: {id:?}"
                )));
            }
        }
        known_ids = Some(ids);
        break;
    }

    let selection = workload_sets::select(
        band,
        roots,
        &env.global_json,
        env.process_architecture,
        observer,
    )?;
    // `GetManifests` first checks that every manifest the selected set
    // names is installed (`HasMissingManifests`), and throws if not.
    if let Some(set) = &selection.set {
        for entry in set {
            if entry.directory(roots, observer).is_none() {
                return Err(unsupported(format!(
                    "the selected workload set names a manifest that is not installed: \
                     {} {}/{}",
                    entry.id, entry.version, entry.band
                )));
            }
        }
    }

    // Primary pass: every id directory in `{root}/sdk-manifests/{band}`,
    // shadowed **by directory name** — the highest-precedence root wins by name,
    // exactly as `SdkDirectoryWorkloadManifestProvider.GetManifests` overwrites
    // its `directoriesWithManifests` dictionary (roots processed via `.Reverse()`
    // so the user-local root, added last, wins) and only *then* probes each
    // winning directory. Crucially the shadow is by name, *before* validating
    // contents: a winner that holds no resolvable manifest is dropped and is
    // *not* backfilled from a lower-precedence root's same-band copy (MSBuild's
    // `ProbeDirectory` simply skips it). It instead becomes eligible for the
    // dotnet-root band fallback below — which searches only bands *below* the
    // host band, never the shadowed same-band dotnet copy.
    let mut winners: HashMap<String, (String, PathBuf)> = HashMap::new();
    for root in roots.manifest_roots() {
        let band_dir = root.join("sdk-manifests").join(&band_name);
        for entry in read_dir_or_degrade(&band_dir, observer)? {
            let Some(id) = entry.name.to_str().map(str::to_owned) else {
                continue;
            };
            // First insertion wins: `manifest_roots()` yields highest precedence
            // first, so a later (lower-precedence) root never displaces a name a
            // higher root already claimed — resolvable or not. Two spellings
            // of one name in one band directory are both listed upstream, in
            // the file system's order, and the last overwrites the first; that
            // order is not ours to see. An id only ASCII folding certainly
            // matches as `OrdinalIgnoreCase` does.
            if !id.is_ascii() {
                return Err(unsupported(format!(
                    "a manifest id directory with a non-ASCII name: {}",
                    entry.path.display()
                )));
            }
            match winners.get(&id.to_ascii_lowercase()) {
                Some((seen, seen_path))
                    if seen != &id && seen_path.parent() == entry.path.parent() =>
                {
                    return Err(unsupported(format!(
                        "manifest id directories spelled two ways in {}",
                        band_dir.display()
                    )));
                }
                Some(_) => {}
                None => {
                    winners.insert(id.to_ascii_lowercase(), (id, entry.path));
                }
            }
        }
    }
    let mut found: HashMap<String, ResolvedManifest> = HashMap::new();
    // Probed in key order: a probe that degrades stops the loop, and what
    // the probes before it observed lands in the evaluation's read set, which
    // must not depend on a `HashMap`'s order.
    let mut winners: Vec<_> = winners.into_iter().collect();
    winners.sort_by(|a, b| a.0.cmp(&b.0));
    for (key, (id, dir)) in winners {
        if is_skipped_manifest_id(&id) {
            continue;
        }
        if let Some(directory) = resolve_manifest_directory(&dir, observer)? {
            found.insert(key, ResolvedManifest { id, directory });
        }
    }

    // The selected set's manifests, then the install state's, override what
    // the scan found (`AddManifest` into a dictionary that keeps the first
    // spelling of an id and replaces its directory). An install-state
    // manifest that is not installed throws.
    for (entries, from) in [
        (selection.set.as_deref(), "workload set"),
        (selection.install_state.as_deref(), "install state"),
    ] {
        for entry in entries.unwrap_or_default() {
            let Some(directory) = entry.directory(roots, observer) else {
                return Err(unsupported(format!(
                    "the workload {from} names a manifest that is not installed: {} {}/{}",
                    entry.id, entry.version, entry.band
                )));
            };
            found
                .entry(entry.id.clone())
                .and_modify(|resolved| resolved.directory = directory.clone())
                .or_insert_with(|| ResolvedManifest {
                    id: entry.id.clone(),
                    directory,
                });
        }
    }

    // Band fallback for known ids the primary pass missed
    // (`FallbackForMissingManifest`): dotnet root only. Every directory
    // there is read as the feature band its name spells, and the band is
    // looked up under its own name, not the directory's. The candidates are
    // the bands below the host band and the host's release band (for a
    // release host, the host band itself, whose id directory the primary
    // pass already found unresolvable); the highest band whose id directory
    // resolves to a manifest wins.
    //
    // MSBuild calls `FallbackForMissingManifest` only for ids that are actually
    // missing, and it is *that* call which enumerates the band directories (and
    // can throw on a stray non-version name). So the enumeration — and its
    // degrade — must be gated on there being a missing id: a fully-resolved set
    // never triggers it, even if a stray directory happens to sit alongside.
    // A known id the resolver skips (an outdated one) is never found, so it is
    // always missing: it enumerates the bands as any other does, and resolves
    // in none of them.
    let any_missing = known_ids
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .any(|id| !found.contains_key(&id.to_ascii_lowercase()));
    if let Some(known) = &known_ids
        && any_missing
    {
        let manifests_dir = roots.dotnet_root.join("sdk-manifests");
        let release_band = band.without_prerelease();
        let mut fallback_bands: Vec<(FeatureBand, PathBuf)> = Vec::new();
        for entry in read_dir_or_degrade(&manifests_dir, observer)? {
            let Some(name) = entry.name.to_str().map(str::to_owned) else {
                continue;
            };
            let Some(candidate) = FeatureBand::parse(&name) else {
                // `FallbackForMissingManifest` constructs `new SdkFeatureBand`
                // for *every* directory under `sdk-manifests` — with no
                // try/catch — so a name that isn't a valid feature band throws a
                // `FormatException` and fails the real resolution. Silently
                // skipping it here would return a *supposedly exact* locator
                // result for a layout MSBuild rejects; a name the resolver
                // parses and `FeatureBand` does not certify degrades too.
                return Err(unsupported(format!(
                    "directory under sdk-manifests whose feature band we do not \
                     certify: {name}"
                )));
            };
            if candidate < *band || candidate == release_band {
                let path = manifests_dir.join(candidate.to_string());
                fallback_bands.push((candidate, path));
            }
        }
        fallback_bands.sort_by(|a, b| b.0.cmp(&a.0));
        for id in known {
            let key = id.to_ascii_lowercase();
            if found.contains_key(&key) || is_skipped_manifest_id(id) {
                continue;
            }
            if !is_safe_manifest_id(id) {
                return Err(unsupported(format!(
                    "manifest id with unsafe path characters: {id}"
                )));
            }
            for (_, band_dir) in &fallback_bands {
                let id_dir = band_dir.join(id);
                if !observed::is_dir(observer, &id_dir) {
                    continue;
                }
                // `FallbackForMissingManifest` resolves the id directory of
                // every candidate band (a list it builds whole) and filters
                // out the unresolvable ones *before* picking the highest
                // band: a band whose id directory holds no manifest is passed
                // over in favour of an older band that resolves, and one
                // whose resolution throws fails the resolution even below
                // the band that wins.
                let resolved = resolve_manifest_directory(&id_dir, observer)?;
                if let Some(directory) = resolved
                    && !found.contains_key(&key)
                {
                    found.insert(
                        key.clone(),
                        ResolvedManifest {
                            id: id.clone(),
                            directory,
                        },
                    );
                }
            }
        }
    }

    // Stable order: known-list line order first, then the rest
    // alphabetically. The known order is a case-sensitive dictionary from
    // each line to its index among the kept lines, a repeated line keeping
    // its last; a manifest is looked up in it by the id it is named by. The
    // rest compare as `OrdinalIgnoreCase` does, which folds to upper case, so
    // `_` sorts after every letter.
    let known_order: HashMap<&str, usize> = known_ids
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
        .map(|(index, id)| (id.as_str(), index))
        .collect();
    let mut manifests: Vec<ResolvedManifest> = found.into_values().collect();
    manifests.sort_by(|a, b| {
        let ka = known_order.get(a.id.as_str());
        let kb = known_order.get(b.id.as_str());
        match (ka, kb) {
            (Some(x), Some(y)) => x.cmp(y),
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (None, None) => a.id.to_ascii_uppercase().cmp(&b.id.to_ascii_uppercase()),
        }
    });
    Ok(manifests)
}

/// `major.minor.patch[-prerelease]` in strict SemVer 2.0 spelling, without
/// build metadata — a subset of what both `ReleaseVersion` (behind
/// `SdkFeatureBand`) and `FXVersion` (behind `ManifestVersion`) parse.
/// Numeric components are capped at nine digits so none can overflow.
fn is_plain_release_version(s: &str) -> bool {
    let (core, prerelease) = match s.split_once('-') {
        Some((core, prerelease)) => (core, Some(prerelease)),
        None => (s, None),
    };
    let components: Vec<&str> = core.split('.').collect();
    components.len() == 3
        && components.iter().all(|c| is_plain_numeric(c))
        && prerelease.is_none_or(is_plain_prerelease)
}

/// A workload set version: [`is_plain_release_version`], or the same with a
/// fourth numeric core component (the workload patch version), which
/// `WorkloadSet.WorkloadSetVersionToWorkloadSetPackageVersion` drops before
/// building the feature band from the first three.
fn is_plain_workload_set_version(s: &str) -> bool {
    let (core, prerelease) = match s.split_once('-') {
        Some((core, prerelease)) => (core, Some(prerelease)),
        None => (s, None),
    };
    let components: Vec<&str> = core.split('.').collect();
    (components.len() == 3 || components.len() == 4)
        && components.iter().all(|c| is_plain_numeric(c))
        && prerelease.is_none_or(is_plain_prerelease)
}

fn is_plain_numeric(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 9
        && s.bytes().all(|b| b.is_ascii_digit())
        && (s == "0" || !s.starts_with('0'))
}

fn is_plain_prerelease(s: &str) -> bool {
    s.split('.').all(|ident| {
        !ident.is_empty()
            && ident
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-')
            && (!ident.bytes().all(|b| b.is_ascii_digit()) || is_plain_numeric(ident))
    })
}

/// `SdkDirectoryWorkloadManifestProvider.ResolveManifestDirectory`:
/// versioned subdirectories containing `WorkloadManifest.json` beat a
/// flat manifest, the highest by `VersionCompare` (`manifest_version.rs`)
/// winning; nothing resolvable means the directory is skipped (`Ok(None)`),
/// not an error.
///
/// The provider folds the candidates in enumeration order, so it compares
/// no name when there is one candidate, which then wins whatever it is
/// called; when there are more, every one must be a name
/// [`ManifestVersion::parse`] certifies, since a comparison the reference
/// cannot make throws, and which comparisons it makes hangs on an order
/// we cannot see. For the same reason two distinct names it cannot tell
/// apart, at the top, decline: the later one listed wins.
fn resolve_manifest_directory(
    id_dir: &Path,
    observer: &Observer,
) -> Result<Option<PathBuf>, SdkResolveError> {
    let mut candidates: Vec<(String, PathBuf)> = Vec::new();
    for entry in read_dir_or_degrade(id_dir, observer)? {
        let candidate = entry.path;
        // CLR `File.Exists`, as `ResolveManifestDirectory` asks it: a
        // dangling link makes its directory a manifest directory too.
        if !dotnet_io::file_exists(observer, &candidate.join("WorkloadManifest.json")) {
            continue;
        }
        let Some(name) = entry.name.to_str().map(str::to_owned) else {
            return Err(unsupported(format!(
                "a workload manifest version directory with a non-UTF-8 name: {}",
                candidate.display()
            )));
        };
        candidates.push((name, candidate));
    }
    if let [(_, only)] = candidates.as_slice() {
        return Ok(Some(only.clone()));
    }
    if !candidates.is_empty() {
        let mut versions = Vec::new();
        for (name, path) in &candidates {
            let Some(version) = ManifestVersion::parse(name) else {
                return Err(unsupported(format!(
                    "a workload manifest version directory whose comparison we do not \
                     certify, beside others: {}",
                    path.display()
                )));
            };
            versions.push((version, path));
        }
        let (best, path) = versions
            .iter()
            .reduce(|best, next| {
                if next.0.compare(&best.0) == std::cmp::Ordering::Greater {
                    next
                } else {
                    best
                }
            })
            .expect("candidates are not empty");
        if versions.iter().any(|(version, other)| {
            other != path && version.compare(best) == std::cmp::Ordering::Equal
        }) {
            return Err(unsupported(format!(
                "workload manifest version directories the resolver cannot tell apart: {}",
                id_dir.display()
            )));
        }
        return Ok(Some((*path).clone()));
    }
    let flat = id_dir.join("WorkloadManifest.json");
    if dotnet_io::file_exists(observer, &flat) {
        // `ResolveManifestDirectory` then opens a flat manifest for its
        // version, and keeps the directory whatever the open throws. An open
        // of a FIFO never returns, so a special file is declined rather than
        // told apart.
        if observed::kind(observer, &flat) == Ok(EntryKind::Other) {
            return Err(unsupported(format!(
                "a flat workload manifest is a special file: {}",
                flat.display()
            )));
        }
        return Ok(Some(id_dir.to_path_buf()));
    }
    Ok(None)
}

/// `File.ReadAllLines`' lines: split at `\r\n`, `\r` or `\n`, with no empty
/// line after a final separator.
fn read_all_lines(text: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let mut rest = text;
    while !rest.is_empty() {
        match rest.find(['\r', '\n']) {
            Some(at) => {
                lines.push(&rest[..at]);
                let skip = if rest[at..].starts_with("\r\n") { 2 } else { 1 };
                rest = &rest[at + skip..];
            }
            None => {
                lines.push(rest);
                rest = "";
            }
        }
    }
    lines
}

/// Ids MSBuild skips wherever encountered: the hardcoded outdated set
/// and the `workloadsets` folder name.
fn is_skipped_manifest_id(id: &str) -> bool {
    id.eq_ignore_ascii_case("workloadsets")
        || OUTDATED_MANIFEST_IDS
            .iter()
            .any(|outdated| id.eq_ignore_ascii_case(outdated))
}

/// Manifest ids come from a file we read off disk and are spliced into
/// paths; hold them to the same containment rules as SDK names.
fn is_safe_manifest_id(id: &str) -> bool {
    !id.is_empty()
        && id
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-' || b == b'_')
}

/// A pack version `Path.Combine` joins into a pack path as one plain
/// component: not empty (which it would skip), not `.` or `..` (which
/// `Directory.Exists` would collapse), and no separator.
fn is_pack_path_component(s: &str) -> bool {
    !s.is_empty()
        && s != "."
        && s != ".."
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'-' | b'_' | b'+'))
}

#[cfg(test)]
mod tests;
