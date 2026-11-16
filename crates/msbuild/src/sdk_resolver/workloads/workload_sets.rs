//! Which workload set, and which install-state manifests, the workload
//! manifest provider applies over the manifests it finds by scanning: its
//! `RefreshWorkloadManifests` (`SdkDirectoryWorkloadManifestProvider.cs`,
//! dotnet/sdk), held to the installed resolvers by `workload_locator_diff`.
//!
//! The provider loads every workload set of the host feature band, and of
//! the `8.0.100` band where the SDK installers drop their baseline sets,
//! whether or not it uses them (a set that fails to load fails the
//! resolution). It then selects one in the first of three ways that
//! applies:
//!
//! 1. `global.json`'s `sdk.workloadVersion`;
//! 2. the install state's `workloadVersion`
//!    (`metadata/workloads/{architecture}/{band}/InstallState/default.json`
//!    under the user-local root when it holds manifests, else the dotnet
//!    root);
//! 3. the highest set of the host band by `VersionCompare`, unless
//!    `global.json`'s `workloads-update-mode` or the install state's
//!    `useWorkloadSets` opts out.
//!
//! A version named by the first two is looked up among the host band's
//! sets, then among the sets of the band the version spells, then among the
//! baseline sets; one found nowhere fails the resolution. The install
//! state's own `manifests` apply too, unless the set came from `global.json`
//! or the default selection.
//!
//! What is certified is a strict subset of what loads: set and manifest
//! versions in plain spellings, ids that are plain path components, JSON
//! the strict reader takes. Anything else declines, whether or not the
//! reference would in fact throw on it.

use std::path::{Path, PathBuf};

use super::super::global_json::{JsonValue, parse_json_string_map, parse_strict_json};
use super::{
    FeatureBand, GlobalJsonWorkloads, ManifestVersion, WorkloadRoots, is_plain_release_version,
    is_plain_workload_set_version, is_safe_manifest_id, read_dir_or_degrade, unsupported,
};
use crate::SdkResolveError;
use crate::dotnet_io;
use crate::observed::{self, Observer};

/// The feature band whose workload sets the provider always loads alongside
/// the host band's: the SDK installers drop their *baseline* workload set
/// under it ("the baseline workload sets were merged with a fixed 8.0.100
/// feature band").
const BASELINE_WORKLOAD_SET_BAND: &str = "8.0.100";

/// One manifest a workload set, or the install state, names.
#[derive(Clone, Debug)]
pub(super) struct SetEntry {
    /// The id, lowercased as `ManifestId` lowercases it.
    pub(super) id: String,
    pub(super) version: String,
    pub(super) band: FeatureBand,
}

impl SetEntry {
    /// `GetManifestDirectoryFromSpecifier`: the first manifest root holding
    /// `{band}/{id}/{version}/WorkloadManifest.json` (CLR `File.Exists`).
    pub(super) fn directory(&self, roots: &WorkloadRoots, observer: &Observer) -> Option<PathBuf> {
        roots.manifest_roots().find_map(|root| {
            let dir = root
                .join("sdk-manifests")
                .join(self.band.to_string())
                .join(&self.id)
                .join(&self.version);
            dotnet_io::file_exists(observer, &dir.join("WorkloadManifest.json")).then_some(dir)
        })
    }
}

/// What the provider applies over its scan, in order.
pub(super) struct Selection {
    /// The selected workload set's manifests.
    pub(super) set: Option<Vec<SetEntry>>,
    /// The install state's manifests, when they apply.
    pub(super) install_state: Option<Vec<SetEntry>>,
}

/// The workload sets of one band: each version with its manifests, in the
/// order the provider's dictionary holds them.
type Sets = Vec<(String, Vec<SetEntry>)>;

/// `RefreshWorkloadManifests`, or the decline where the reference may throw
/// or select by what we do not model. `architecture` is the build process's
/// (`RuntimeInformation.ProcessArchitecture`); `None` reads no install
/// state, which the caller has made sure there is none of.
pub(super) fn select(
    band: &FeatureBand,
    roots: &WorkloadRoots,
    global_json: &GlobalJsonWorkloads,
    architecture: Option<&str>,
    observer: &Observer,
) -> Result<Selection, SdkResolveError> {
    let host_sets = load_sets(band, roots, observer)?;
    let baseline_band =
        FeatureBand::parse(BASELINE_WORKLOAD_SET_BAND).expect("the baseline band parses");
    let baseline_sets = load_sets(&baseline_band, roots, observer)?;
    let find = |version: &str| -> Result<Vec<SetEntry>, SdkResolveError> {
        find_set(version, band, &host_sets, &baseline_sets, roots, observer)
    };

    let (global_json_version, global_json_use_sets) = match global_json {
        GlobalJsonWorkloads::Silent => (None, None),
        GlobalJsonWorkloads::Reads {
            workload_version,
            use_workload_sets,
        } => (workload_version.as_deref(), *use_workload_sets),
        GlobalJsonWorkloads::Unmodelled => {
            return Err(unsupported(
                "global.json says something to the workload reader we do not model",
            ));
        }
    };
    let mut set = None;
    let mut use_install_state = true;
    if let Some(version) = global_json_version {
        use_install_state = false;
        set = Some(find(version)?);
    }

    let install_state = match architecture {
        Some(architecture) => read_install_state(band, roots, architecture, observer)?,
        None => InstallState::default(),
    };
    let mut install_state_manifests = None;
    if set.is_none() {
        if let Some(version) = install_state.workload_version.as_deref()
            && !version.is_empty()
        {
            set = Some(find(version)?);
        }
        if let Some(manifests) = &install_state.manifests {
            install_state_manifests = Some(entries(manifests, band).ok_or_else(|| {
                unsupported("the workload install state names manifests we do not certify")
            })?);
        }
    }
    if set.is_none()
        && global_json_use_sets
            .or(install_state.use_workload_sets)
            .unwrap_or(true)
        && !host_sets.is_empty()
    {
        set = Some(highest(&host_sets)?.clone());
        use_install_state = false;
    }
    Ok(Selection {
        set,
        install_state: install_state_manifests.filter(|_| use_install_state),
    })
}

/// `TryGetWorkloadSet`: the set of `version` among the host band's sets, the
/// sets of the band the version spells, or the baseline sets; a decline when
/// it is in none, where the reference throws.
fn find_set(
    version: &str,
    band: &FeatureBand,
    host_sets: &Sets,
    baseline_sets: &Sets,
    roots: &WorkloadRoots,
    observer: &Observer,
) -> Result<Vec<SetEntry>, SdkResolveError> {
    let lookup = |sets: &Sets| {
        sets.iter()
            .find(|(v, _)| v == version)
            .map(|(_, entries)| entries.clone())
    };
    let Some(version_band) = set_version_band(version) else {
        return Err(unsupported(format!(
            "a workload set version we do not certify: {version:?}"
        )));
    };
    if let Some(found) = lookup(host_sets) {
        return Ok(found);
    }
    if version_band != *band
        && let Some(found) = lookup(&load_sets(&version_band, roots, observer)?)
    {
        return Ok(found);
    }
    lookup(baseline_sets).ok_or_else(|| {
        unsupported(format!(
            "the workload set {version} is not installed, so the resolution fails"
        ))
    })
}

/// The highest set by `VersionCompare`, folded as the provider folds the
/// versions (`VersionCompare(s1, s2) >= 0 ? s1 : s2`); a decline when two at
/// the top tie, where the first in an order we cannot see wins.
fn highest(sets: &Sets) -> Result<&Vec<SetEntry>, SdkResolveError> {
    let versions: Vec<(ManifestVersion<'_>, &Vec<SetEntry>)> = sets
        .iter()
        .map(|(version, entries)| {
            ManifestVersion::parse(version)
                .map(|parsed| (parsed, entries))
                .ok_or_else(|| {
                    unsupported(format!(
                        "a workload set version whose comparison we do not certify: {version}"
                    ))
                })
        })
        .collect::<Result<_, _>>()?;
    let (top, entries) = versions
        .iter()
        .reduce(|best, next| {
            if next.0.compare(&best.0) == std::cmp::Ordering::Greater {
                next
            } else {
                best
            }
        })
        .expect("the sets are not empty");
    if versions
        .iter()
        .filter(|(version, _)| version.compare(top) == std::cmp::Ordering::Equal)
        .count()
        > 1
    {
        return Err(unsupported(
            "workload sets of the host band the resolver cannot tell apart",
        ));
    }
    Ok(entries)
}

/// `WorkloadSet.GetWorkloadSetFeatureBand` of a set version: the band of its
/// first three components, with its prerelease when it has only three;
/// `None` for a version outside the plain spellings.
fn set_version_band(version: &str) -> Option<FeatureBand> {
    if !is_plain_workload_set_version(version) {
        return None;
    }
    let core = version.split_once('-').map_or(version, |(core, _)| core);
    let components: Vec<&str> = core.split('.').collect();
    if components.len() == 3 {
        FeatureBand::parse(version)
    } else {
        FeatureBand::parse(&components[..3].join("."))
    }
}

/// `GetAvailableWorkloadSets(band)`: every loadable set under
/// `{root}/sdk-manifests/{band}/workloadsets` of each manifest root, the
/// dotnet root's first and the user-local root's over them by version.
///
/// A set directory holding no `*.workloadset.json` loads as no set, and one
/// whose version spells another band is passed over; any file the glob
/// could take on some host (its name ends `.workloadset.json` in any
/// casing) must be one it takes on every host, a regular file, and a JSON
/// object of plain entries, no id repeated in any casing within the set.
fn load_sets(
    band: &FeatureBand,
    roots: &WorkloadRoots,
    observer: &Observer,
) -> Result<Sets, SdkResolveError> {
    let manifest_roots: Vec<&Path> = roots.manifest_roots().collect();
    let mut sets: Sets = Vec::new();
    for root in manifest_roots.into_iter().rev() {
        let sets_root = root
            .join("sdk-manifests")
            .join(band.to_string())
            .join("workloadsets");
        if !observed::is_dir(observer, &sets_root) {
            continue;
        }
        for set_dir in read_dir_or_degrade(&sets_root, observer)? {
            let (Some(entries), case_variant) = load_set(&set_dir.path, band, observer)? else {
                continue;
            };
            let Some(version) = set_dir.name.to_str().map(str::to_owned) else {
                return Err(unsupported(format!(
                    "a workload set with a non-UTF-8 version: {}",
                    set_dir.path.display()
                )));
            };
            let Some(version_band) = set_version_band(&version) else {
                return Err(unsupported(format!(
                    "a workload set version we do not certify: {}",
                    set_dir.path.display()
                )));
            };
            if version_band != *band {
                continue;
            }
            if case_variant {
                return Err(unsupported(format!(
                    "a workload set holding a file only a case-insensitive glob takes: {}",
                    set_dir.path.display()
                )));
            }
            match sets.iter_mut().find(|(v, _)| *v == version) {
                Some(existing) => existing.1 = entries,
                None => sets.push((version, entries)),
            }
        }
    }
    Ok(sets)
}

/// `WorkloadSet.FromWorkloadSetFolder`: the manifests of the set in
/// `set_dir`, `None` for a directory holding no set file, and whether a
/// file only a case-insensitive glob takes (macOS's, Windows's, not
/// Linux's) is among them: one that must load either way, but whose
/// contents count on some hosts only.
fn load_set(
    set_dir: &Path,
    band: &FeatureBand,
    observer: &Observer,
) -> Result<(Option<Vec<SetEntry>>, bool), SdkResolveError> {
    let malformed = |path: &Path, why: &str| {
        Err(unsupported(format!(
            "workload set may fail to load ({why}): {}",
            path.display()
        )))
    };
    let listing = observed::read_dir(observer, set_dir)
        .map_err(|err| unsupported(format!("cannot enumerate {}: {err}", set_dir.display())))?;
    let mut entries: Option<Vec<SetEntry>> = None;
    let mut case_variant = false;
    for entry in listing {
        let entry = entry
            .map_err(|err| unsupported(format!("cannot enumerate {}: {err}", set_dir.display())))?;
        let path = entry.path;
        let Some(name) = entry.name.to_str() else {
            return malformed(&path, "non-UTF-8 file name");
        };
        if !name.to_ascii_lowercase().ends_with(".workloadset.json") {
            continue;
        }
        case_variant |= !name.ends_with(".workloadset.json");
        if !observed::is_file(observer, &path) {
            return malformed(&path, "not a regular file");
        }
        let Ok(text) = observed::read_to_string(observer, &path) else {
            return malformed(&path, "unreadable or not UTF-8");
        };
        let Some(map) = parse_json_string_map(&text) else {
            return malformed(&path, "not a JSON object of strings");
        };
        let Some(file_entries) = entries_of(&map, band) else {
            return malformed(&path, "manifest entries not certified to parse");
        };
        let all = entries.get_or_insert_with(Vec::new);
        for file_entry in file_entries {
            if all.iter().any(|seen| seen.id == file_entry.id) {
                return malformed(&path, "manifest id repeated");
            }
            all.push(file_entry);
        }
    }
    Ok((entries, case_variant))
}

/// `WorkloadSet.FromDictionaryForJson` of `map`, a band defaulting to
/// `default_band`; `None` where we do not certify it parses: an id that is
/// not a plain path component (or repeats in any casing), a version or band
/// outside the plain spellings.
fn entries_of(map: &[(String, String)], default_band: &FeatureBand) -> Option<Vec<SetEntry>> {
    let mut out: Vec<SetEntry> = Vec::new();
    for (id, value) in map {
        if !is_safe_manifest_id(id) {
            return None;
        }
        let id = id.to_ascii_lowercase();
        if out.iter().any(|seen| seen.id == id) {
            return None;
        }
        let mut parts = value.split('/');
        let version = parts.next().unwrap_or_default();
        let band = match parts.next() {
            None => default_band.clone(),
            Some(band) if is_plain_release_version(band) => FeatureBand::parse(band)?,
            Some(_) => return None,
        };
        if parts.next().is_some() || !is_plain_release_version(version) {
            return None;
        }
        out.push(SetEntry {
            id,
            version: version.to_owned(),
            band,
        });
    }
    Some(out)
}

/// [`entries_of`] for the install state's `manifests`.
fn entries(manifests: &[(String, String)], band: &FeatureBand) -> Option<Vec<SetEntry>> {
    entries_of(manifests, band)
}

/// What the provider reads of the install state (`InstallStateContents`).
#[derive(Default)]
struct InstallState {
    use_workload_sets: Option<bool>,
    manifests: Option<Vec<(String, String)>>,
    workload_version: Option<String>,
}

/// `InstallStateContents.FromPath` of the install state for `band` and
/// `architecture`: the default contents where CLR `File.Exists` finds no
/// file, else the file deserialised as `System.Text.Json` deserialises it
/// (case-sensitive camel-case properties, trailing commas allowed, comments
/// not, others ignored). A shape outside the certified subset declines: a
/// file that is no regular file, one we cannot read, a top level other than
/// an object, a property repeated, a value of another type.
fn read_install_state(
    band: &FeatureBand,
    roots: &WorkloadRoots,
    architecture: &str,
    observer: &Observer,
) -> Result<InstallState, SdkResolveError> {
    let root = roots.manifest_roots().next().expect("a manifest root");
    let path = root
        .join("metadata")
        .join("workloads")
        .join(architecture)
        .join(band.to_string())
        .join("InstallState")
        .join("default.json");
    if !dotnet_io::file_exists(observer, &path) {
        return Ok(InstallState::default());
    }
    let decline = |why: &str| {
        Err(unsupported(format!(
            "the workload install state may not read as we read it ({why}): {}",
            path.display()
        )))
    };
    if !observed::is_file(observer, &path) {
        return decline("not a regular file");
    }
    let Ok(text) = observed::read_to_string(observer, &path) else {
        return decline("unreadable or not UTF-8");
    };
    let Some(JsonValue::Object(members)) = parse_strict_json(&text, true) else {
        return decline("not a JSON object");
    };
    let mut state = InstallState::default();
    for (i, (key, value)) in members.iter().enumerate() {
        if members[..i].iter().any(|(seen, _)| seen == key) {
            return decline("a property repeated");
        }
        match (key.as_str(), value) {
            ("useWorkloadSets", JsonValue::Bool(b)) => state.use_workload_sets = Some(*b),
            ("useWorkloadSets", JsonValue::Null)
            | ("manifests", JsonValue::Null)
            | ("workloadVersion", JsonValue::Null) => {}
            ("workloadVersion", JsonValue::String(s)) => state.workload_version = Some(s.clone()),
            ("manifests", JsonValue::Object(entries)) => {
                let mut map = Vec::new();
                for (id, version) in entries {
                    let JsonValue::String(version) = version else {
                        return decline("a manifest version that is not a string");
                    };
                    if map.iter().any(|(seen, _): &(String, String)| seen == id) {
                        return decline("a manifest repeated");
                    }
                    map.push((id.clone(), version.clone()));
                }
                state.manifests = Some(map);
            }
            ("useWorkloadSets" | "manifests" | "workloadVersion", _) => {
                return decline("a property of another type");
            }
            _ => {}
        }
    }
    Ok(state)
}
