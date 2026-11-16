//! Whether the workload resolver loads a set of resolved manifests without
//! throwing.
//!
//! The auto-import locator asks the workload resolver for installed SDK packs,
//! and that first reads every resolved `WorkloadManifest.json`
//! (`WorkloadManifestReader`, a hand-written reader that throws on any key or
//! value outside its grammar), with the localization catalog for the process's
//! UI culture, and then composes them (`WorkloadResolver.ComposeWorkloadManifests`,
//! which throws on a workload or pack two manifests define, and on a
//! `depends-on` it cannot meet). Any throw fails the resolution, so an empty
//! answer is exact only where none can happen.
//!
//! [`check_manifests_load`] certifies a strict subset of what loads, and
//! declines everything else: a document the strict JSON reader refuses (so
//! comments and trailing commas, which the reference skips, decline too), an
//! integer `version`, an id outside plain ASCII path components, a version
//! outside the plain spellings, a kind outside the named ones. Within the
//! subset each rule is the reference's, transcribed from dotnet/sdk
//! (`WorkloadManifestReader.cs`, `WorkloadManifestReader.Localization.cs`,
//! `WorkloadResolver.cs`); `workload_locator_diff` holds it to the resolver.

use std::path::{Path, PathBuf};

use super::super::global_json::{JsonValue, parse_json_string_map, parse_strict_json};
use super::{is_plain_release_version, unsupported};
use crate::SdkResolveError;
use crate::dotnet_io;
use crate::observed::{self, Observer};

/// A resolved manifest: the id the provider names it by (its directory's
/// name, or the known-list id that found it) and its directory.
pub(super) struct Resolved<'a> {
    pub(super) id: &'a str,
    pub(super) directory: &'a Path,
}

/// What composition reads of one manifest.
struct Facts {
    version: String,
    /// The workloads it defines, each with whether it is concrete and of the
    /// `dev` kind (so needs a description), and its description.
    workloads: Vec<(String, Option<String>)>,
    packs: Vec<String>,
    depends_on: Vec<(String, String)>,
}

/// Decline unless the workload resolver certainly loads `manifests`.
pub(super) fn check_manifests_load(
    manifests: &[Resolved<'_>],
    observer: &Observer,
) -> Result<(), SdkResolveError> {
    let mut all: Vec<(&Resolved<'_>, Facts)> = Vec::new();
    for manifest in manifests {
        let path = manifest.directory.join("WorkloadManifest.json");
        let decline = |why: &str| {
            Err(unsupported(format!(
                "the workload resolver may fail to load {} ({why})",
                path.display()
            )))
        };
        let Ok(text) = observed::read_to_string(observer, &path) else {
            return decline("unreadable or not UTF-8");
        };
        let facts = match read_manifest(&text) {
            Ok(facts) => facts,
            Err(why) => return decline(why),
        };
        for catalog in localization_catalogs(manifest.directory, observer)? {
            // A catalog replaces each workload's description it names; a
            // concrete `dev` workload whose description ends up empty throws.
            for (workload, description) in &facts.workloads {
                let key = format!("workloads/{workload}/description");
                if description.is_some()
                    && catalog
                        .iter()
                        .any(|(name, value)| *name == key && value.is_empty())
                {
                    return decline("a localization catalog empties a description");
                }
            }
        }
        all.push((manifest, facts));
    }
    compose(&all)
}

/// The entries of every localization catalog in `{directory}/localize` that a
/// UI culture could select (`WorkloadManifest.{culture}.json`), each read as
/// the reader reads it: the culture is the build process's, which we cannot
/// see, so every candidate must load.
fn localization_catalogs(
    directory: &Path,
    observer: &Observer,
) -> Result<Vec<Vec<(String, String)>>, SdkResolveError> {
    let localize = directory.join("localize");
    let entries = match observed::read_dir(observer, &localize) {
        Ok(entries) => entries,
        Err(err)
            if matches!(
                err.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
            ) =>
        {
            return Ok(Vec::new());
        }
        Err(err) => {
            return Err(unsupported(format!(
                "cannot enumerate {}: {err}",
                localize.display()
            )));
        }
    };
    let mut catalogs = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|err| {
            unsupported(format!("cannot enumerate {}: {err}", localize.display()))
        })?;
        let Some(name) = entry.name.to_str() else {
            return Err(unsupported(format!(
                "a localization entry with a non-UTF-8 name in {}",
                localize.display()
            )));
        };
        let lower = name.to_ascii_lowercase();
        if !(lower.starts_with("workloadmanifest.") && lower.ends_with(".json")) {
            continue;
        }
        let path: PathBuf = entry.path;
        // The catalog lookup asks CLR `File.Exists`, so a directory is passed
        // over; anything else it finds is opened.
        if !dotnet_io::file_exists(observer, &path) {
            continue;
        }
        let catalog = observed::is_file(observer, &path)
            .then(|| observed::read_to_string(observer, &path).ok())
            .flatten()
            .and_then(|text| parse_json_string_map(&text))
            .filter(|entries| {
                // `ReadStringDictionary` throws on a key it has already read.
                entries
                    .iter()
                    .enumerate()
                    .all(|(i, (key, _))| entries[..i].iter().all(|(seen, _)| seen != key))
            });
        match catalog {
            Some(catalog) => catalogs.push(catalog),
            None => {
                return Err(unsupported(format!(
                    "the workload resolver may fail to load the localization catalog {}",
                    path.display()
                )));
            }
        }
    }
    Ok(catalogs)
}

/// `ComposeWorkloadManifests`: every `depends-on` met, and no workload or pack
/// defined twice.
fn compose(all: &[(&Resolved<'_>, Facts)]) -> Result<(), SdkResolveError> {
    let decline = |why: String| {
        Err(unsupported(format!(
            "workload manifests may not compose: {why}"
        )))
    };
    let mut workloads: Vec<String> = Vec::new();
    let mut packs: Vec<String> = Vec::new();
    for (manifest, facts) in all {
        for (dependency, version) in &facts.depends_on {
            let Some((_, found)) = all
                .iter()
                .find(|(other, _)| other.id.eq_ignore_ascii_case(dependency))
            else {
                return decline(format!("{} depends on missing {dependency}", manifest.id));
            };
            let (Some(needed), Some(have)) =
                (release_triple(version), release_triple(&found.version))
            else {
                return decline(format!(
                    "{}'s dependency on {dependency} compares versions we do not certify",
                    manifest.id
                ));
            };
            if needed > have {
                return decline(format!("{} needs {dependency} {version}", manifest.id));
            }
        }
        for (workload, _) in &facts.workloads {
            let key = workload.to_ascii_lowercase();
            if workloads.contains(&key) {
                return decline(format!("workload {workload} is defined twice"));
            }
            workloads.push(key);
        }
        for pack in &facts.packs {
            let key = pack.to_ascii_lowercase();
            if packs.contains(&key) {
                return decline(format!("pack {pack} is defined twice"));
            }
            packs.push(key);
        }
    }
    Ok(())
}

/// `major.minor.patch` with no prerelease, as numbers, for an `FXVersion`
/// comparison we certify.
fn release_triple(version: &str) -> Option<(u64, u64, u64)> {
    if !is_plain_release_version(version) || version.contains('-') {
        return None;
    }
    let mut parts = version.split('.').map(|part| part.parse::<u64>().ok());
    Some((parts.next()??, parts.next()??, parts.next()??))
}

/// A workload or pack id `PathComponentUtilities.IsValidPathComponent`
/// certainly accepts: plain ASCII, no separators, not `.` or `..`.
fn is_id(s: &str) -> bool {
    !s.is_empty()
        && s != "."
        && s != ".."
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-' || b == b'_')
}

/// Which of `names` (ASCII, matched as `OrdinalIgnoreCase` matches them) `key`
/// is, or `None` for a key the reader throws on.
fn which<'n>(key: &str, names: &[&'n str]) -> Option<&'n str> {
    names
        .iter()
        .copied()
        .find(|name| key.eq_ignore_ascii_case(name))
}

/// The entries of `value` if it is an object whose keys `which` all names,
/// none twice: the reader throws on an unknown key and on a known one read
/// again.
fn fields<'v>(
    value: &'v JsonValue,
    names: &[&'static str],
) -> Result<Vec<(&'static str, &'v JsonValue)>, &'static str> {
    let JsonValue::Object(entries) = value else {
        return Err("expected an object");
    };
    let mut out: Vec<(&'static str, &'v JsonValue)> = Vec::new();
    for (key, value) in entries {
        let Some(name) = which(key, names) else {
            return Err("an unknown key");
        };
        if out.iter().any(|(seen, _)| *seen == name) {
            return Err("a key read twice");
        }
        out.push((name, value));
    }
    Ok(out)
}

fn string(value: &JsonValue) -> Result<&str, &'static str> {
    match value {
        JsonValue::String(s) => Ok(s),
        _ => Err("expected a string"),
    }
}

fn id_array(value: &JsonValue) -> Result<(), &'static str> {
    let JsonValue::Array(items) = value else {
        return Err("expected an array");
    };
    for item in items {
        if !is_id(string(item)?) {
            return Err("an id we do not certify");
        }
    }
    Ok(())
}

/// An object of distinct keys whose values are strings `check` accepts:
/// `ReadDependsOn`, `ReadStringDictionary`.
fn string_map<'v>(
    value: &'v JsonValue,
    case_insensitive_keys: bool,
    check: impl Fn(&str) -> bool,
) -> Result<Vec<(&'v str, &'v str)>, &'static str> {
    let JsonValue::Object(entries) = value else {
        return Err("expected an object");
    };
    let mut out: Vec<(&str, &str)> = Vec::new();
    for (key, value) in entries {
        let value = string(value)?;
        if !check(value) {
            return Err("a value we do not certify");
        }
        let repeated = out.iter().any(|(seen, _)| {
            if case_insensitive_keys {
                seen.eq_ignore_ascii_case(key)
            } else {
                seen == key
            }
        });
        if repeated || (case_insensitive_keys && !key.is_ascii()) {
            return Err("a key read twice, or one we cannot fold");
        }
        out.push((key, value));
    }
    Ok(out)
}

/// `WorkloadManifestReader.ReadWorkloadManifest` over `text`, within the
/// certified subset.
fn read_manifest(text: &str) -> Result<Facts, &'static str> {
    let document = parse_strict_json(text).ok_or("not JSON the strict reader accepts")?;
    let top = fields(
        &document,
        &[
            "version",
            "description",
            "depends-on",
            "workloads",
            "packs",
            "data",
        ],
    )?;
    let mut facts = Facts {
        version: String::new(),
        workloads: Vec::new(),
        packs: Vec::new(),
        depends_on: Vec::new(),
    };
    let mut has_version = false;
    for (name, value) in top {
        match name {
            "version" => {
                // An integer is read too, but not certified.
                let version = string(value)?;
                if !is_plain_release_version(version) {
                    return Err("a manifest version we do not certify");
                }
                facts.version = version.to_owned();
                has_version = true;
            }
            "description" => {
                string(value)?;
            }
            "depends-on" => {
                facts.depends_on = string_map(value, true, is_plain_release_version)?
                    .into_iter()
                    .map(|(id, version)| (id.to_owned(), version.to_owned()))
                    .collect();
            }
            "workloads" => {
                let JsonValue::Object(entries) = value else {
                    return Err("expected an object");
                };
                for (id, definition) in entries {
                    if !is_id(id) {
                        return Err("a workload id we do not certify");
                    }
                    if facts
                        .workloads
                        .iter()
                        .any(|(seen, _)| seen.eq_ignore_ascii_case(id))
                    {
                        return Err("a workload defined twice");
                    }
                    let needs_description = read_workload(definition)?;
                    facts.workloads.push((id.clone(), needs_description));
                }
            }
            "packs" => {
                let JsonValue::Object(entries) = value else {
                    return Err("expected an object");
                };
                for (id, pack) in entries {
                    if !is_id(id) {
                        return Err("a pack id we do not certify");
                    }
                    if facts.packs.iter().any(|seen| seen.eq_ignore_ascii_case(id)) {
                        return Err("a pack defined twice");
                    }
                    read_pack(pack)?;
                    facts.packs.push(id.clone());
                }
            }
            // Skipped whatever it holds.
            "data" => {}
            _ => unreachable!("`fields` admits only the names it is given"),
        }
    }
    if !has_version {
        return Err("no version");
    }
    Ok(facts)
}

/// `ReadWorkloadDefinition`: `Some(description)` for a concrete workload whose
/// `kind` is `dev`, which must have a non-empty one, and `None` for any other.
/// A workload with no `kind` is a `dev` one, but the reader asks for a
/// description only where the key names it.
fn read_workload(value: &JsonValue) -> Result<Option<String>, &'static str> {
    let entries = fields(
        value,
        &[
            "description",
            "kind",
            "abstract",
            "packs",
            "extends",
            "platforms",
            "replace-with",
        ],
    )?;
    let mut description = None;
    let mut is_abstract = false;
    let mut dev = false;
    for (name, value) in entries {
        match name {
            "description" => description = Some(string(value)?.to_owned()),
            "kind" => match which(string(value)?, &["dev", "build"]) {
                Some("dev") => dev = true,
                Some(_) => dev = false,
                None => return Err("a workload kind we do not certify"),
            },
            "abstract" => match value {
                JsonValue::Bool(b) => is_abstract = *b,
                _ => return Err("expected a bool"),
            },
            "packs" | "extends" => id_array(value)?,
            "platforms" => {
                let JsonValue::Array(items) = value else {
                    return Err("expected an array");
                };
                for item in items {
                    string(item)?;
                }
            }
            // A redirect throws `NotImplementedException`.
            "replace-with" => return Err("a workload redirect"),
            _ => unreachable!("`fields` admits only the names it is given"),
        }
    }
    if !is_abstract && dev {
        match description {
            Some(d) if !d.is_empty() => Ok(Some(d)),
            _ => Err("a concrete dev workload without a description"),
        }
    } else {
        Ok(None)
    }
}

/// `ReadWorkloadPack`.
fn read_pack(value: &JsonValue) -> Result<(), &'static str> {
    let entries = fields(value, &["version", "kind", "alias-to"])?;
    let (mut version, mut kind) = (false, false);
    for (name, value) in entries {
        match name {
            "version" => {
                string(value)?;
                version = true;
            }
            "kind" => {
                if which(
                    string(value)?,
                    &["sdk", "framework", "library", "template", "tool"],
                )
                .is_none()
                {
                    return Err("a pack kind we do not certify");
                }
                kind = true;
            }
            "alias-to" => {
                string_map(value, false, is_id)?;
            }
            _ => unreachable!("`fields` admits only the names it is given"),
        }
    }
    if version && kind {
        Ok(())
    } else {
        Err("a pack without a version or a kind")
    }
}
