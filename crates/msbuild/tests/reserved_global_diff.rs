//! Differential test: which caller global property names MSBuild refuses,
//! against the names `validate_inputs` refuses.
//!
//! MSBuild refuses a global property whose name is reserved
//! (`ReservedPropertyNames.IsReservedProperty`) or is not a valid property name,
//! and then evaluates nothing (`MSB4177` from the command line). A caller extra
//! property of such a name that we accept is committed as the property's value
//! while the real build has no value at all, so the two must refuse alike:
//!
//! - **The reserved list** ([`test_support::MSBUILD_RESERVED_NAMES`]) is the
//!   MSBuild's own, read by reflection (the oracle's `reservedNames` op), in
//!   both directions, for the MSBuild `dotnet` resolves and for each SDK of
//!   the devshell's dotnet root.
//! - **Each name** of a candidate set is put to both sides as the only global:
//!   every reserved name in several spellings, near misses of each (one
//!   character added, dropped, swapped, or replaced by a non-ASCII letter whose
//!   case relative is ASCII), the names MSBuild deliberately leaves
//!   unreserved, invalid names, and generated names over an alphabet of name
//!   and non-name characters. MSBuild's verdict (accepted, refused as
//!   reserved, refused as invalid) must be ours, exactly: a refusal of a name
//!   MSBuild accepts would only be a decline, but nothing here needs one.

mod common;

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::observed::host_fs::HostPath as _;

use borzoi_msbuild::{ParseError, parse_fsproj, test_support};
use common::case_axis::{non_ascii_lookalike, respell_name};
use common::{Oracle, SplitMix64};

/// What a side makes of one global property name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Verdict {
    Accepted,
    RefusedAsReserved,
    RefusedAsInvalid,
}

/// MSBuild's verdict on `name` as the only global property.
fn msbuild_verdict(oracle: &mut Oracle, name: &str) -> (Verdict, String) {
    match oracle.global_name(name) {
        Ok(()) => (Verdict::Accepted, String::new()),
        Err(message) if message.contains("property name is reserved") => {
            (Verdict::RefusedAsReserved, message)
        }
        Err(message) => (Verdict::RefusedAsInvalid, message),
    }
}

/// Our verdict on `name` as the only extra property.
fn our_verdict(name: &str) -> Verdict {
    let extras = HashMap::from([(name.to_string(), "x".to_string())]);
    match parse_fsproj(
        "<Project/>",
        Path::new("/repo/Demo.fsproj"),
        &extras,
        &HashMap::new(),
    ) {
        Ok(_) => Verdict::Accepted,
        Err(ParseError::ReservedPropertyInExtras(n)) => {
            assert_eq!(n, name, "the refusal names the caller's spelling");
            Verdict::RefusedAsReserved
        }
        Err(ParseError::InvalidPropertyNameInExtras(n)) => {
            assert_eq!(n, name, "the refusal names the caller's spelling");
            Verdict::RefusedAsInvalid
        }
        Err(other) => panic!("{name:?}: unexpected refusal {other:?}"),
    }
}

/// Names MSBuild leaves unreserved although they look like reserved ones: the
/// constants `ReservedPropertyNames` keeps for them, and other toolset names.
const UNRESERVED_LOOKALIKES: &[&str] = &[
    "MSBuildExtensionsPath",
    "MSBuildExtensionsPath32",
    "MSBuildExtensionsPath64",
    "MSBuildUserExtensionsPath",
    "LocalAppData",
    "MSBuildFileVersion",
    "MSBuildSemanticVersion",
    "OS",
    "MSBuildFrameworkToolsRoot",
    "MSBuildOverrideTasksPath",
    "DefaultOverrideToolsVersion",
    "MSBuildSDKsPath",
    "MSBuildIsRestoring",
    "MSBuildAllProjects",
    "MSBuildLoadMicrosoftTargetsReadOnly",
    "MSBuildProjectExtensionsPath",
    "MSBuildThisFileX",
    "MSBuildProject",
    "MSBuild",
    "VisualStudioVersion",
    "DOTNET_HOST_PATH",
    "RoslynTargetsPath",
    "Configuration",
];

/// Names that are not valid property names.
const INVALID: &[&str] = &[
    "",
    " ",
    "a b",
    "1abc",
    "-x",
    "a.b",
    "a;b",
    "a=b",
    "$(x)",
    "%41",
    "x%20y",
    "Ünïcode",
    "a\tb",
    " Foo",
    "Foo ",
    "MSBuildVersion ",
    " MSBuildVersion",
];

/// One character of a generated name: name characters, characters no name
/// holds, and non-ASCII letters whose case relatives are ASCII.
const ALPHABET: &[&str] = &[
    "a", "Z", "s", "I", "k", "_", "-", "0", "9", ".", ";", " ", "$", "(", "%", "\u{131}",
    "\u{17f}", "\u{212a}", "\u{dc}",
];

fn candidates(reserved: &[String]) -> BTreeSet<String> {
    let mut rng = SplitMix64(0x972);
    let mut out = BTreeSet::new();
    for name in reserved {
        out.insert(name.clone());
        out.insert(name.to_ascii_lowercase());
        out.insert(name.to_ascii_uppercase());
        for _ in 0..4 {
            out.insert(respell_name(&mut rng, name));
        }
        if let Some(lookalike) = non_ascii_lookalike(name) {
            out.insert(lookalike);
        }
        let chars: Vec<char> = name.chars().collect();
        out.insert(chars[..chars.len() - 1].iter().collect());
        out.insert(chars[1..].iter().collect());
        for suffix in ["X", "1", "-", "_", "s"] {
            out.insert(format!("{name}{suffix}"));
        }
        out.insert(format!("_{name}"));
        let at = 1 + rng.below(chars.len() - 1);
        let mut dropped = chars.clone();
        dropped.remove(at);
        out.insert(dropped.into_iter().collect());
        let at = rng.below(chars.len() - 1);
        let mut swapped = chars.clone();
        swapped.swap(at, at + 1);
        out.insert(swapped.into_iter().collect());
    }
    out.extend(UNRESERVED_LOOKALIKES.iter().map(|n| n.to_string()));
    out.extend(INVALID.iter().map(|n| n.to_string()));
    for _ in 0..300 {
        let mut name = if rng.below(3) == 0 {
            "MSBuild".to_string()
        } else {
            String::new()
        };
        for _ in 0..rng.below(8) {
            name.push_str(rng.pick(ALPHABET));
        }
        out.insert(name);
    }
    out
}

#[test]
fn our_reserved_names_are_msbuilds() {
    let mut oracle = Oracle::spawn();
    let theirs: BTreeSet<String> = oracle
        .reserved_names()
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    let ours: BTreeSet<String> = test_support::MSBUILD_RESERVED_NAMES
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    assert_eq!(
        ours.len(),
        test_support::MSBUILD_RESERVED_NAMES.len(),
        "our reserved list spells a name twice"
    );
    let missing: Vec<_> = theirs.difference(&ours).collect();
    let extra: Vec<_> = ours.difference(&theirs).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "reserved by MSBuild, not by us: {missing:?}; reserved by us, not by MSBuild: {extra:?}"
    );
}

/// Every SDK under the devshell's dotnet root, each `<root>/sdk/<version>`
/// holding an MSBuild, by its real path (as the muxer reaches it).
///
/// The corpus root's SDK 11 is not among them: its MSBuild needs the .NET 11
/// runtime, and the oracle runs on .NET 10.
fn installed_sdks() -> Vec<PathBuf> {
    let root = common::dotnet_root_from_env();
    let mut sdks: Vec<PathBuf> = host_fs::read_dir(root.join("sdk"))
        .expect("the dotnet root has an sdk directory")
        .map(|entry| entry.expect("sdk directory entry").path())
        .filter(|path| path.join("MSBuild.dll").host_is_file())
        .map(|path| host_fs::canonicalize(&path).expect("an installed SDK resolves"))
        .collect();
    sdks.sort();
    sdks
}

#[test]
fn every_installed_msbuild_reserves_our_names() {
    // An MSBuild that reserves a name we do not would refuse a global we
    // commit. Each SDK of the devshell is asked, so an SDK added to it that
    // reserves a new name fails here.
    let ours: BTreeSet<String> = test_support::MSBUILD_RESERVED_NAMES
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    let sdks = installed_sdks();
    assert!(!sdks.is_empty(), "no SDK installed");
    for sdk in sdks {
        let dir = tempfile::TempDir::new().unwrap();
        let theirs: BTreeSet<String> = Oracle::spawn_for_sdk(&sdk, dir.path())
            .reserved_names()
            .iter()
            .map(|n| n.to_ascii_lowercase())
            .collect();
        assert_eq!(
            theirs,
            ours,
            "the MSBuild of {} reserves a different set",
            sdk.display()
        );
    }
}

#[test]
fn a_global_name_is_refused_exactly_when_msbuild_refuses_it() {
    let mut oracle = Oracle::spawn();
    let reserved = oracle.reserved_names();
    let candidates = candidates(&reserved);
    let mut disagreements = Vec::new();
    let mut census: HashMap<Verdict, usize> = HashMap::new();
    for name in &candidates {
        let (theirs, message) = msbuild_verdict(&mut oracle, name);
        let ours = our_verdict(name);
        *census.entry(theirs).or_default() += 1;
        if theirs != ours {
            disagreements.push(format!(
                "{name:?}: MSBuild {theirs:?} ({message}), ours {ours:?}"
            ));
        }
    }
    eprintln!(
        "{} candidate names; MSBuild's verdicts: {census:?}",
        candidates.len()
    );
    // Every verdict is exercised, every reserved name among the refusals.
    for verdict in [
        Verdict::Accepted,
        Verdict::RefusedAsReserved,
        Verdict::RefusedAsInvalid,
    ] {
        assert!(
            census.get(&verdict).copied().unwrap_or(0) > 0,
            "no candidate drew {verdict:?}"
        );
    }
    assert!(
        census[&Verdict::RefusedAsReserved] >= reserved.len(),
        "fewer reserved refusals than reserved names: {census:?}"
    );
    assert!(
        disagreements.is_empty(),
        "{} of {} names disagree:\n{}",
        disagreements.len(),
        candidates.len(),
        disagreements.join("\n")
    );
}
