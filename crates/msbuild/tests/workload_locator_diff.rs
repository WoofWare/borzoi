//! The workload locator SDKs, held to MSBuild's own workload resolver.
//!
//! `borzoi_msbuild::workloads` reimplements what the workload MSBuild SDK
//! resolver answers for `Microsoft.NET.SDK.WorkloadManifestTargetsLocator`,
//! for `Microsoft.NET.SDK.WorkloadAutoImportPropsLocator`, and for any other
//! SDK name, which it looks up as a workload pack. This differential asks the
//! real one, through `tools/workload-oracle`, which loads each installed
//! SDK's `Microsoft.NET.Sdk.WorkloadMSBuildSdkResolver.dll` and calls
//! `CachingWorkloadResolver.Resolve` (the call MSBuild makes) on generated
//! dotnet layouts. It grades every SDK of the devshell's corpus root
//! (`BORZOI_DOTNET_ROOT_SDK11`), so a prerelease SDK's resolver is graded as
//! well as the release ones.
//!
//! Eight sweeps, each *certain-implies-exact* (an answer we commit must be the
//! resolver's) with a positive domain where we must commit:
//!
//! - the feature band of a host SDK version (`SdkFeatureBand`), over a
//!   generated grid of version strings: release, `preview.N`, `rc.N`, with and
//!   without a build suffix, the substrings that collapse a prerelease to its
//!   release band, build metadata, and malformed cores;
//! - the order of two feature bands (`SdkFeatureBand.CompareTo`), over pairs
//!   from the same grid;
//! - the locators themselves, over generated layouts: band directories around
//!   the host's (its own, its release band, earlier and later previews and
//!   release candidates, earlier and later releases, non-canonical spellings),
//!   known-list order, flat and versioned manifests, unresolvable id
//!   directories, and a missing `WorkloadManifest.targets`;
//! - which of a manifest's version directories wins (the provider's
//!   `VersionCompare`), over every name alone, every pair and a sample of
//!   triples of a vocabulary of release, prerelease and malformed names;
//! - workload sets (of the host band, other bands and the baseline band),
//!   the install state under the oracle's architecture or another, and a
//!   `global.json` pinning a set or choosing the update mode, over generated
//!   layouts (the oracle is handed the `global.json`);
//! - the installed SDK packs the auto-import locator returns, over generated
//!   manifests declaring packs of every kind, with versions, `alias-to` maps
//!   against generated runtime identifier chains, and pack directories under
//!   the user and dotnet roots (with odd entries in place of a pack or its
//!   `Sdk/AutoImport.props`), plus planted layouts each resolver and we must
//!   answer as planted, each graded SDK's own installation, and its own
//!   manifests with every pack they name installed;
//! - the workload pack an SDK name that is no locator names
//!   (`TryGetPackInfo`): installed, missing, or no pack for the host, over
//!   generated manifests declaring packs of every kind, aliased or not, looked
//!   up in any case, with each pack placed under the user and dotnet roots at
//!   its kind's location or another's (as a directory, a file or an odd
//!   entry), plus planted layouts, and every pack name the graded SDKs' own
//!   manifests' targets import, on their installation and with every pack
//!   installed;
//! - every existence probe the resolver makes (`File.Exists` of a manifest,
//!   its targets, a marker, the install state, the known list, the runtime
//!   identifier chain, and `Directory.GetDirectories` of a band or id
//!   directory), with a dangling link, a link loop, a directory, a link to
//!   one, a link to a file, a socket and, where nothing opens the path, a
//!   FIFO at the probed path.

mod common;

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use borzoi_msbuild::observed;
use borzoi_msbuild::observed::host_fs::HostPath as _;
use borzoi_msbuild::observed::{Observer, host_fs};
use borzoi_msbuild::workloads::{
    EXECUTABLE_HEADER_BYTES, ProcessArchitecture, WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
    WORKLOAD_MANIFEST_TARGETS_LOCATOR, WorkloadEnvironment, WorkloadPackResolution,
    resolve_workload_locator, resolve_workload_pack,
};
use borzoi_msbuild::{SdkResolution, test_support};
use borzoi_oracle_harness::workload_oracle::Oracle;
use common::SplitMix64;
#[cfg(unix)]
use common::odd_entry::{self, Odd};
use serde_json::json;

/// The devshell's corpus root (flake.nix, `dotnet-sdk-corpus`): the release
/// SDKs and SDK 11's prerelease.
const SDK11_ROOT_VAR: &str = "BORZOI_DOTNET_ROOT_SDK11";

/// Every SDK directory of the corpus root, so every installed resolver is
/// graded.
fn graded_sdks() -> Vec<PathBuf> {
    let root = std::env::var_os(SDK11_ROOT_VAR)
        .map(PathBuf::from)
        .unwrap_or_else(|| panic!("{SDK11_ROOT_VAR} is not set; run under nix develop"));
    let mut sdks: Vec<PathBuf> = host_fs::read_dir(root.join("sdk"))
        .expect("the corpus root has an sdk directory")
        .map(|entry| entry.expect("sdk directory entry").path())
        .filter(|path| {
            path.join("Microsoft.NET.Sdk.WorkloadMSBuildSdkResolver.dll")
                .host_is_file()
        })
        .collect();
    sdks.sort();
    assert!(
        sdks.iter().any(|sdk| sdk
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.contains('-'))),
        "the corpus root must hold a prerelease SDK for this differential to grade one: {sdks:?}"
    );
    sdks
}

// ---------------------------------------------------------------------------
// Version strings.

const PRERELEASES: &[&str] = &[
    "preview.1",
    "preview.7",
    "preview.10",
    "rc.1",
    "rc.2",
    "rc.10",
    "preview.1.25101.3",
    "preview.7.25380.108",
    "rc.1.26425.128",
    "rc.2.25502.107",
    "alpha",
    "alpha.1",
    "beta.2.3",
    "rc",
    "preview",
    "1",
    "1.2",
    "0.3.4",
    "dev",
    "ci.1",
    "rtm.25515.1",
    "preview.1.dev",
    "specific.1",
    "rc.1-x",
    "Preview.1",
    "RC.1",
    "preview.01",
    "preview..1",
    "preview.1_2",
];

const CORES: &[&str] = &[
    "10.0.100",
    "10.0.101",
    "10.0.112",
    "10.0.199",
    "10.0.200",
    "10.0.201",
    "10.0.300",
    "10.0.301",
    "10.0.401",
    "11.0.100",
    "11.0.105",
    "11.0.200",
    "9.0.100",
    "8.0.100",
    "12.1.0",
    "10.0.0",
    "10.0.1",
    "10.0",
    "10.0.100.1",
    "010.0.100",
    "10.0.0100",
    "2147483648.0.100",
];

const METADATA: &[&str] = &["", "+abc", "+abc.def", "+"];

fn version_grid() -> Vec<String> {
    let mut out = Vec::new();
    for core in CORES {
        for metadata in METADATA {
            out.push(format!("{core}{metadata}"));
            for pre in PRERELEASES {
                out.push(format!("{core}-{pre}{metadata}"));
            }
        }
    }
    out.push(String::new());
    out.push("-rc.1".to_owned());
    out
}

/// The versions whose band we must compute: a well-formed release core and no
/// build metadata, with no prerelease, a `preview.N` or `rc.N` one, or either
/// with a build suffix — the spellings released SDKs carry.
fn must_band(version: &str) -> bool {
    let (core, pre) = match version.split_once('-') {
        Some((core, pre)) => (core, Some(pre)),
        None => (version, None),
    };
    let parts: Vec<&str> = core.split('.').collect();
    let plain_number = |s: &str| {
        !s.is_empty()
            && s.len() <= 9
            && s.bytes().all(|b| b.is_ascii_digit())
            && (s == "0" || !s.starts_with('0'))
    };
    if parts.len() != 3 || !parts.iter().all(|p| plain_number(p)) || version.contains('+') {
        return false;
    }
    match pre {
        None => true,
        Some(pre) => {
            let ids: Vec<&str> = pre.split('.').collect();
            matches!(ids.first(), Some(&"preview" | &"rc"))
                && (ids.len() == 2 || ids.len() == 4)
                && ids[1..].iter().all(|id| plain_number(id))
        }
    }
}

/// The architecture read off a dotnet root's `dotnet` muxer, as a host reads
/// it (its leading bytes, through the observer), is the one a process of that
/// muxer reports: the one the install state is keyed by.
#[test]
fn the_muxer_s_header_names_its_process_architecture() {
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let theirs = oracle.request(&json!({"op": "identity"}))["processArchitecture"]
            .as_str()
            .expect("the oracle names its architecture")
            .to_owned();
        let muxer = sdk
            .parent()
            .and_then(Path::parent)
            .expect("an SDK directory sits at <dotnet-root>/sdk/<version>")
            .join(if cfg!(windows) {
                "dotnet.exe"
            } else {
                "dotnet"
            });
        let header = observed::read_prefix(&Observer::new(), &muxer, EXECUTABLE_HEADER_BYTES)
            .expect("the muxer reads");
        assert_eq!(
            ProcessArchitecture::of_executable(&header).map(ProcessArchitecture::name),
            Some(theirs.as_str()),
            "{}: the muxer's header against the process it runs ({})",
            sdk.display(),
            muxer.display()
        );
    }
}

#[test]
fn a_host_feature_band_is_the_resolver_s() {
    let versions = version_grid();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut committed = 0;
        for version in &versions {
            let ours = test_support::workload_feature_band(version);
            let theirs = oracle.request(&json!({"op": "band", "version": version}));
            let their_band = theirs["ok"]
                .as_bool()
                .unwrap()
                .then(|| theirs["band"].as_str().unwrap().to_owned());
            if let Some(ours) = &ours {
                committed += 1;
                assert_eq!(
                    Some(ours),
                    their_band.as_ref(),
                    "{}: band of {version:?}: we commit {ours:?}, the resolver says {theirs}",
                    sdk.display()
                );
            } else {
                assert!(
                    !must_band(version),
                    "{}: we decline the band of {version:?}, which the resolver computes as {theirs}",
                    sdk.display()
                );
            }
        }
        println!(
            "{}: committed {committed} of {} bands",
            sdk.display(),
            versions.len()
        );
    }
}

#[test]
fn feature_bands_order_as_the_resolver_orders_them() {
    let bands: Vec<String> = version_grid()
        .into_iter()
        .filter(|v| test_support::workload_feature_band(v).is_some())
        .collect();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut compared = 0;
        let mut rng = SplitMix64(0xba4d_0bde);
        for _ in 0..4000 {
            let a = rng.pick(&bands);
            let b = rng.pick(&bands);
            let ours = test_support::compare_workload_feature_bands(a, b)
                .expect("a version whose band we compute orders");
            let theirs = oracle.request(&json!({"op": "compareBands", "a": a, "b": b}));
            assert_eq!(theirs["ok"], json!(true), "{a} vs {b}: {theirs}");
            let theirs = match theirs["cmp"].as_i64().unwrap() {
                -1 => Ordering::Less,
                0 => Ordering::Equal,
                _ => Ordering::Greater,
            };
            assert_eq!(ours, theirs, "{}: {a} vs {b}", sdk.display());
            compared += 1;
        }
        assert!(compared > 0);
    }
}

// ---------------------------------------------------------------------------
// Layouts.

/// Manifest ids the layouts draw from. `microsoft.net.workload.ios` is on the
/// resolver's outdated list.
const IDS: &[&str] = &[
    "contoso.one",
    "contoso.two",
    "contoso.three",
    "contoso.four",
    "microsoft.net.workload.ios",
];

/// An id no known list names, found only in a band directory.
const UNLISTED_ID: &str = "contoso.unlisted";

/// A manifest version directory name, and whether it is in the domain we must
/// resolve beside any other of these: a name `VersionCompare` certainly
/// compares, which none of the others ties with.
const MANIFEST_VERSIONS: &[(&str, bool)] = &[
    ("1.0.0", true),
    ("1.0.2", true),
    ("1.0.10", true),
    ("2.0.0", true),
    ("2.0.0-rc.1", true),
    ("2.0.0-preview.3.1", true),
    ("2.0.0-rc.1.26425.128", true),
    ("1.0.0.1", true),
    ("2.0", true),
    ("26.5.11720-net11-p6", true),
    ("2.0.0+abc", false),
    ("not-a-version", false),
];

/// The manifest versions in the domain we must resolve.
const PLAIN_MANIFEST_VERSIONS: &[(&str, bool)] = &[
    ("1.0.0", true),
    ("1.0.2", true),
    ("1.0.10", true),
    ("2.0.0", true),
    ("2.0.0-rc.1", true),
    ("2.0.0-preview.3.1", true),
];

struct Host {
    version: String,
    /// `(major, minor, patch-hundreds)` and the prerelease label and number,
    /// for deriving the band directories around it.
    major: u64,
    minor: u64,
    hundreds: u64,
    pre: Option<(&'static str, u64)>,
}

fn gen_host(rng: &mut SplitMix64) -> Host {
    let major = 10 + rng.below(3) as u64;
    let minor = 0;
    let hundreds = 1 + rng.below(3) as u64;
    let patch = hundreds * 100 + *rng.pick(&[0, 0, 1, 12]);
    let pre = match rng.below(3) {
        0 => None,
        1 => Some(("preview", 1 + rng.below(8) as u64)),
        _ => Some(("rc", 1 + rng.below(2) as u64)),
    };
    let mut version = format!("{major}.{minor}.{patch}");
    if let Some((label, n)) = pre {
        version.push_str(&format!("-{label}.{n}"));
        if rng.below(2) == 0 {
            version.push_str(&format!(".{}.{}", 25000 + rng.below(999), rng.below(200)));
        }
    } else if rng.below(6) == 0 {
        // A prerelease that collapses to the release band.
        version.push_str(rng.pick(&["-dev", "-ci.1", "-rtm.25515.1"]));
    }
    if rng.below(4) == 0 {
        // Build metadata, which the user-local check cannot parse on a host
        // without a prerelease.
        version.push_str("+abc");
    }
    Host {
        version,
        major,
        minor,
        hundreds,
        pre,
    }
}

/// Band directory names around the host's, with whether each is a spelling
/// the resolver parses (the rest make its fallback enumeration throw).
fn band_candidates(host: &Host) -> Vec<(String, bool)> {
    let (ma, mi, h) = (host.major, host.minor, host.hundreds);
    let release = |ma: u64, h: u64| format!("{ma}.{mi}.{}", h * 100);
    let mut out = vec![
        (release(ma, h), true),
        (release(ma, h + 1), true),
        (release(ma - 1, h), true),
        (release(ma - 1, 4), true),
        (format!("{ma}.{mi}.{}", h * 100 + 5), true),
        (format!("{ma}.{mi}.{}-preview.1", h * 100), true),
        (format!("{ma}.{mi}.{}-preview.3.25123.4", h * 100), true),
        (format!("{ma}.{mi}.{}-rc.2", h * 100), true),
        (format!("{ma}.{mi}.{}-rc.1", (h + 1) * 100), true),
        (format!("{}.{mi}.{}-rc.1", ma - 1, h * 100), true),
        (format!("{ma}.{mi}.{}-dev", h * 100), true),
    ];
    if let Some((label, n)) = host.pre {
        out.push((format!("{ma}.{mi}.{}-{label}.{n}", h * 100), true));
        out.push((format!("{ma}.{mi}.{}-{label}.{}", h * 100, n + 1), true));
        if n > 1 {
            out.push((format!("{ma}.{mi}.{}-{label}.{}", h * 100, n - 1), true));
        }
    }
    out.push(("not-a-band".to_owned(), false));
    out
}

/// One generated layout, and whether it is in the domain we must resolve.
struct Layout {
    _dir: tempfile::TempDir,
    dotnet_root: PathBuf,
    /// The user profile's dotnet directory, handed to both resolvers.
    user_root: Option<PathBuf>,
    host: Host,
    in_domain: bool,
    description: String,
}

impl Host {
    /// The host's feature band directory name, and its release band's.
    fn bands(&self) -> (String, String) {
        let release = format!("{}.{}.{}", self.major, self.minor, self.hundreds * 100);
        let band = match self.pre {
            Some((label, n)) => format!("{release}-{label}.{n}"),
            None => release.clone(),
        };
        (band, release)
    }
}

/// Fill `band_dir` with a random subset of the manifest ids, each flat,
/// versioned or unresolvable, with or without `WorkloadManifest.targets`;
/// clears `in_domain` for a manifest version outside the plain spellings,
/// which a `plain` band never holds.
fn populate_band(
    rng: &mut SplitMix64,
    band_dir: &Path,
    in_domain: &mut bool,
    plain: bool,
) -> Vec<String> {
    std::fs::create_dir_all(band_dir).unwrap();
    let mut contents = Vec::new();
    for id in IDS.iter().chain([&UNLISTED_ID]) {
        if rng.below(3) == 0 {
            continue;
        }
        let id_dir = band_dir.join(id);
        let targets = rng.below(5) != 0;
        let shape = match rng.below(4) {
            0 => {
                write(&id_dir.join("WorkloadManifest.json"), MANIFEST_JSON);
                if targets {
                    write(&id_dir.join("WorkloadManifest.targets"), "<Project />");
                }
                "flat".to_owned()
            }
            1 => {
                std::fs::create_dir_all(&id_dir).unwrap();
                "empty".to_owned()
            }
            _ => {
                let mut names = Vec::new();
                for _ in 0..1 + rng.below(2) {
                    let (version, in_spelling) = if plain {
                        *rng.pick(PLAIN_MANIFEST_VERSIONS)
                    } else {
                        *rng.pick(MANIFEST_VERSIONS)
                    };
                    if !in_spelling {
                        *in_domain = false;
                    }
                    let version_dir = id_dir.join(version);
                    write(&version_dir.join("WorkloadManifest.json"), MANIFEST_JSON);
                    if targets {
                        write(&version_dir.join("WorkloadManifest.targets"), "<Project />");
                    }
                    names.push(version);
                }
                format!("versions {names:?}")
            }
        };
        contents.push(format!(
            "{id}: {shape}{}",
            if targets { "" } else { " (no targets)" }
        ));
    }
    contents
}

fn write(path: &Path, content: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, content).unwrap();
}

const MANIFEST_JSON: &str = r#"{"version": "1.0.0", "workloads": {}, "packs": {}}"#;

/// The file `WorkloadResolver.Create` reads the runtime identifiers from, in
/// the host SDK directory, and what a linux-x64 SDK holds there.
const RID_CHAIN: &str = "NETCoreSdkRuntimeIdentifierChain.txt";
const RID_CHAIN_CONTENT: &str = "linux-x64\nlinux\nunix\nany\nbase\n";

/// A generated layout. A `plain` one keeps to the domain we must resolve: a
/// host version we certify, band directories the resolver parses, and plain
/// manifest versions. The domain is rarely met otherwise, and a sweep of such
/// layouts never holds a decline of ours to the resolver.
fn gen_layout(rng: &mut SplitMix64, plain: bool) -> Layout {
    let dir = tempfile::TempDir::new().unwrap();
    let dotnet_root = host_fs::canonicalize(dir.path()).unwrap().join("dotnet");
    let host = loop {
        let host = gen_host(rng);
        if !plain || test_support::workload_accepts_host_version(&host.version) {
            break host;
        }
    };
    let mut description = format!("host {}\n", host.version);
    // The locators resolve a host whose spelling they certify; for the rest
    // they make no claim.
    let mut in_domain = test_support::workload_accepts_host_version(&host.version);

    let sdk_dir = dotnet_root.join("sdk").join(&host.version);
    std::fs::create_dir_all(&sdk_dir).unwrap();
    if rng.below(2) == 0 {
        write(&sdk_dir.join(RID_CHAIN), RID_CHAIN_CONTENT);
        description.push_str("runtime identifier chain\n");
    }
    if rng.below(5) != 0 {
        let mut known: Vec<&str> = IDS.iter().copied().filter(|_| rng.below(4) != 0).collect();
        for i in (1..known.len()).rev() {
            known.swap(i, rng.below(i + 1));
        }
        write(
            &sdk_dir.join("KnownWorkloadManifests.txt"),
            &known.join("\n"),
        );
        description.push_str(&format!("known {known:?}\n"));
    }

    for (band, parses) in band_candidates(&host) {
        if rng.below(2) == 0 {
            continue;
        }
        if !parses {
            if plain {
                continue;
            }
            in_domain = false;
        }
        let band_dir = dotnet_root.join("sdk-manifests").join(&band);
        let contents = populate_band(rng, &band_dir, &mut in_domain, plain);
        description.push_str(&format!("band {band}: {contents:?}\n"));
    }

    // A user-local install: a user root (sometimes with manifests of its own
    // for the host band), and the `userlocal` marker under the release band's
    // name, under the prerelease band's, or nowhere.
    let user_root = (rng.below(2) == 0).then(|| {
        let user_root = dotnet_root.parent().unwrap().join("user");
        std::fs::create_dir_all(&user_root).unwrap();
        let (band, release) = host.bands();
        if rng.below(2) == 0 {
            let contents = populate_band(
                rng,
                &user_root.join("sdk-manifests").join(&band),
                &mut in_domain,
                plain,
            );
            description.push_str(&format!("user band {band}: {contents:?}\n"));
        }
        let marker_band = match rng.below(3) {
            0 => Some(release),
            1 => Some(band),
            _ => None,
        };
        if let Some(marker_band) = marker_band {
            write(
                &dotnet_root
                    .join("metadata")
                    .join("workloads")
                    .join(&marker_band)
                    .join("userlocal"),
                "",
            );
            description.push_str(&format!("userlocal marker under {marker_band}\n"));
        }
        user_root
    });
    Layout {
        _dir: dir,
        dotnet_root,
        user_root,
        host,
        in_domain,
        description,
    }
}

fn ours(layout: &Layout, locator: &str) -> Option<Vec<String>> {
    let env = WorkloadEnvironment {
        user_dotnet_root: layout.user_root.as_deref(),
        overrides_present: false,
        resolver_switched_off: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    let sdk_dir = layout.dotnet_root.join("sdk").join(&layout.host.version);
    match resolve_workload_locator(
        locator,
        &layout.dotnet_root,
        &sdk_dir,
        &env,
        &Observer::new(),
    ) {
        Ok(SdkResolution::Roots(roots)) => Some(
            roots
                .iter()
                .map(|p| p.to_string_lossy().into_owned())
                .collect(),
        ),
        Ok(other) => panic!("a locator resolves to roots, not {other:?}"),
        Err(_) => None,
    }
}

fn theirs(oracle: &mut Oracle, layout: &Layout, locator: &str) -> Result<Vec<String>, String> {
    let response = oracle.request(&json!({
        "op": "resolve",
        "sdk": locator,
        "dotnetRoot": layout.dotnet_root.to_string_lossy(),
        "sdkVersion": layout.host.version,
        "userProfileDir": layout.user_root.as_ref().map(|p| p.to_string_lossy()),
    }));
    if response["ok"] != json!(true) {
        return Err(response["thrown"].to_string());
    }
    assert_eq!(response["kind"], json!("multiple"), "{response}");
    Ok(response["paths"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p.as_str().unwrap().to_owned())
        .collect())
}

#[test]
fn the_workload_locators_resolve_as_the_resolver_does() {
    sweep_locators(0x0b0a_7d5e, 150);
}

/// The fresh-seed twin; `BORZOI_MSBUILD_SOAK_SEED` reproduces a run.
#[test]
#[ignore = "soak: run with --ignored; BORZOI_MSBUILD_SOAK_SEED reproduces"]
fn soak_the_workload_locators_resolve_as_the_resolver_does() {
    let (seed, cases) = common::soak_parameters("workload_locator_diff", 2000);
    sweep_locators(seed, cases);
}

/// Both locators' answers on `layout`, ours against the resolver's: the
/// number we commit, the number the resolver gives on a layout in the domain
/// we must resolve, and why the first wrong one is wrong.
fn grade(oracle: &mut Oracle, layout: &Layout) -> (usize, usize, Option<String>) {
    let mut committed = 0;
    let mut answered = 0;
    let mut failure = None;
    for locator in [
        WORKLOAD_MANIFEST_TARGETS_LOCATOR,
        WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
    ] {
        let ours = ours(layout, locator);
        let theirs = theirs(oracle, layout, locator);
        let verdict = match (&ours, &theirs) {
            (Some(ours), Ok(theirs)) if ours == theirs => None,
            (Some(ours), _) => Some(format!(
                "we commit {ours:#?}, the resolver says {theirs:#?}"
            )),
            (None, Ok(theirs)) if layout.in_domain => {
                Some(format!("we decline, the resolver says {theirs:#?}"))
            }
            (None, _) => None,
        };
        if ours.is_some() {
            committed += 1;
        }

        if theirs.is_ok() && layout.in_domain {
            answered += 1;
        }
        if let Some(verdict) = verdict {
            failure.get_or_insert(format!("{locator}: {verdict}"));
        }
    }
    (committed, answered, failure)
}

fn sweep_locators(seed: u64, cases: usize) {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(seed);
        let mut committed = 0;
        let mut prerelease_committed = 0;
        let mut hosts = BTreeSet::new();
        for case in 0..cases {
            let layout = gen_layout(&mut rng, case % 2 == 1);
            let (here, _, failure) = grade(&mut oracle, &layout);
            committed += here;
            if layout.host.pre.is_some() {
                prerelease_committed += here;
            }
            hosts.insert(layout.host.version.clone());
            if let Some(failure) = failure
                && failures.len() < 8
            {
                failures.push(format!(
                    "{} case {case}, {failure}\n{}",
                    sdk.display(),
                    layout.description
                ));
            }
        }
        println!(
            "{}: committed {committed} of {} answers ({prerelease_committed} on prerelease hosts), {} hosts",
            sdk.display(),
            cases * 2,
            hosts.len()
        );
        assert!(
            committed >= cases * 2 / 3 && prerelease_committed >= cases / 3,
            "{}: the sweep committed too little to grade ({committed}, {prerelease_committed} on \
             prerelease hosts)",
            sdk.display()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// ---------------------------------------------------------------------------
// What the resolver's existence probes meet.

/// A path the resolver asks `File.Exists` of, and what it does with what it
/// finds there.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
enum Probe {
    /// `WorkloadManifest.targets` in a resolved manifest directory: the
    /// targets locator keeps the directory where it exists.
    Targets,
    /// `WorkloadManifest.json`: it makes its directory a manifest directory;
    /// a flat one is then opened (failures caught) to read its version, and
    /// the auto-import locator opens every resolved one to load it.
    ManifestJson,
    /// `metadata/workloads/{release band}/userlocal`: the user root takes part.
    UserLocal,
    /// `metadata/workloads/{release band}/installertype/msi`: an MSI install,
    /// whose install state lives outside the layout.
    Msi,
    /// `metadata/workloads/{arch}/{band}/InstallState/default.json`: read
    /// where it exists.
    InstallState,
    /// `KnownWorkloadManifests.txt` in the host SDK directory: read with
    /// `File.ReadAllLines` where it exists.
    KnownList,
    /// `NETCoreSdkRuntimeIdentifierChain.txt` in the host SDK directory:
    /// read with `File.ReadAllLines` where it exists.
    RidChain,
    /// An entry of a band directory or a manifest id directory, which
    /// `Directory.GetDirectories` lists: only a directory, or a link it can
    /// follow to one, is a candidate.
    Entry,
}

#[cfg(unix)]
impl Probe {
    const ALL: &[Probe] = &[
        Probe::Targets,
        Probe::ManifestJson,
        Probe::UserLocal,
        Probe::Msi,
        Probe::InstallState,
        Probe::KnownList,
        Probe::RidChain,
        Probe::Entry,
    ];

    /// The shapes this probe is graded on: a FIFO only where nothing opens
    /// the path, since the resolver's read of one blocks for good.
    fn shapes(self) -> &'static [Odd] {
        match self {
            Probe::Targets | Probe::UserLocal | Probe::Msi | Probe::Entry => Odd::ALL,
            Probe::ManifestJson | Probe::InstallState | Probe::KnownList | Probe::RidChain => {
                Odd::OPENABLE
            }
        }
    }

    /// Whether we decline `odd` here on purpose while the resolver answers:
    /// an MSI marker or an install state is outside what we resolve, and a
    /// flat manifest or a targets file that is a socket is one we decline
    /// rather than tell apart from a FIFO, whose read hangs the resolver (a
    /// flat manifest) or MSBuild's import and the walk (a targets file).
    fn declines_on_purpose(self, odd: Odd) -> bool {
        match self {
            Probe::Msi | Probe::InstallState => odd.file_exists_to_dotnet(),
            Probe::ManifestJson => odd == Odd::Socket,
            Probe::Targets => matches!(odd, Odd::Socket | Odd::Fifo),
            _ => false,
        }
    }

    /// Whether the resolver throws on `odd` here, whatever the layout: it
    /// reads a file `File.Exists` found, and the read of a dangling link, a
    /// link loop or a socket fails.
    fn resolver_throws(self, odd: Odd) -> bool {
        matches!(self, Probe::KnownList | Probe::RidChain)
            && matches!(odd, Odd::Dangling | Odd::Loop | Odd::Socket)
    }
}

/// `RuntimeInformation.ProcessArchitecture`'s name for this machine, which
/// the install-state folder is keyed by.
#[cfg(unix)]
fn process_architecture() -> &'static str {
    match std::env::consts::ARCH {
        "x86_64" => "X64",
        "aarch64" => "Arm64",
        other => panic!("no ProcessArchitecture name known for {other}"),
    }
}

/// The directories in `dir`, sorted.
#[cfg(unix)]
fn subdirectories(dir: &Path) -> Vec<PathBuf> {
    let Ok(entries) = host_fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut out: Vec<PathBuf> = entries
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.host_is_dir())
        .collect();
    out.sort();
    out
}

/// Every file named `name` under `root`, sorted.
fn files_named(root: &Path, name: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = host_fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.host_is_dir() {
                stack.push(path);
            } else if path.file_name().is_some_and(|n| n == name) {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// Put `odd` at the path `probe` asks about in `layout`, or `None` where the
/// layout has no such path (no manifest to perturb, or no user root for the
/// `userlocal` marker to bring in).
#[cfg(unix)]
fn perturb(rng: &mut SplitMix64, layout: &mut Layout, probe: Probe, odd: Odd) -> Option<PathBuf> {
    let manifest_trees: Vec<PathBuf> = std::iter::once(layout.dotnet_root.join("sdk-manifests"))
        .chain(layout.user_root.iter().map(|u| u.join("sdk-manifests")))
        .collect();
    let manifests: Vec<PathBuf> = manifest_trees
        .iter()
        .flat_map(|tree| files_named(tree, "WorkloadManifest.json"))
        .collect();
    if matches!(probe, Probe::Targets | Probe::ManifestJson) && manifests.is_empty() {
        return None;
    }
    let (band, release) = layout.host.bands();
    let workloads = layout.dotnet_root.join("metadata").join("workloads");
    let sdk_dir = layout.dotnet_root.join("sdk").join(&layout.host.version);
    let (path, content) = match probe {
        Probe::Targets => (
            rng.pick(&manifests)
                .with_file_name("WorkloadManifest.targets"),
            "<Project />".to_owned(),
        ),
        Probe::ManifestJson => (rng.pick(&manifests).clone(), MANIFEST_JSON.to_owned()),
        Probe::UserLocal => {
            layout.user_root.as_ref()?;
            (workloads.join(&release).join("userlocal"), String::new())
        }
        Probe::Msi => (
            workloads.join(&release).join("installertype").join("msi"),
            String::new(),
        ),
        Probe::InstallState => (
            workloads
                .join(process_architecture())
                .join(&band)
                .join("InstallState")
                .join("default.json"),
            "{}".to_owned(),
        ),
        Probe::KnownList => {
            let path = sdk_dir.join("KnownWorkloadManifests.txt");
            let content = host_fs::read_to_string(&path).unwrap_or_default();
            (path, content)
        }
        Probe::RidChain => (sdk_dir.join(RID_CHAIN), RID_CHAIN_CONTENT.to_owned()),
        Probe::Entry => {
            // A band directory's entry is named as a manifest id, an id
            // directory's as a manifest version.
            let mut parents: Vec<(PathBuf, &str)> = Vec::new();
            for tree in &manifest_trees {
                for band_dir in subdirectories(tree) {
                    for id_dir in subdirectories(&band_dir) {
                        parents.push((id_dir, "3.0.0"));
                    }
                    parents.push((band_dir, "contoso.entry"));
                }
            }
            if parents.is_empty() {
                return None;
            }
            let (parent, name) = rng.pick(&parents);
            (parent.join(name), String::new())
        }
    };
    let aside = layout._dir.path().join("aside");
    odd_entry::place(odd, &path, &content, &aside);
    if probe.declines_on_purpose(odd) {
        layout.in_domain = false;
    }
    let shown = path.strip_prefix(layout._dir.path()).unwrap_or(&path);
    layout
        .description
        .push_str(&format!("{odd:?} at {}\n", shown.display()));
    Some(path)
}

/// Every probe the resolver makes, with every shape it can meet there, on
/// generated layouts: where the resolver's `File.Exists` and the operating
/// system's `stat` part (a dangling link or a socket is a file to the one and
/// not the other), we must answer as the resolver does or decline.
///
/// Each shape is graded on layouts until the resolver has answered on two in
/// the domain we must resolve (where every answer of ours is a commit the
/// resolver grades), unless no answer is to be had: a shape we decline on
/// purpose, or one whose read throws in the resolver.
#[cfg(unix)]
#[test]
fn the_workload_probes_answer_as_the_resolver_s() {
    const MIN_LAYOUTS: usize = 4;
    const MIN_ANSWERS: usize = 2;
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(0x0dd_e417);
        for &probe in Probe::ALL {
            for &odd in probe.shapes() {
                let unanswerable = probe.declines_on_purpose(odd) || probe.resolver_throws(odd);
                let (mut graded, mut committed, mut answered, mut attempts) = (0, 0, 0, 0);
                while graded < MIN_LAYOUTS || (answered < MIN_ANSWERS && !unanswerable) {
                    attempts += 1;
                    assert!(
                        attempts < 400,
                        "{}: {probe:?} as {odd:?}: {graded} layouts took the probe, and the \
                         resolver answered on {answered} in the domain",
                        sdk.display()
                    );
                    let mut layout = gen_layout(&mut rng, true);
                    let Some(placed) = perturb(&mut rng, &mut layout, probe, odd) else {
                        continue;
                    };
                    // The walk would read a special targets file MSBuild
                    // imports, and a read of a FIFO never returns, so no
                    // committed root may hold one.
                    if matches!(probe, Probe::Targets)
                        && matches!(odd, Odd::Socket | Odd::Fifo)
                        && ours(&layout, WORKLOAD_MANIFEST_TARGETS_LOCATOR).is_some_and(|roots| {
                            roots
                                .iter()
                                .any(|root| Path::new(root) == placed.parent().unwrap())
                        })
                    {
                        failures.push(format!(
                            "{}, {probe:?} as {odd:?}: we commit a root whose targets file is \
                             a special file\n{}",
                            sdk.display(),
                            layout.description
                        ));
                    }
                    graded += 1;
                    let (here, theirs, failure) = grade(&mut oracle, &layout);
                    committed += here;
                    answered += theirs;
                    if let Some(failure) = failure
                        && failures.len() < 8
                    {
                        failures.push(format!(
                            "{}, {probe:?} as {odd:?}: {failure}\n{}",
                            sdk.display(),
                            layout.description
                        ));
                    }
                }
                println!(
                    "{}: {probe:?} as {odd:?}: committed {committed} of {} answers; the resolver \
                     answered {answered} in the domain",
                    sdk.display(),
                    graded * 2
                );
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// ---------------------------------------------------------------------------
// What the resolver reads in a manifest and in the known list.

/// A manifest document, written over a resolved manifest of a plain layout,
/// and whether the resolver loads it.
#[derive(Clone, Copy, Debug)]
enum Content {
    /// The resolver loads it, and we must answer as it does.
    Loads(&'static str, &'static str),
    /// The resolver throws reading or composing it, and we must decline.
    Throws(&'static str, &'static str),
    /// The resolver loads it, and we decline on purpose: outside the strict
    /// reader (a comment, a trailing comma, input after the object) or the
    /// certified spellings (an integer version).
    Declined(&'static str, &'static str),
    /// Outside what we certify, and read differently by the installed
    /// resolvers (a later one validates what an earlier one let through), so
    /// we decline on purpose and hold no resolver to either outcome.
    Unsettled(&'static str, &'static str),
}

/// `{own}` stands for the manifest's own id, `{w}` for a workload id and
/// `{p}` for a pack id unique to the layout.
const CONTENTS: &[Content] = &[
    Content::Loads("plain", r#"{"version": "1.0.0"}"#),
    Content::Loads(
        "every top-level key",
        r#"{"version": "1.0.0", "description": "d", "depends-on": {}, "workloads": {}, "packs": {}, "data": {"x": [1, {"y": null}]}}"#,
    ),
    Content::Loads(
        "keys in another case",
        r#"{"Version": "1.0.0", "WORKLOADS": {}, "Packs": {}}"#,
    ),
    Content::Loads(
        "a pack",
        r#"{"version": "1.0.0", "packs": {"{p}": {"version": "1.2.3", "kind": "Sdk"}}}"#,
    ),
    Content::Loads(
        "an aliased pack",
        r#"{"version": "1.0.0", "packs": {"{p}": {"version": "1.2.3", "kind": "framework", "alias-to": {"linux-x64": "{p}.Linux", "any": "{p}.Any"}}}}"#,
    ),
    Content::Loads(
        "workloads",
        r#"{"version": "1.0.0", "workloads": {"{w}": {"description": "W", "kind": "dev", "packs": ["{p}"], "extends": ["{w}-base"], "platforms": ["linux-x64"]}, "{w}-base": {"abstract": true}, "{w}-build": {"kind": "build"}}, "packs": {"{p}": {"version": "1.0.0", "kind": "library"}}}"#,
    ),
    Content::Loads(
        "a met dependency",
        r#"{"version": "1.0.0", "depends-on": {"{own}": "1.0.0"}}"#,
    ),
    Content::Throws("an unknown key", r#"{"version": "1.0.0", "frobnicate": 1}"#),
    Content::Throws("no version", r#"{"description": "d"}"#),
    Content::Throws("a malformed version", r#"{"version": "abc"}"#),
    Content::Throws("a key twice", r#"{"version": "1.0.0", "Version": "1.0.1"}"#),
    Content::Throws(
        "a pack without a kind",
        r#"{"version": "1.0.0", "packs": {"{p}": {"version": "1.0.0"}}}"#,
    ),
    Content::Throws(
        "a pack of an unknown kind",
        r#"{"version": "1.0.0", "packs": {"{p}": {"version": "1.0.0", "kind": "widget"}}}"#,
    ),
    Content::Throws(
        "a concrete dev workload without a description",
        r#"{"version": "1.0.0", "workloads": {"{w}": {"kind": "dev", "packs": []}}}"#,
    ),
    Content::Loads(
        "a workload of no kind without a description",
        r#"{"version": "1.0.0", "workloads": {"{w}": {"packs": []}}}"#,
    ),
    Content::Throws(
        "a workload redirect",
        r#"{"version": "1.0.0", "workloads": {"{w}": {"replace-with": "{w}-new"}}}"#,
    ),
    Content::Unsettled(
        "a workload id that is no path component",
        r#"{"version": "1.0.0", "workloads": {"a/b": {"abstract": true}}}"#,
    ),
    Content::Throws(
        "a missing dependency",
        r#"{"version": "1.0.0", "depends-on": {"contoso.nowhere": "1.0.0"}}"#,
    ),
    Content::Throws(
        "an unmet dependency",
        r#"{"version": "1.0.0", "depends-on": {"{own}": "9.0.0"}}"#,
    ),
    Content::Throws("not JSON", r#"{"version": "#),
    Content::Throws("an array", "[]"),
    Content::Declined("an integer version", r#"{"version": 1}"#),
    Content::Declined("a comment", r#"{"version": "1.0.0" /* c */}"#),
    Content::Loads("trailing commas", r#"{"version": "1.0.0",}"#),
    Content::Declined("input after the object", r#"{"version": "1.0.0"} x"#),
];

impl Content {
    fn text(self) -> (&'static str, &'static str) {
        match self {
            Content::Loads(n, t)
            | Content::Throws(n, t)
            | Content::Declined(n, t)
            | Content::Unsettled(n, t) => (n, t),
        }
    }
}

/// A localization catalog written beside a manifest: its file name and text.
type Catalog = (&'static str, &'static str);

/// The manifest id a `WorkloadManifest.json` under a manifest tree is named
/// by: the directory just below its band directory.
fn manifest_id(tree: &Path, manifest: &Path) -> String {
    let relative = manifest
        .strip_prefix(tree)
        .expect("the manifest is in the tree");
    let mut components = relative.components();
    components.next();
    components
        .next()
        .expect("a manifest sits below an id directory")
        .as_os_str()
        .to_string_lossy()
        .into_owned()
}

/// Every resolved-manifest content the reader and the composition can meet,
/// written over one manifest of a plain layout (and, for a catalog case, with
/// localization catalogs beside it): where the resolver throws, the
/// auto-import locator must decline, and where it loads, both locators must
/// answer as it does.
#[test]
fn workload_manifests_load_as_the_resolver_reads_them() {
    let mut cases: Vec<(String, Content, Option<Catalog>)> = CONTENTS
        .iter()
        .map(|&content| (content.text().0.to_owned(), content, None))
        .collect();
    let workloads = *CONTENTS
        .iter()
        .find(|content| content.text().0 == "workloads")
        .expect("a workloads case");
    cases.push((
        "a localized description".to_owned(),
        workloads,
        Some((
            "WorkloadManifest.ja.json",
            r#"{"workloads/{w}/description": "ワ"}"#,
        )),
    ));
    // The resolver opens only the catalog the build process's UI culture
    // selects, and the oracle's selects none of these; we cannot see that
    // culture, so a catalog that would throw under some culture declines.
    cases.push((
        "a malformed catalog".to_owned(),
        Content::Declined("", workloads.text().1),
        Some(("WorkloadManifest.ja.json", "{")),
    ));
    cases.push((
        "a catalog that empties a description".to_owned(),
        Content::Declined("", workloads.text().1),
        Some((
            "WorkloadManifest.de.json",
            r#"{"workloads/{w}/description": ""}"#,
        )),
    ));
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(0x313_6d6e);
        for (name, content, catalog) in &cases {
            let (mut graded, mut auto_committed, mut auto_answered, mut auto_threw) = (0, 0, 0, 0);
            let mut attempts = 0;
            while graded < 6 {
                attempts += 1;
                assert!(attempts < 200, "{name}: no layout has a manifest");
                let mut layout = gen_layout(&mut rng, true);
                // A manifest of the host band, which the primary pass resolves.
                let tree = layout.dotnet_root.join("sdk-manifests");
                let manifests =
                    files_named(&tree.join(layout.host.bands().0), "WorkloadManifest.json");
                if manifests.is_empty() {
                    continue;
                }
                let target = rng.pick(&manifests).clone();
                let own = manifest_id(&tree, &target);
                let fill = |text: &str| {
                    text.replace("{own}", &own)
                        .replace("{w}", "contoso-workload")
                        .replace("{p}", "Contoso.Pack")
                };
                std::fs::write(&target, fill(content.text().1)).unwrap();
                if let Some((file, text)) = catalog {
                    write(&target.with_file_name("localize").join(file), &fill(text));
                }
                if matches!(content, Content::Declined(..) | Content::Unsettled(..)) {
                    layout.in_domain = false;
                }
                layout.description.push_str(&format!(
                    "{name} in {}\n",
                    target.strip_prefix(&layout.dotnet_root).unwrap().display()
                ));
                graded += 1;
                let (_, _, failure) = grade(&mut oracle, &layout);
                if let Some(failure) = failure
                    && failures.len() < 8
                {
                    failures.push(format!(
                        "{}, {name}: {failure}\n{}",
                        sdk.display(),
                        layout.description
                    ));
                }
                let ours = ours(&layout, WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR);
                let theirs = theirs(&mut oracle, &layout, WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR);
                auto_committed += usize::from(ours.is_some());
                auto_answered += usize::from(theirs.is_ok());
                auto_threw += usize::from(theirs.is_err());
            }
            println!(
                "{}: {name}: auto-import committed {auto_committed}, the resolver answered \
                 {auto_answered} and threw {auto_threw} of {graded}",
                sdk.display()
            );
            // Each case must reach what it is about: a loading manifest a
            // commit, a throwing one a throw.
            match content {
                Content::Loads(..) => assert!(
                    auto_committed > 0,
                    "{}: {name}: the auto-import locator never committed",
                    sdk.display()
                ),
                Content::Throws(..) => assert!(
                    auto_threw > 0,
                    "{}: {name}: the resolver never threw",
                    sdk.display()
                ),
                Content::Declined(..) => assert!(
                    auto_answered > 0,
                    "{}: {name}: the resolver never answered",
                    sdk.display()
                ),
                Content::Unsettled(..) => {}
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// A known list's spelling, which `File.ReadAllLines` reads line by line,
/// keeping every non-empty line untrimmed.
#[derive(Clone, Copy, Debug)]
enum KnownSpelling {
    /// One id per `\n` line.
    Plain,
    /// `\r\n` line ends.
    Crlf,
    /// Lone `\r` line ends.
    LoneCr,
    /// Blank lines between the ids.
    Blank,
    /// A leading UTF-8 BOM.
    Bom,
    /// The first id repeated at the end.
    Repeated,
    /// The ids in another case than their directories.
    OtherCase,
    /// A space before each id, which the resolver keeps.
    Padded,
    /// A line of spaces.
    Spaces,
    /// One id spelled in two cases.
    TwoSpellings,
}

impl KnownSpelling {
    const ALL: &[KnownSpelling] = &[
        KnownSpelling::Plain,
        KnownSpelling::Crlf,
        KnownSpelling::LoneCr,
        KnownSpelling::Blank,
        KnownSpelling::Bom,
        KnownSpelling::Repeated,
        KnownSpelling::OtherCase,
        KnownSpelling::Padded,
        KnownSpelling::Spaces,
        KnownSpelling::TwoSpellings,
    ];

    /// Whether we decline on purpose: an id the fallback would look up that
    /// is no plain path component (a padded or blank one), and one id spelled
    /// two ways, whose outcome hangs on dictionary order.
    fn declines_on_purpose(self) -> bool {
        matches!(
            self,
            KnownSpelling::Padded | KnownSpelling::Spaces | KnownSpelling::TwoSpellings
        )
    }

    fn spell(self, ids: &[&str]) -> String {
        let upper = |id: &str| -> String {
            id.split('.')
                .map(|part| {
                    let mut chars = part.chars();
                    chars
                        .next()
                        .map(|c| c.to_ascii_uppercase().to_string() + chars.as_str())
                        .unwrap_or_default()
                })
                .collect::<Vec<_>>()
                .join(".")
        };
        match self {
            KnownSpelling::Plain => ids.join("\n"),
            KnownSpelling::Crlf => ids.join("\r\n") + "\r\n",
            KnownSpelling::LoneCr => ids.join("\r"),
            KnownSpelling::Blank => ids.join("\n\n") + "\n",
            KnownSpelling::Bom => format!("\u{feff}{}", ids.join("\n")),
            KnownSpelling::Repeated => {
                let mut lines: Vec<&str> = ids.to_vec();
                lines.extend(ids.first());
                lines.join("\n")
            }
            KnownSpelling::OtherCase => ids
                .iter()
                .map(|id| upper(id))
                .collect::<Vec<_>>()
                .join("\n"),
            KnownSpelling::Padded => ids
                .iter()
                .map(|id| format!(" {id}"))
                .collect::<Vec<_>>()
                .join("\n"),
            KnownSpelling::Spaces => format!("{}\n   \n", ids.join("\n")),
            KnownSpelling::TwoSpellings => {
                let mut lines: Vec<String> = ids.iter().map(|id| id.to_string()).collect();
                lines.extend(ids.first().map(|id| upper(id)));
                lines.join("\n")
            }
        }
    }
}

/// Every spelling of a known list `File.ReadAllLines` reads differently from
/// a line-trimming reader, over plain layouts: the targets locator's order
/// and fallback must be the resolver's, or we decline.
#[test]
fn the_known_list_is_read_as_the_resolver_reads_it() {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(0x6b6e_6f77);
        for &spelling in KnownSpelling::ALL {
            let mut committed = 0;
            for _ in 0..8 {
                let mut layout = gen_layout(&mut rng, true);
                let mut ids: Vec<&str> =
                    IDS.iter().copied().filter(|_| rng.below(3) != 0).collect();
                ids.push(UNLISTED_ID);
                for i in (1..ids.len()).rev() {
                    ids.swap(i, rng.below(i + 1));
                }
                let path = layout
                    .dotnet_root
                    .join("sdk")
                    .join(&layout.host.version)
                    .join("KnownWorkloadManifests.txt");
                std::fs::write(&path, spelling.spell(&ids)).unwrap();
                if spelling.declines_on_purpose() {
                    layout.in_domain = false;
                }
                layout
                    .description
                    .push_str(&format!("known list {spelling:?} of {ids:?}\n"));
                let (here, _, failure) = grade(&mut oracle, &layout);
                committed += here;
                if let Some(failure) = failure
                    && failures.len() < 8
                {
                    failures.push(format!(
                        "{}, {spelling:?}: {failure}\n{}",
                        sdk.display(),
                        layout.description
                    ));
                }
            }
            println!(
                "{}: {spelling:?}: committed {committed} of 16 answers",
                sdk.display()
            );
            assert!(
                committed > 0 || spelling.declines_on_purpose(),
                "{}: {spelling:?}: the sweep committed nothing",
                sdk.display()
            );
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// Prerelease spellings a `depends-on` compares: the orders `FXVersion.Compare`
/// takes from the first differing character rather than whole identifiers.
const FX_VERSIONS: &[&str] = &[
    "1.0.0",
    "1.0.1",
    "1.0.0-rc",
    "1.0.0-rc.1",
    "1.0.0-rc.2",
    "1.0.0-rc.10",
    "1.0.0-rc.1.2",
    "1.0.0-rc.a",
    "1.0.0-rc-1",
    "1.0.0-preview.9",
    "1.0.0-a",
    "1.0.0-a-b",
    "1.0.0-a.b",
    "1.0.0-1",
    "1.0.0-10",
    "1.0.0-x.-1",
    "1.0.0-x.-10",
];

/// A manifest that depends on itself at another version: the auto-import
/// locator loads it exactly where the resolver's `FXVersion.Compare` puts the
/// needed version at or below its own, over every pair of [`FX_VERSIONS`].
#[test]
fn a_dependency_s_versions_compare_as_the_resolver_compares_them() {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let (mut met, mut unmet) = (0, 0);
        for own in FX_VERSIONS {
            for needed in FX_VERSIONS {
                let dir = tempfile::TempDir::new().unwrap();
                let dotnet_root = host_fs::canonicalize(dir.path()).unwrap().join("dotnet");
                std::fs::create_dir_all(dotnet_root.join("sdk/10.0.100")).unwrap();
                write(
                    &dotnet_root.join("sdk-manifests/10.0.100/contoso.one/WorkloadManifest.json"),
                    &format!(
                        r#"{{"version": "{own}", "depends-on": {{"contoso.one": "{needed}"}}}}"#
                    ),
                );
                let layout = Layout {
                    _dir: dir,
                    dotnet_root,
                    user_root: None,
                    host: Host {
                        version: "10.0.100".to_owned(),
                        major: 10,
                        minor: 0,
                        hundreds: 1,
                        pre: None,
                    },
                    in_domain: true,
                    description: format!("contoso.one {own} depends on itself at {needed}\n"),
                };
                let ours = ours(&layout, WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR);
                let theirs = theirs(&mut oracle, &layout, WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR);
                if theirs.is_ok() {
                    met += 1;
                } else {
                    unmet += 1;
                }
                if ours.is_some() != theirs.is_ok() && failures.len() < 8 {
                    failures.push(format!(
                        "{}: {}we answer {ours:?}, the resolver {theirs:?}",
                        sdk.display(),
                        layout.description
                    ));
                }
            }
        }
        println!("{}: {met} met, {unmet} unmet", sdk.display());
        assert!(
            met > 0 && unmet > 0,
            "{}: the sweep graded one side only",
            sdk.display()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// ---------------------------------------------------------------------------
// Which manifest version directory wins.

/// Manifest version directory names: release cores of two, three and four
/// components, spellings `System.Version` reads as one value (leading zeros),
/// prereleases whose identifiers `ReleaseVersion` compares numerically, by
/// length, ordinally and by count (and whose first carries the `-`), and names
/// either parser refuses.
const VERSION_DIRECTORY_NAMES: &[&str] = &[
    "1.0.0",
    "1.0.1",
    "1.0.10",
    "1.0.9",
    "2.0.0",
    "1.0",
    "1.0.0.0",
    "1.0.0.1",
    "01.0.0",
    "1.00.0",
    "1",
    "1.0.0-rc.1",
    "1.0.0-rc.2",
    "1.0.0-rc.10",
    "1.0.0-rc.01",
    "1.0.0-preview.1",
    "1.0.0-1",
    "1.0.0-10",
    "1.0.0-9",
    "1.0.0-a",
    "1.0.0-A",
    "1.0.0-rc.1.2",
    "1.0.0-rc",
    "1.0.0-rc.a",
    "1.0.0--1",
    "1.0.0-",
    "1.0.0-net11-p6",
    "01.0.0-rc.1",
    "1.0.0.0-rc.1",
    "1.0-rc.1",
    "11.0.100-rc.1.26425.128",
    "1.0.0-rc+x",
    "1.0.0+x",
    "1.0.0-rc..1",
    "1.0.0-rc_1",
    "foo",
    "-1",
    "1.0.0.0.0",
    "2147483648.0.0",
    " 1.0.0",
];

/// Every name alone, every pair and a fixed sample of triples of
/// [`VERSION_DIRECTORY_NAMES`] as the version directories of one manifest,
/// each with its targets: the targets locator's answer, ours against the
/// resolver's, certain-implies-exact. We must commit for a lone name (the
/// resolver compares nothing), and for names [`test_support`] certifies of
/// which no two tie at the top.
#[test]
fn the_highest_manifest_version_directory_is_the_resolver_s() {
    let mut sets: Vec<Vec<&str>> = VERSION_DIRECTORY_NAMES.iter().map(|n| vec![*n]).collect();
    for (i, a) in VERSION_DIRECTORY_NAMES.iter().enumerate() {
        for b in &VERSION_DIRECTORY_NAMES[i + 1..] {
            sets.push(vec![a, b]);
        }
    }
    let mut rng = SplitMix64(0x0918_7e75);
    for _ in 0..300 {
        let mut set: Vec<&str> = (0..3).map(|_| *rng.pick(VERSION_DIRECTORY_NAMES)).collect();
        set.sort_unstable();
        set.dedup();
        sets.push(set);
    }
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let tmp = tempfile::TempDir::new().unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        let host = "10.0.100";
        let mut committed = 0;
        for (case, set) in sets.iter().enumerate() {
            let dotnet = root.join(format!("c{case}"));
            let sdk_dir = dotnet.join("sdk").join(host);
            std::fs::create_dir_all(&sdk_dir).unwrap();
            let id_dir = dotnet.join("sdk-manifests").join(host).join("contoso.one");
            for name in set {
                write(
                    &id_dir.join(name).join("WorkloadManifest.json"),
                    MANIFEST_JSON,
                );
                write(
                    &id_dir.join(name).join("WorkloadManifest.targets"),
                    "<Project />",
                );
            }
            let env = WorkloadEnvironment {
                user_dotnet_root: None,
                overrides_present: false,
                resolver_switched_off: false,
                global_json: Default::default(),
                process_architecture: None,
            };
            let ours = match resolve_workload_locator(
                WORKLOAD_MANIFEST_TARGETS_LOCATOR,
                &dotnet,
                &sdk_dir,
                &env,
                &Observer::new(),
            ) {
                Ok(SdkResolution::Roots(roots)) => Some(
                    roots
                        .iter()
                        .map(|p| p.to_string_lossy().into_owned())
                        .collect::<Vec<_>>(),
                ),
                Ok(other) => panic!("a locator resolves to roots, not {other:?}"),
                Err(_) => None,
            };
            let response = oracle.request(&json!({
                "op": "resolve",
                "sdk": WORKLOAD_MANIFEST_TARGETS_LOCATOR,
                "dotnetRoot": dotnet.to_string_lossy(),
                "sdkVersion": host,
                "userProfileDir": null,
            }));
            let theirs = (response["ok"] == json!(true)).then(|| {
                response["paths"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|p| p.as_str().unwrap().to_owned())
                    .collect::<Vec<_>>()
            });
            let must =
                set.len() == 1 || test_support::workload_manifest_versions_are_told_apart(set);
            match (&ours, &theirs) {
                (Some(ours), Some(theirs)) if ours == theirs => committed += 1,
                (Some(ours), _) => failures.push(format!(
                    "{}: {set:?}: we pick {ours:?}, the resolver answers {response}",
                    sdk.display()
                )),
                (None, Some(theirs)) if must => failures.push(format!(
                    "{}: {set:?}: we decline, the resolver picks {theirs:?}",
                    sdk.display()
                )),
                (None, _) => {}
            }
        }
        println!("{}: committed {committed} of {}", sdk.display(), sets.len());
        assert!(
            committed >= sets.len() / 3,
            "{}: {committed}",
            sdk.display()
        );
    }
    assert!(
        failures.is_empty(),
        "{}",
        failures[..failures.len().min(20)].join("\n")
    );
}

// ---------------------------------------------------------------------------
// Workload sets, the install state and global.json.

/// A generated layout of the workload-set family: manifests of two ids at
/// several versions in the host band (and one in an older band); workload
/// sets of the host band, of other bands and of the 8.0.100 baseline band,
/// naming installed manifests, missing ones, ids in other casings and other
/// bands; an install state under the oracle's architecture or another's,
/// with `useWorkloadSets`, a `workloadVersion` and `manifests`; and a
/// `global.json` with `workloadVersion` and `workloads-update-mode` in
/// either casing. `in_domain` is false where something was generated that
/// we do not certify (a malformed file, a non-object `sdk`).
struct SetLayout {
    _dir: tempfile::TempDir,
    dotnet_root: PathBuf,
    global_json: Option<PathBuf>,
    in_domain: bool,
    description: String,
}

const HOST: &str = "10.0.100";

fn gen_set_layout(rng: &mut SplitMix64, architecture: &str) -> SetLayout {
    let dir = tempfile::TempDir::new().unwrap();
    let root = host_fs::canonicalize(dir.path()).unwrap();
    let dotnet_root = root.join("dotnet");
    std::fs::create_dir_all(dotnet_root.join("sdk").join(HOST)).unwrap();
    let mut description = String::new();
    let mut in_domain = true;
    for id in ["contoso.one", "contoso.two"] {
        for version in ["1.0.0", "2.0.0", "3.0.0"] {
            if rng.below(3) == 0 {
                continue;
            }
            let dir = dotnet_root
                .join("sdk-manifests")
                .join(HOST)
                .join(id)
                .join(version);
            write(&dir.join("WorkloadManifest.json"), MANIFEST_JSON);
            if rng.below(4) != 0 {
                write(&dir.join("WorkloadManifest.targets"), "<Project />");
            }
            description.push_str(&format!("manifest {id} {version}\n"));
        }
    }
    let older = dotnet_root.join("sdk-manifests/9.0.100/contoso.three/1.0.0");
    write(&older.join("WorkloadManifest.json"), MANIFEST_JSON);
    write(&older.join("WorkloadManifest.targets"), "<Project />");

    let set_body = |rng: &mut SplitMix64, in_domain: &mut bool| -> String {
        if rng.below(12) == 0 {
            *in_domain = false;
            return "{".to_owned();
        }
        let mut entries = Vec::new();
        for id in ["contoso.one", "Contoso.Two", "contoso.three"] {
            if rng.below(2) == 0 {
                continue;
            }
            let value = match (id, rng.below(4)) {
                ("contoso.three", _) => "1.0.0/9.0.105".to_owned(),
                (_, 0) => "9.9.9".to_owned(),
                (_, n) => format!("{n}.0.0"),
            };
            entries.push(format!("\"{id}\": \"{value}\""));
        }
        format!("{{{}}}", entries.join(", "))
    };
    const SET_VERSIONS: &[&str] = &["10.0.100", "10.0.101", "10.0.100.1", "10.0.200"];
    let mut set_versions = Vec::new();
    for version in SET_VERSIONS {
        if rng.below(3) != 0 {
            continue;
        }
        let band = if *version == "10.0.200" {
            "10.0.200"
        } else {
            HOST
        };
        let body = set_body(rng, &mut in_domain);
        write(
            &dotnet_root
                .join("sdk-manifests")
                .join(band)
                .join("workloadsets")
                .join(version)
                .join("x.workloadset.json"),
            &body,
        );
        description.push_str(&format!("set {band}/{version}: {body}\n"));
        set_versions.push(*version);
    }
    if rng.below(3) == 0 {
        let body = set_body(rng, &mut in_domain);
        write(
            &dotnet_root.join("sdk-manifests/8.0.100/workloadsets/8.0.100/x.workloadset.json"),
            &body,
        );
        description.push_str(&format!("baseline set 8.0.100: {body}\n"));
        set_versions.push("8.0.100");
    }
    let pick_version = |rng: &mut SplitMix64| -> String {
        match rng.below(4) {
            0 => "10.0.105".to_owned(),
            _ if !set_versions.is_empty() => (*rng.pick(&set_versions)).to_owned(),
            _ => "10.0.100".to_owned(),
        }
    };

    if rng.below(2) == 0 {
        let arch = if rng.below(5) == 0 {
            "Arm64"
        } else {
            architecture
        };
        let mut members = Vec::new();
        if rng.below(2) == 0 {
            members.push(format!("\"useWorkloadSets\": {}", rng.below(2) == 0));
        }
        if rng.below(3) == 0 {
            members.push(format!("\"workloadVersion\": \"{}\"", pick_version(rng)));
        }
        if rng.below(3) == 0 {
            members.push(format!(
                "\"manifests\": {{\"contoso.one\": \"{}.0.0\"}}",
                1 + rng.below(3)
            ));
        }
        let mut body = format!("{{{}}}", members.join(", "));
        if rng.below(10) == 0 {
            body = format!("{{/* c */{}", &body[1..]);
            in_domain = false;
        }
        write(
            &dotnet_root
                .join("metadata/workloads")
                .join(arch)
                .join(HOST)
                .join("InstallState/default.json"),
            &body,
        );
        description.push_str(&format!("install state ({arch}): {body}\n"));
    }

    let global_json = (rng.below(2) == 0).then(|| {
        let path = root.join("global.json");
        let (sdk, version, mode) = match rng.below(3) {
            0 => ("sdk", "workloadVersion", "workloads-update-mode"),
            1 => ("SDK", "WorkloadVersion", "Workloads-Update-Mode"),
            _ => ("sdk", "workloadversion", "workloads-update-mode"),
        };
        let mut members = Vec::new();
        if rng.below(2) == 0 {
            members.push(format!("\"{version}\": \"{}\"", pick_version(rng)));
        }
        if rng.below(2) == 0 {
            let value = *rng.pick(&["manifests", "workload-set", "Manifests", "other"]);
            members.push(format!("\"{mode}\": \"{value}\""));
        }
        let body = match rng.below(12) {
            0 => {
                in_domain = false;
                format!("{{\"{sdk}\": null}}")
            }
            // A form feed, which the host-side parse skips and the workload
            // reader throws on.
            1 => {
                in_domain = false;
                format!("{{\u{c}\"{sdk}\": {{{}}}}}", members.join(", "))
            }
            _ => format!("{{\"{sdk}\": {{{}}}}}", members.join(", ")),
        };
        write(&path, &body);
        description.push_str(&format!("global.json: {body}\n"));
        path
    });
    SetLayout {
        _dir: dir,
        dotnet_root,
        global_json,
        in_domain,
        description,
    }
}

/// Both locators over generated [`SetLayout`]s, ours against each installed
/// resolver's, certain-implies-exact; where nothing outside the certified
/// subset was generated and the resolver answers, we must answer too.
#[test]
fn workload_sets_and_the_install_state_are_applied_as_the_resolver_applies_them() {
    sweep_sets(0x0818_5e75, 300);
}

/// The fresh-seed twin; `BORZOI_MSBUILD_SOAK_SEED` reproduces a run.
#[test]
#[ignore = "soak: run with --ignored; BORZOI_MSBUILD_SOAK_SEED reproduces"]
fn soak_workload_sets_and_the_install_state() {
    let (seed, cases) = common::soak_parameters("workload_sets", 2000);
    sweep_sets(seed, cases);
}

fn sweep_sets(seed: u64, cases: usize) {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let architecture = oracle.request(&json!({"op": "identity"}))["processArchitecture"]
            .as_str()
            .expect("the oracle names its architecture")
            .to_owned();
        let mut rng = SplitMix64(seed);
        let (mut committed, mut answered) = (0, 0);
        for case in 0..cases {
            let layout = gen_set_layout(&mut rng, &architecture);
            let global_json = layout.global_json.as_ref().map(|path| {
                borzoi_msbuild::parse_global_json(&host_fs::read_to_string(path).unwrap())
                    .expect("the generated global.json parses")
                    .workloads
            });
            for locator in [
                WORKLOAD_MANIFEST_TARGETS_LOCATOR,
                WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
            ] {
                let env = WorkloadEnvironment {
                    user_dotnet_root: None,
                    overrides_present: false,
                    resolver_switched_off: false,
                    global_json: global_json.clone().unwrap_or_default(),
                    process_architecture: Some(
                        ProcessArchitecture::from_name(&architecture)
                            .expect("the oracle names an Architecture member"),
                    ),
                };
                let sdk_dir = layout.dotnet_root.join("sdk").join(HOST);
                let ours = match resolve_workload_locator(
                    locator,
                    &layout.dotnet_root,
                    &sdk_dir,
                    &env,
                    &Observer::new(),
                ) {
                    Ok(SdkResolution::Roots(roots)) => Some(
                        roots
                            .iter()
                            .map(|p| p.to_string_lossy().into_owned())
                            .collect::<Vec<_>>(),
                    ),
                    Ok(other) => panic!("a locator resolves to roots, not {other:?}"),
                    Err(_) => None,
                };
                let response = oracle.request(&json!({
                    "op": "resolve",
                    "sdk": locator,
                    "dotnetRoot": layout.dotnet_root.to_string_lossy(),
                    "sdkVersion": HOST,
                    "userProfileDir": null,
                    "globalJsonPath": layout.global_json.as_ref().map(|p| p.to_string_lossy()),
                }));
                let theirs = (response["ok"] == json!(true)).then(|| {
                    response["paths"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|p| p.as_str().unwrap().to_owned())
                        .collect::<Vec<_>>()
                });
                if theirs.is_some() && layout.in_domain {
                    answered += 1;
                }
                let failure = match (&ours, &theirs) {
                    (Some(ours), Some(theirs)) if ours == theirs => {
                        committed += 1;
                        None
                    }
                    (Some(ours), _) => {
                        Some(format!("we commit {ours:#?}, the resolver: {response}"))
                    }
                    (None, Some(theirs)) if layout.in_domain => {
                        Some(format!("we decline, the resolver says {theirs:#?}"))
                    }
                    (None, _) => None,
                };
                if let Some(failure) = failure
                    && failures.len() < 8
                {
                    failures.push(format!(
                        "{} case {case}, {locator}: {failure}\n{}",
                        sdk.display(),
                        layout.description
                    ));
                }
            }
        }
        println!(
            "{}: committed {committed}, the resolver answered {answered} in the domain, of {}",
            sdk.display(),
            cases * 2
        );
        assert!(committed >= cases / 2, "{}: {committed}", sdk.display());
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// ---------------------------------------------------------------------------
// The installed SDK packs the auto-import locator returns.

/// Runtime identifier chains the host SDK directory may hold, as text: the
/// resolver reads the file with `File.ReadAllLines` and keeps every non-empty
/// line, untrimmed. `None` is no file, which leaves no alias resolvable.
#[cfg(unix)]
const PACK_RID_CHAINS: &[Option<&str>] = &[
    None,
    Some("linux-x64\nlinux\nunix\nany\nbase\n"),
    Some("osx-arm64\r\nosx\r\nunix-arm64\r\nunix\r\nany\r\nbase"),
    Some("\u{feff}linux-x64\nany\n"),
    Some("\n\nunix\n\nlinux-x64\n"),
    Some("linux-x64 \rany"),
];

/// The keys an `alias-to` map draws from: runtime identifiers of the chains
/// above, one in another case and one with a trailing space (the lookup is
/// ordinal), and one no chain lists.
#[cfg(unix)]
const ALIAS_KEYS: &[&str] = &[
    "linux-x64",
    "Linux-X64",
    "linux-x64 ",
    "osx-arm64",
    "unix",
    "any",
    "win-x64",
];

/// A pack's `version`, and whether it is a plain path component, which we
/// certify; the resolver joins the rest into a pack path that is not one.
/// The certified ones come first.
#[cfg(unix)]
const PACK_VERSIONS: &[(&str, bool)] = &[
    ("1.0.0", true),
    ("10.0.0-rc.1.25451.107", true),
    ("35.0.7", true),
    ("1.0.0+meta", true),
    ("", false),
    ("..", false),
    ("a/b", false),
];

/// What sits at a pack's path under one pack root.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
enum PackEntry {
    /// A directory, holding `Sdk/AutoImport.props` as the [`PropsEntry`]
    /// says, or no such file (`None`).
    Installed(Option<PropsEntry>),
    /// An odd entry in place of the directory: `Directory.Exists` alone is
    /// asked of it.
    Odd(Odd),
}

/// What sits at `Sdk/AutoImport.props` in an installed pack.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
enum PropsEntry {
    File,
    /// `AutoImport.props` beside `Sdk` rather than in it, which the resolver
    /// does not look for.
    Beside,
    Odd(Odd),
}

/// A generated layout of manifests declaring packs: their kinds, versions,
/// `alias-to` maps (some packs aliasing one target, which the resolver
/// returns once) and ids (some shared between manifests, which fails the
/// composition), the runtime identifier chain, and each pack id the
/// manifests can resolve to installed under the user root, the dotnet root,
/// both or neither, in the manifest's casing or another, with or without
/// `Sdk/AutoImport.props`, or with an odd entry in place of either.
#[cfg(unix)]
struct PackLayout {
    _dir: tempfile::TempDir,
    dotnet_root: PathBuf,
    user_root: Option<PathBuf>,
    /// How many SDK packs alias `any`, which the chain lists, to one shared
    /// target at one version, and nothing else.
    shared_sdk_aliases: usize,
    in_domain: bool,
    description: String,
}

#[cfg(unix)]
fn gen_pack_layout(rng: &mut SplitMix64) -> PackLayout {
    let dir = tempfile::TempDir::new().unwrap();
    let root = host_fs::canonicalize(dir.path()).unwrap();
    let dotnet_root = root.join("dotnet");
    let sdk_dir = dotnet_root.join("sdk").join(HOST);
    std::fs::create_dir_all(&sdk_dir).unwrap();
    let mut description = String::new();
    let mut in_domain = true;

    let chain = *rng.pick(PACK_RID_CHAINS);
    if let Some(chain) = chain {
        write(&sdk_dir.join(RID_CHAIN), chain);
    }
    description.push_str(&format!("runtime identifier chain {chain:?}\n"));

    const MANIFEST_IDS: &[&str] = &["contoso.one", "contoso.two", "contoso.three"];
    if rng.below(2) == 0 {
        let mut known: Vec<&str> = MANIFEST_IDS.to_vec();
        for i in (1..known.len()).rev() {
            known.swap(i, rng.below(i + 1));
        }
        write(
            &sdk_dir.join("KnownWorkloadManifests.txt"),
            &known.join("\n"),
        );
        description.push_str(&format!("known {known:?}\n"));
    }

    // Every (pack id, version) a manifest can resolve to, for installing.
    let mut targets: Vec<(String, String)> = Vec::new();
    let mut shared_sdk_aliases = 0;
    for (index, manifest_id) in MANIFEST_IDS.iter().enumerate() {
        if rng.below(4) == 0 {
            continue;
        }
        let mut packs = serde_json::Map::new();
        for k in 0..rng.below(4) {
            let id = match rng.below(10) {
                // In two manifests, the composition throws.
                0 => "Contoso.Shared.Sdk".to_owned(),
                _ => format!("Contoso.M{index}.Sdk{k}"),
            };
            let kind = *rng.pick(&[
                "Sdk",
                "Sdk",
                "Sdk",
                "sdk",
                "SDK",
                "Framework",
                "Library",
                "Template",
                "Tool",
            ]);
            let shape = rng.below(5);
            let (version, plain) = if shape == 4 {
                // One shared alias target at one version, so two such packs
                // name one path.
                PACK_VERSIONS[0]
            } else if rng.below(12) == 0 {
                *rng.pick(PACK_VERSIONS)
            } else {
                *rng.pick(&PACK_VERSIONS[..4])
            };
            if !plain {
                in_domain = false;
            }
            let mut pack = serde_json::Map::new();
            pack.insert("kind".to_owned(), json!(kind));
            pack.insert("version".to_owned(), json!(version));
            targets.push((id.clone(), version.to_owned()));
            match shape {
                0 | 1 => {}
                4 => {
                    pack.insert(
                        "alias-to".to_owned(),
                        json!({ "any": "Contoso.Aliased.Shared" }),
                    );
                    targets.push(("Contoso.Aliased.Shared".to_owned(), version.to_owned()));
                    shared_sdk_aliases += usize::from(kind.eq_ignore_ascii_case("sdk"));
                }
                2 => {
                    pack.insert("alias-to".to_owned(), json!({}));
                }
                _ => {
                    let mut aliases = serde_json::Map::new();
                    for _ in 0..1 + rng.below(3) {
                        let key = *rng.pick(ALIAS_KEYS);
                        let target = match rng.below(4) {
                            // Shared with another pack: the same path twice,
                            // which the resolver returns once.
                            0 => "Contoso.Aliased.Shared".to_owned(),
                            1 => format!("{id}.Any"),
                            _ => format!("{id}.{}", key.trim().replace('-', ".")),
                        };
                        targets.push((target.clone(), version.to_owned()));
                        aliases.insert(key.to_owned(), json!(target));
                    }
                    pack.insert("alias-to".to_owned(), serde_json::Value::Object(aliases));
                }
            }
            packs.insert(id, serde_json::Value::Object(pack));
        }
        let body = json!({ "version": "1.0.0", "packs": packs });
        let manifest_dir = dotnet_root
            .join("sdk-manifests")
            .join(HOST)
            .join(manifest_id)
            .join("1.0.0");
        write(
            &manifest_dir.join("WorkloadManifest.json"),
            &body.to_string(),
        );
        description.push_str(&format!("manifest {manifest_id}: {body}\n"));
    }

    // A user root, consulted for packs where the `userlocal` marker is
    // present.
    let user_root = (rng.below(3) == 0).then(|| {
        let user_root = root.join("user");
        std::fs::create_dir_all(&user_root).unwrap();
        if rng.below(4) != 0 {
            write(
                &dotnet_root
                    .join("metadata/workloads")
                    .join(HOST)
                    .join("userlocal"),
                "",
            );
            description.push_str("userlocal marker\n");
        }
        description.push_str("user root\n");
        user_root
    });

    targets.sort();
    targets.dedup();
    let aside = root.join("aside");
    let pack_roots: Vec<PathBuf> = user_root
        .iter()
        .cloned()
        .chain([dotnet_root.clone()])
        .collect();
    let mut placed = BTreeSet::new();
    for (id, version) in &targets {
        // An uncertified version names no directory of its own to install.
        if !PACK_VERSIONS[..4].iter().any(|(v, _)| v == version) {
            continue;
        }
        for pack_root in &pack_roots {
            if rng.below(3) == 0 {
                continue;
            }
            // The id in another casing, which a case-insensitive file system
            // finds under the manifest's spelling.
            let spelled = if rng.below(5) == 0 {
                id.to_ascii_lowercase()
            } else {
                id.clone()
            };
            let path = pack_root.join("packs").join(&spelled).join(version);
            // One entry per path, where the file system may fold case.
            if !placed.insert(path.to_string_lossy().to_ascii_lowercase()) {
                continue;
            }
            let entry = match rng.below(8) {
                0 => PackEntry::Odd(*rng.pick(Odd::ALL)),
                _ => PackEntry::Installed(match rng.below(8) {
                    0 => None,
                    1 => Some(PropsEntry::Beside),
                    2 => Some(PropsEntry::Odd(*rng.pick(Odd::ALL))),
                    _ => Some(PropsEntry::File),
                }),
            };
            match entry {
                PackEntry::Odd(odd) => odd_entry::place(odd, &path, "", &aside),
                PackEntry::Installed(props) => {
                    std::fs::create_dir_all(&path).unwrap();
                    let at = path.join("Sdk").join("AutoImport.props");
                    match props {
                        None => {}
                        Some(PropsEntry::File) => write(&at, "<Project />"),
                        Some(PropsEntry::Beside) => {
                            write(&path.join("AutoImport.props"), "<Project />")
                        }
                        Some(PropsEntry::Odd(odd)) => {
                            odd_entry::place(odd, &at, "<Project />", &aside);
                            // A special file MSBuild would import: its read
                            // of a FIFO never returns, and we decline a
                            // socket rather than tell it apart.
                            if matches!(odd, Odd::Socket | Odd::Fifo) {
                                in_domain = false;
                            }
                        }
                    }
                }
            }
            description.push_str(&format!(
                "{entry:?} at {}\n",
                path.strip_prefix(&root).unwrap().display()
            ));
        }
    }
    PackLayout {
        _dir: dir,
        dotnet_root,
        user_root,
        shared_sdk_aliases: if chain.is_some_and(|c| c.contains("any")) {
            shared_sdk_aliases
        } else {
            0
        },
        in_domain,
        description,
    }
}

/// Both locators over generated [`PackLayout`]s, ours against each installed
/// resolver's, certain-implies-exact; where nothing outside the certified
/// subset was generated and the resolver answers, we must answer too. Each
/// way an installed SDK pack reaches the answer (through an alias, under the
/// user root, twice over one path) must be met on a commit.
#[cfg(unix)]
#[test]
fn installed_sdk_packs_are_the_resolver_s() {
    sweep_packs(0x0818_9ac5, 300);
}

/// The fresh-seed twin; `BORZOI_MSBUILD_SOAK_SEED` reproduces a run.
#[cfg(unix)]
#[test]
#[ignore = "soak: run with --ignored; BORZOI_MSBUILD_SOAK_SEED reproduces"]
fn soak_installed_sdk_packs() {
    let (seed, cases) = common::soak_parameters("workload_packs", 2000);
    sweep_packs(seed, cases);
}

#[cfg(unix)]
fn sweep_packs(seed: u64, cases: usize) {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(seed);
        let (mut committed, mut answered, mut threw) = (0, 0, 0);
        // What the committed auto-import answers reached.
        let (mut found, mut aliased, mut user, mut repeated) = (0, 0, 0, 0);
        for case in 0..cases {
            let layout = gen_pack_layout(&mut rng);
            for locator in [
                WORKLOAD_MANIFEST_TARGETS_LOCATOR,
                WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
            ] {
                let env = WorkloadEnvironment {
                    user_dotnet_root: layout.user_root.as_deref(),
                    overrides_present: false,
                    resolver_switched_off: false,
                    global_json: Default::default(),
                    process_architecture: None,
                };
                let sdk_dir = layout.dotnet_root.join("sdk").join(HOST);
                let ours = match resolve_workload_locator(
                    locator,
                    &layout.dotnet_root,
                    &sdk_dir,
                    &env,
                    &Observer::new(),
                ) {
                    Ok(SdkResolution::Roots(roots)) => Some(
                        roots
                            .iter()
                            .map(|p| p.to_string_lossy().into_owned())
                            .collect::<Vec<_>>(),
                    ),
                    Ok(other) => panic!("a locator resolves to roots, not {other:?}"),
                    Err(_) => None,
                };
                let response = oracle.request(&json!({
                    "op": "resolve",
                    "sdk": locator,
                    "dotnetRoot": layout.dotnet_root.to_string_lossy(),
                    "sdkVersion": HOST,
                    "userProfileDir": layout.user_root.as_ref().map(|p| p.to_string_lossy()),
                }));
                let theirs = (response["ok"] == json!(true)).then(|| {
                    response["paths"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|p| p.as_str().unwrap().to_owned())
                        .collect::<Vec<_>>()
                });
                if locator == WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR {
                    threw += usize::from(theirs.is_none());
                }
                if theirs.is_some() && layout.in_domain {
                    answered += 1;
                }
                let failure = match (&ours, &theirs) {
                    (Some(ours), Some(theirs)) if ours == theirs => {
                        committed += 1;
                        if locator == WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR && !ours.is_empty() {
                            found += 1;
                            // `{root}/packs/{id}/{version}/Sdk`: an alias
                            // target's id extends its pack's, or is shared.
                            aliased += usize::from(ours.iter().any(|p| {
                                let id = Path::new(p)
                                    .iter()
                                    .rev()
                                    .nth(2)
                                    .and_then(|id| id.to_str())
                                    .unwrap_or_default();
                                id.starts_with("Contoso.Aliased.") || id.split('.').count() > 3
                            }));
                            user +=
                                usize::from(layout.user_root.as_ref().is_some_and(|u| {
                                    ours.iter().any(|p| Path::new(p).starts_with(u))
                                }));
                            repeated += usize::from(
                                layout.shared_sdk_aliases > 1
                                    && ours.iter().any(|p| p.contains("/Contoso.Aliased.Shared/")),
                            );
                        }
                        None
                    }
                    (Some(ours), _) => {
                        Some(format!("we commit {ours:#?}, the resolver: {response}"))
                    }
                    (None, Some(theirs)) if layout.in_domain => {
                        Some(format!("we decline, the resolver says {theirs:#?}"))
                    }
                    (None, _) => None,
                };
                if let Some(failure) = failure
                    && failures.len() < 8
                {
                    failures.push(format!(
                        "{} case {case}, {locator}: {failure}\n{}",
                        sdk.display(),
                        layout.description
                    ));
                }
            }
        }
        println!(
            "{}: committed {committed}, the resolver answered {answered} in the domain and the \
             auto-import locator threw {threw}, of {}; auto-import answers holding a pack \
             {found}: through an alias {aliased}, under the user root {user}, where two \
             packs alias one path {repeated}",
            sdk.display(),
            cases * 2
        );
        assert!(committed >= cases, "{}: {committed}", sdk.display());
        assert!(
            found > 0 && aliased > 0 && user > 0 && repeated > 0,
            "{}: the sweep never committed some way a pack reaches the answer",
            sdk.display()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// Both locators on each graded SDK's own installation, whose manifests
/// declare real packs (aliased per runtime identifier, of every kind), held
/// to that SDK's resolver: what we commit must be its answer, and we must
/// commit. The devshell's installation carries a `userlocal` marker, so both
/// are handed an empty user root.
#[test]
fn the_installed_layouts_resolve_as_their_own_resolvers_do() {
    let mut failures = Vec::new();
    let user = tempfile::TempDir::new().unwrap();
    let user_root = host_fs::canonicalize(user.path()).unwrap();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let architecture = ProcessArchitecture::from_name(
            oracle.request(&json!({"op": "identity"}))["processArchitecture"]
                .as_str()
                .expect("the oracle names its architecture"),
        )
        .expect("the oracle names an Architecture member");
        let dotnet_root = sdk.parent().unwrap().parent().unwrap();
        let version = sdk.file_name().unwrap().to_string_lossy().into_owned();
        for locator in [
            WORKLOAD_MANIFEST_TARGETS_LOCATOR,
            WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
        ] {
            let env = WorkloadEnvironment {
                user_dotnet_root: Some(&user_root),
                overrides_present: false,
                resolver_switched_off: false,
                global_json: Default::default(),
                process_architecture: Some(architecture),
            };
            let ours = resolve_workload_locator(locator, dotnet_root, &sdk, &env, &Observer::new());
            let response = oracle.request(&json!({
                "op": "resolve",
                "sdk": locator,
                "dotnetRoot": dotnet_root.to_string_lossy(),
                "sdkVersion": version,
                "userProfileDir": user_root.to_string_lossy(),
            }));
            let theirs: Option<Vec<PathBuf>> = response["paths"]
                .as_array()
                .map(|paths| paths.iter().map(|p| p.as_str().unwrap().into()).collect());
            println!(
                "{}: {locator}: we say {ours:?}, the resolver {response}",
                sdk.display()
            );
            match (ours, theirs) {
                (Ok(SdkResolution::Roots(ours)), Some(theirs)) if ours == theirs => {}
                (ours, _) => failures.push(format!(
                    "{}: {locator}: we say {ours:?}, the resolver {response}",
                    sdk.display()
                )),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// Each graded SDK's own manifests, runtime identifier chain and known list,
/// in a fresh dotnet root where every pack id they name (an alias target
/// included) is installed at its version with `Sdk/AutoImport.props`: the
/// auto-import locator's answer is then every SDK pack of the real manifests
/// that resolves for the SDK's runtime identifiers, in composition order, and
/// we must commit it.
#[cfg(unix)]
#[test]
fn the_installed_manifests_packs_resolve_as_their_own_resolvers_do() {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let version = sdk.file_name().unwrap().to_string_lossy().into_owned();
        let fresh = FreshPackRoot::new(&sdk);
        let (dotnet_root, sdk_dir) = (&fresh.dotnet_root, &fresh.sdk_dir);
        let env = WorkloadEnvironment {
            user_dotnet_root: None,
            overrides_present: false,
            resolver_switched_off: false,
            global_json: Default::default(),
            process_architecture: None,
        };
        let ours = resolve_workload_locator(
            WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
            dotnet_root,
            sdk_dir,
            &env,
            &Observer::new(),
        );
        let response = oracle.request(&json!({
            "op": "resolve",
            "sdk": WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
            "dotnetRoot": dotnet_root.to_string_lossy(),
            "sdkVersion": version,
            "userProfileDir": null,
        }));
        let theirs: Option<Vec<PathBuf>> = response["paths"]
            .as_array()
            .map(|paths| paths.iter().map(|p| p.as_str().unwrap().into()).collect());
        println!(
            "{}: the resolver returns {} folders",
            sdk.display(),
            theirs.as_ref().map_or(0, Vec::len)
        );
        match (ours, theirs) {
            (Ok(SdkResolution::Roots(ours)), Some(theirs))
                if ours == theirs && !theirs.is_empty() => {}
            (ours, _) => failures.push(format!(
                "{}: we say {ours:#?}, the resolver {response}",
                sdk.display()
            )),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// A fresh dotnet root holding one graded SDK's own manifests, runtime
/// identifier chain and known list, where every pack id the manifests name
/// (an alias target included) is installed at its version with
/// `Sdk/AutoImport.props`.
#[cfg(unix)]
struct FreshPackRoot {
    _dir: tempfile::TempDir,
    dotnet_root: PathBuf,
    sdk_dir: PathBuf,
}

#[cfg(unix)]
impl FreshPackRoot {
    fn new(sdk: &Path) -> FreshPackRoot {
        let real_root = sdk.parent().unwrap().parent().unwrap();
        let version = sdk.file_name().unwrap().to_string_lossy().into_owned();
        let dir = tempfile::TempDir::new().unwrap();
        let dotnet_root = host_fs::canonicalize(dir.path()).unwrap().join("dotnet");
        let sdk_dir = dotnet_root.join("sdk").join(&version);
        std::fs::create_dir_all(&sdk_dir).unwrap();
        for name in [RID_CHAIN, "KnownWorkloadManifests.txt"] {
            if let Ok(text) = host_fs::read_to_string(sdk.join(name)) {
                write(&sdk_dir.join(name), &text);
            }
        }
        std::os::unix::fs::symlink(
            real_root.join("sdk-manifests"),
            dotnet_root.join("sdk-manifests"),
        )
        .unwrap();
        // Real manifests carry trailing commas, which `serde_json` refuses.
        let trailing_comma = |text: &str| -> String {
            let mut out = String::new();
            let mut pending = String::new();
            for c in text.chars() {
                if c == ',' {
                    out.push_str(&pending);
                    pending = ",".to_owned();
                } else if !pending.is_empty() && c.is_whitespace() {
                    pending.push(c);
                } else {
                    if !(pending.starts_with(',') && (c == '}' || c == ']')) {
                        out.push_str(&pending);
                    } else {
                        out.push_str(&pending[1..]);
                    }
                    pending.clear();
                    out.push(c);
                }
            }
            out + &pending
        };
        for manifest in files_named(&real_root.join("sdk-manifests"), "WorkloadManifest.json") {
            let text = host_fs::read_to_string(&manifest).unwrap();
            let document: serde_json::Value = serde_json::from_str(&trailing_comma(&text))
                .unwrap_or_else(|e| panic!("{}: {e}", manifest.display()));
            let Some(packs) = document["packs"].as_object() else {
                continue;
            };
            for (id, pack) in packs {
                let version = pack["version"].as_str().unwrap();
                let aliases = pack["alias-to"].as_object().into_iter().flatten();
                for id in
                    std::iter::once(id.as_str()).chain(aliases.map(|(_, t)| t.as_str().unwrap()))
                {
                    let props = dotnet_root
                        .join("packs")
                        .join(id)
                        .join(version)
                        .join("Sdk/AutoImport.props");
                    write(&props, "<Project />");
                }
            }
        }
        FreshPackRoot {
            _dir: dir,
            dotnet_root,
            sdk_dir,
        }
    }
}

/// A planted pack layout: manifests (id and `packs` object, in known-list
/// order), the runtime identifier chain, the pack directories that ship
/// `Sdk/AutoImport.props` (relative to the layout root), and the answer
/// each installed resolver must give and we must commit, as directories
/// relative to the layout root.
#[cfg(unix)]
struct PackPlant {
    name: &'static str,
    manifests: &'static [(&'static str, &'static str)],
    chain: &'static str,
    installed: &'static [&'static str],
    user_local: bool,
    answer: &'static [&'static str],
}

#[cfg(unix)]
const PACK_PLANTS: &[PackPlant] = &[
    PackPlant {
        name: "two packs aliased to one path, returned once",
        manifests: &[
            (
                "contoso.one",
                r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0", "alias-to": {"linux-x64": "Shared.Sdk"}}}"#,
            ),
            (
                "contoso.two",
                r#"{"B.Sdk": {"kind": "sdk", "version": "1.0.0", "alias-to": {"any": "Shared.Sdk"}}}"#,
            ),
        ],
        chain: "linux-x64\nany\n",
        installed: &["dotnet/packs/Shared.Sdk/1.0.0"],
        user_local: false,
        answer: &["dotnet/packs/Shared.Sdk/1.0.0/Sdk"],
    },
    PackPlant {
        name: "the alias of the chain's first listed identifier",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "2.0.0", "alias-to": {"any": "A.Any", "linux-x64": "A.Linux"}}}"#,
        )],
        chain: "linux-x64\nany\n",
        installed: &["dotnet/packs/A.Any/2.0.0", "dotnet/packs/A.Linux/2.0.0"],
        user_local: false,
        answer: &["dotnet/packs/A.Linux/2.0.0/Sdk"],
    },
    PackPlant {
        name: "the user root before the dotnet root",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0"}}"#,
        )],
        chain: "",
        installed: &["user/packs/A.Sdk/1.0.0", "dotnet/packs/A.Sdk/1.0.0"],
        user_local: true,
        answer: &["user/packs/A.Sdk/1.0.0/Sdk"],
    },
    PackPlant {
        name: "manifest order, then each manifest's packs in document order",
        manifests: &[
            (
                "contoso.two",
                r#"{"Z.Sdk": {"kind": "Sdk", "version": "1.0.0"}, "Fw": {"kind": "Framework", "version": "1.0.0"}, "M.Sdk": {"kind": "Sdk", "version": "1.0.0"}}"#,
            ),
            (
                "contoso.one",
                r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0"}}"#,
            ),
        ],
        chain: "",
        installed: &[
            "dotnet/packs/A.Sdk/1.0.0",
            "dotnet/packs/Fw/1.0.0",
            "dotnet/packs/M.Sdk/1.0.0",
            "dotnet/packs/Z.Sdk/1.0.0",
        ],
        user_local: false,
        answer: &[
            "dotnet/packs/Z.Sdk/1.0.0/Sdk",
            "dotnet/packs/M.Sdk/1.0.0/Sdk",
            "dotnet/packs/A.Sdk/1.0.0/Sdk",
        ],
    },
];

/// Each [`PackPlant`] on each installed resolver: the resolver gives the
/// planted answer, and we commit it.
#[cfg(unix)]
#[test]
fn planted_sdk_packs_resolve_as_planted() {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        for plant in PACK_PLANTS {
            let dir = tempfile::TempDir::new().unwrap();
            let root = host_fs::canonicalize(dir.path()).unwrap();
            let dotnet_root = root.join("dotnet");
            let sdk_dir = dotnet_root.join("sdk").join(HOST);
            std::fs::create_dir_all(&sdk_dir).unwrap();
            write(&sdk_dir.join(RID_CHAIN), plant.chain);
            let known: Vec<&str> = plant.manifests.iter().map(|(id, _)| *id).collect();
            write(
                &sdk_dir.join("KnownWorkloadManifests.txt"),
                &known.join("\n"),
            );
            for (id, packs) in plant.manifests {
                write(
                    &dotnet_root
                        .join("sdk-manifests")
                        .join(HOST)
                        .join(id)
                        .join("1.0.0")
                        .join("WorkloadManifest.json"),
                    &format!(r#"{{"version": "1.0.0", "packs": {packs}}}"#),
                );
            }
            for pack in plant.installed {
                write(&root.join(pack).join("Sdk/AutoImport.props"), "<Project />");
            }
            let user_root = root.join("user");
            std::fs::create_dir_all(&user_root).unwrap();
            if plant.user_local {
                write(
                    &dotnet_root
                        .join("metadata/workloads")
                        .join(HOST)
                        .join("userlocal"),
                    "",
                );
            }
            let expected: Vec<String> = plant
                .answer
                .iter()
                .map(|p| root.join(p).to_string_lossy().into_owned())
                .collect();
            let env = WorkloadEnvironment {
                user_dotnet_root: Some(&user_root),
                overrides_present: false,
                resolver_switched_off: false,
                global_json: Default::default(),
                process_architecture: None,
            };
            let ours = match resolve_workload_locator(
                WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
                &dotnet_root,
                &sdk_dir,
                &env,
                &Observer::new(),
            ) {
                Ok(SdkResolution::Roots(roots)) => Ok(roots
                    .iter()
                    .map(|p| p.to_string_lossy().into_owned())
                    .collect::<Vec<_>>()),
                other => Err(format!("{other:?}")),
            };
            let response = oracle.request(&json!({
                "op": "resolve",
                "sdk": WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
                "dotnetRoot": dotnet_root.to_string_lossy(),
                "sdkVersion": HOST,
                "userProfileDir": user_root.to_string_lossy(),
            }));
            let theirs: Option<Vec<String>> = response["paths"].as_array().map(|paths| {
                paths
                    .iter()
                    .map(|p| p.as_str().unwrap().to_owned())
                    .collect()
            });
            if theirs.as_ref() != Some(&expected) {
                failures.push(format!(
                    "{}, {}: the resolver says {response}, planted {expected:#?}",
                    sdk.display(),
                    plant.name
                ));
            }
            if ours.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "{}, {}: we say {ours:#?}, planted {expected:#?}",
                    sdk.display(),
                    plant.name
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// ---------------------------------------------------------------------------
// The workload pack an SDK name that is no locator names.

/// The workload resolver's answer for an SDK name that is no locator
/// (`TryGetPackInfo`), in a currency both sides speak.
#[derive(Clone, Debug, PartialEq, Eq)]
enum PackAnswer {
    /// `NullResolutionResult`: MSBuild asks the next resolver.
    Null,
    /// `SinglePathResolutionResult`: the pack's `Sdk` folder.
    Single(String),
    /// `EmptyResolutionResult` holding exactly one `MissingWorkloadPack` item,
    /// for the requested name, with this `Version` and no other metadata, and
    /// no property.
    Missing(String),
}

/// Our answer for `name`, or `None` where we decline.
fn ours_pack(
    name: &str,
    dotnet_root: &Path,
    version: &str,
    env: &WorkloadEnvironment<'_>,
) -> Option<PackAnswer> {
    let sdk_dir = dotnet_root.join("sdk").join(version);
    match resolve_workload_pack(name, dotnet_root, &sdk_dir, env, &Observer::new()) {
        Ok(WorkloadPackResolution::NotAPack) => Some(PackAnswer::Null),
        Ok(WorkloadPackResolution::Installed(path)) => {
            Some(PackAnswer::Single(path.to_string_lossy().into_owned()))
        }
        Ok(WorkloadPackResolution::Missing { version }) => Some(PackAnswer::Missing(version)),
        Err(_) => None,
    }
}

/// The resolver's answer for `name`, or what it threw.
fn theirs_pack(
    oracle: &mut Oracle,
    name: &str,
    dotnet_root: &Path,
    version: &str,
    user_root: Option<&Path>,
) -> Result<PackAnswer, String> {
    let response = oracle.request(&json!({
        "op": "resolve",
        "sdk": name,
        "dotnetRoot": dotnet_root.to_string_lossy(),
        "sdkVersion": version,
        "userProfileDir": user_root.map(|p| p.to_string_lossy()),
    }));
    if response["ok"] != json!(true) {
        return Err(response["thrown"].to_string());
    }
    Ok(match response["kind"].as_str() {
        Some("null") => PackAnswer::Null,
        Some("single") => PackAnswer::Single(response["path"].as_str().unwrap().to_owned()),
        Some("empty") => {
            let version = match (
                response["properties"].as_object(),
                response["items"].as_array(),
            ) {
                (Some(properties), Some(items)) if properties.is_empty() && items.len() == 1 => {
                    let item = &items[0];
                    let metadata = item["metadata"].as_object();
                    match (item["type"].as_str(), item["spec"].as_str(), metadata) {
                        (Some("MissingWorkloadPack"), Some(spec), Some(metadata))
                            if spec == name && metadata.len() == 1 =>
                        {
                            metadata.get("Version").and_then(|v| v.as_str())
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            PackAnswer::Missing(
                version
                    .unwrap_or_else(|| {
                        panic!(
                            "the resolver's empty result is not the one MissingWorkloadPack \
                             item this differential knows: {response}"
                        )
                    })
                    .to_owned(),
            )
        }
        _ => panic!("a pack name resolves to no locator's answer: {response}"),
    })
}

/// A pack's `kind`, spelled as manifests may spell it.
#[cfg(unix)]
const PACK_KINDS: &[&str] = &[
    "Sdk",
    "sdk",
    "SDK",
    "Framework",
    "Library",
    "Template",
    "Tool",
];

/// Where the resolver looks for a pack of `kind` under `root`, and whether it
/// asks `File.Exists` of it rather than `Directory.Exists`
/// (`WorkloadResolver.GetPackPath`). Only for placing entries: the resolver,
/// not this, grades where we look.
#[cfg(unix)]
fn pack_location(root: &Path, id: &str, version: &str, kind: &str) -> (PathBuf, bool) {
    let nupkg = format!("{}.{}.nupkg", id.to_lowercase(), version.to_lowercase());
    match kind.to_ascii_lowercase().as_str() {
        "sdk" | "framework" => (root.join("packs").join(id).join(version), false),
        "tool" => (root.join("tool-packs").join(id).join(version), false),
        "template" => (root.join("template-packs").join(nupkg), true),
        "library" => (root.join("library-packs").join(nupkg), true),
        other => panic!("no pack kind {other}"),
    }
}

/// What a generated manifest says of the pack a query names.
#[cfg(unix)]
#[derive(Clone, Debug)]
struct DefinedPack {
    kind: &'static str,
    aliased: bool,
    /// Whether its version is a plain path component, which we certify.
    plain: bool,
}

/// One SDK name looked up on a [`PackLookupLayout`]: the name, and the pack
/// it names ignoring case, if a manifest defines one.
#[cfg(unix)]
struct PackQuery {
    name: String,
    defined: Option<DefinedPack>,
}

/// A generated layout of manifests defining packs of every kind (aliased or
/// not, at plain versions and others, an id sometimes shared between
/// manifests, which fails the composition), the runtime identifier chain, and
/// each pack id they can resolve to placed under the user root, the dotnet
/// root, both or neither: at the location of its kind or of another kind, in
/// the manifest's casing or another, as a directory, a file or an odd entry.
#[cfg(unix)]
struct PackLookupLayout {
    _dir: tempfile::TempDir,
    dotnet_root: PathBuf,
    user_root: Option<PathBuf>,
    queries: Vec<PackQuery>,
    description: String,
}

#[cfg(unix)]
fn gen_pack_lookup_layout(rng: &mut SplitMix64) -> PackLookupLayout {
    let dir = tempfile::TempDir::new().unwrap();
    let root = host_fs::canonicalize(dir.path()).unwrap();
    let dotnet_root = root.join("dotnet");
    let sdk_dir = dotnet_root.join("sdk").join(HOST);
    std::fs::create_dir_all(&sdk_dir).unwrap();
    let mut description = String::new();

    let chain = *rng.pick(PACK_RID_CHAINS);
    if let Some(chain) = chain {
        write(&sdk_dir.join(RID_CHAIN), chain);
    }
    description.push_str(&format!("runtime identifier chain {chain:?}\n"));

    // Each pack a manifest defines, and every (id, kind, version) a pack can
    // resolve to, for placing.
    let mut defined: Vec<(String, DefinedPack)> = Vec::new();
    let mut targets: Vec<(String, &'static str, String)> = Vec::new();
    let mut alias_targets: Vec<String> = Vec::new();
    for (index, manifest_id) in ["contoso.one", "contoso.two"].iter().enumerate() {
        if rng.below(4) == 0 {
            continue;
        }
        let mut packs = serde_json::Map::new();
        for k in 0..rng.below(4) {
            let id = match rng.below(12) {
                // In both manifests, the composition throws.
                0 => "Contoso.Shared".to_owned(),
                _ => format!("Contoso.M{index}.P{k}"),
            };
            let kind = *rng.pick(PACK_KINDS);
            let (version, plain) = if rng.below(10) == 0 {
                *rng.pick(PACK_VERSIONS)
            } else {
                *rng.pick(&PACK_VERSIONS[..4])
            };
            let mut pack = serde_json::Map::new();
            pack.insert("kind".to_owned(), json!(kind));
            pack.insert("version".to_owned(), json!(version));
            let aliased = match rng.below(4) {
                0 => {
                    pack.insert("alias-to".to_owned(), json!({}));
                    targets.push((id.clone(), kind, version.to_owned()));
                    false
                }
                1 => {
                    let mut aliases = serde_json::Map::new();
                    for _ in 0..1 + rng.below(3) {
                        let key = *rng.pick(ALIAS_KEYS);
                        let target = format!("{id}.{}", key.trim().replace('-', "."));
                        targets.push((target.clone(), kind, version.to_owned()));
                        alias_targets.push(target.clone());
                        aliases.insert(key.to_owned(), json!(target));
                    }
                    pack.insert("alias-to".to_owned(), serde_json::Value::Object(aliases));
                    true
                }
                _ => {
                    targets.push((id.clone(), kind, version.to_owned()));
                    false
                }
            };
            defined.push((
                id.clone(),
                DefinedPack {
                    kind,
                    aliased,
                    plain,
                },
            ));
            packs.insert(id, serde_json::Value::Object(pack));
        }
        let body = json!({ "version": "1.0.0", "packs": packs });
        write(
            &dotnet_root
                .join("sdk-manifests")
                .join(HOST)
                .join(manifest_id)
                .join("1.0.0")
                .join("WorkloadManifest.json"),
            &body.to_string(),
        );
        description.push_str(&format!("manifest {manifest_id}: {body}\n"));
    }

    let user_root = (rng.below(3) == 0).then(|| {
        let user_root = root.join("user");
        std::fs::create_dir_all(&user_root).unwrap();
        if rng.below(4) != 0 {
            write(
                &dotnet_root
                    .join("metadata/workloads")
                    .join(HOST)
                    .join("userlocal"),
                "",
            );
            description.push_str("userlocal marker\n");
        }
        description.push_str("user root\n");
        user_root
    });

    targets.sort();
    targets.dedup();
    let aside = root.join("aside");
    let pack_roots: Vec<PathBuf> = user_root
        .iter()
        .cloned()
        .chain([dotnet_root.clone()])
        .collect();
    let mut placed = BTreeSet::new();
    for (id, kind, version) in &targets {
        if !PACK_VERSIONS[..4].iter().any(|(v, _)| v == version) {
            continue;
        }
        for pack_root in &pack_roots {
            if rng.below(3) == 0 {
                continue;
            }
            // Now and then at another kind's location, which the resolver
            // does not look in.
            let at_kind = if rng.below(8) == 0 {
                *rng.pick(PACK_KINDS)
            } else {
                kind
            };
            let spelled = if rng.below(5) == 0 {
                id.to_ascii_lowercase()
            } else {
                id.clone()
            };
            let (path, is_file) = pack_location(pack_root, &spelled, version, at_kind);
            if !placed.insert(path.to_string_lossy().to_ascii_lowercase()) {
                continue;
            }
            let what = match rng.below(8) {
                0 | 1 => {
                    let odd = *rng.pick(Odd::ALL);
                    odd_entry::place(odd, &path, "", &aside);
                    format!("{odd:?}")
                }
                2 if is_file => {
                    std::fs::create_dir_all(&path).unwrap();
                    "a directory".to_owned()
                }
                _ if is_file => {
                    write(&path, "");
                    "a file".to_owned()
                }
                _ => {
                    std::fs::create_dir_all(path.join("Sdk")).unwrap();
                    "a directory".to_owned()
                }
            };
            description.push_str(&format!(
                "{what} at {}\n",
                path.strip_prefix(&root).unwrap().display()
            ));
        }
    }

    let recase = |rng: &mut SplitMix64, name: &str| match rng.below(4) {
        0 => name.to_ascii_lowercase(),
        1 => name.to_ascii_uppercase(),
        _ => name.to_owned(),
    };
    let mut queries: Vec<PackQuery> = Vec::new();
    // The last definition of an id is the one a manifest keeps (a JSON
    // object's repeated key), and an id both manifests define is one query.
    for (id, pack) in defined.iter().rev() {
        if queries.iter().any(|q| q.name.eq_ignore_ascii_case(id)) {
            continue;
        }
        queries.push(PackQuery {
            name: recase(rng, id),
            defined: Some(pack.clone()),
        });
    }
    if let Some(target) = alias_targets.first() {
        queries.push(PackQuery {
            name: target.clone(),
            defined: None,
        });
    }
    queries.push(PackQuery {
        name: "Contoso.Unknown".to_owned(),
        defined: None,
    });
    PackLookupLayout {
        _dir: dir,
        dotnet_root,
        user_root,
        queries,
        description,
    }
}

/// SDK names that are no locator, looked up on generated
/// [`PackLookupLayout`]s, ours against each installed resolver's,
/// certain-implies-exact; where the pack named is at a plain version and the
/// resolver answers, we must answer too. Each way the answer can come about
/// (an installed pack through an alias, under the user root, of a kind other
/// than `Sdk`, named in another case; a missing pack, a file-kind pack among
/// them; a defined alias that resolves for no listed identifier) must be met
/// on a commit.
#[cfg(unix)]
#[test]
fn workload_packs_named_as_sdks_are_the_resolver_s() {
    sweep_pack_lookups(0x0818_7e9b, 300);
}

/// The fresh-seed twin; `BORZOI_MSBUILD_SOAK_SEED` reproduces a run.
#[cfg(unix)]
#[test]
#[ignore = "soak: run with --ignored; BORZOI_MSBUILD_SOAK_SEED reproduces"]
fn soak_workload_packs_named_as_sdks() {
    let (seed, cases) = common::soak_parameters("workload_pack_lookups", 2000);
    sweep_pack_lookups(seed, cases);
}

#[cfg(unix)]
fn sweep_pack_lookups(seed: u64, cases: usize) {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(seed);
        let (mut committed, mut queried) = (0, 0);
        // What the committed answers reached.
        let (mut aliased, mut user, mut other_kind, mut recased) = (0, 0, 0, 0);
        let (mut missing, mut missing_file_kind, mut unresolved_alias) = (0, 0, 0);
        for case in 0..cases {
            let layout = gen_pack_lookup_layout(&mut rng);
            let env = WorkloadEnvironment {
                user_dotnet_root: layout.user_root.as_deref(),
                overrides_present: false,
                resolver_switched_off: false,
                global_json: Default::default(),
                process_architecture: None,
            };
            for query in &layout.queries {
                queried += 1;
                let ours = ours_pack(&query.name, &layout.dotnet_root, HOST, &env);
                let theirs = theirs_pack(
                    &mut oracle,
                    &query.name,
                    &layout.dotnet_root,
                    HOST,
                    layout.user_root.as_deref(),
                );
                let in_domain = query.defined.as_ref().is_none_or(|pack| pack.plain);
                let failure = match (&ours, &theirs) {
                    (Some(ours), Ok(theirs)) if ours == theirs => {
                        committed += 1;
                        let kind = query.defined.as_ref().map(|pack| pack.kind);
                        match ours {
                            PackAnswer::Single(path) => {
                                aliased += usize::from(
                                    query.defined.as_ref().is_some_and(|pack| pack.aliased),
                                );
                                user += usize::from(
                                    layout
                                        .user_root
                                        .as_ref()
                                        .is_some_and(|u| Path::new(path).starts_with(u)),
                                );
                                other_kind += usize::from(
                                    kind.is_some_and(|k| !k.eq_ignore_ascii_case("sdk")),
                                );
                                recased += usize::from(!path.contains(&query.name));
                            }
                            PackAnswer::Missing(_) => {
                                missing += 1;
                                missing_file_kind += usize::from(
                                    kind.is_some_and(|k| matches!(k, "Template" | "Library")),
                                );
                            }
                            PackAnswer::Null => {
                                unresolved_alias += usize::from(query.defined.is_some());
                            }
                        }
                        None
                    }
                    (Some(ours), _) => {
                        Some(format!("we commit {ours:?}, the resolver: {theirs:?}"))
                    }
                    (None, Ok(theirs)) if in_domain => {
                        Some(format!("we decline, the resolver says {theirs:?}"))
                    }
                    (None, _) => None,
                };
                if let Some(failure) = failure
                    && failures.len() < 8
                {
                    failures.push(format!(
                        "{} case {case}, {:?}: {failure}\n{}",
                        sdk.display(),
                        query.name,
                        layout.description
                    ));
                }
            }
        }
        println!(
            "{}: committed {committed} of {queried} lookups: installed through an alias \
             {aliased}, under the user root {user}, of another kind {other_kind}, named in \
             another case {recased}; missing {missing}, of a file kind {missing_file_kind}; a \
             defined pack resolving for no identifier {unresolved_alias}",
            sdk.display(),
        );
        assert!(committed * 2 >= queried, "{}: {committed}", sdk.display());
        assert!(
            aliased > 0
                && user > 0
                && other_kind > 0
                && recased > 0
                && missing > 0
                && missing_file_kind > 0
                && unresolved_alias > 0,
            "{}: the sweep never committed some way a pack lookup answers",
            sdk.display()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// A planted pack lookup: manifests (id and `packs` object), the runtime
/// identifier chain, the entries installed (relative to the layout root: a
/// directory, or a file where the path ends `.nupkg`), the name looked up,
/// and the answer each installed resolver must give and we must commit.
#[cfg(unix)]
struct PackLookupPlant {
    name: &'static str,
    manifests: &'static [(&'static str, &'static str)],
    chain: &'static str,
    installed: &'static [&'static str],
    user_local: bool,
    query: &'static str,
    answer: PlantedPackAnswer,
}

/// [`PackAnswer`], with a path relative to the layout root.
#[cfg(unix)]
enum PlantedPackAnswer {
    Null,
    Single(&'static str),
    Missing(&'static str),
}

#[cfg(unix)]
const PACK_LOOKUP_PLANTS: &[PackLookupPlant] = &[
    PackLookupPlant {
        name: "an installed pack, named in another case",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0"}}"#,
        )],
        chain: "",
        installed: &["dotnet/packs/A.Sdk/1.0.0"],
        user_local: false,
        query: "a.SDK",
        answer: PlantedPackAnswer::Single("dotnet/packs/A.Sdk/1.0.0/Sdk"),
    },
    PackLookupPlant {
        name: "an alias, through the chain's first identifier it names",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "2.0.0", "alias-to": {"any": "A.Any", "linux-x64": "A.Linux"}}}"#,
        )],
        chain: "linux-x64\nany\n",
        installed: &["dotnet/packs/A.Any/2.0.0", "dotnet/packs/A.Linux/2.0.0"],
        user_local: false,
        query: "A.Sdk",
        answer: PlantedPackAnswer::Single("dotnet/packs/A.Linux/2.0.0/Sdk"),
    },
    PackLookupPlant {
        name: "an alias naming none of the chain's identifiers is no pack",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0", "alias-to": {"win-x64": "A.Win"}}}"#,
        )],
        chain: "linux-x64\nany\n",
        installed: &["dotnet/packs/A.Win/1.0.0"],
        user_local: false,
        query: "A.Sdk",
        answer: PlantedPackAnswer::Null,
    },
    PackLookupPlant {
        name: "an alias's target is no pack itself",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0", "alias-to": {"any": "A.Any"}}}"#,
        )],
        chain: "any\n",
        installed: &["dotnet/packs/A.Any/1.0.0"],
        user_local: false,
        query: "A.Any",
        answer: PlantedPackAnswer::Null,
    },
    PackLookupPlant {
        name: "the user root before the dotnet root",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "1.0.0"}}"#,
        )],
        chain: "",
        installed: &["user/packs/A.Sdk/1.0.0", "dotnet/packs/A.Sdk/1.0.0"],
        user_local: true,
        query: "A.Sdk",
        answer: PlantedPackAnswer::Single("user/packs/A.Sdk/1.0.0/Sdk"),
    },
    PackLookupPlant {
        name: "a pack installed nowhere is missing, at its own version",
        manifests: &[(
            "contoso.one",
            r#"{"A.Sdk": {"kind": "Sdk", "version": "3.1.4"}}"#,
        )],
        chain: "",
        installed: &["dotnet/packs/A.Sdk/1.0.0"],
        user_local: false,
        query: "A.Sdk",
        answer: PlantedPackAnswer::Missing("3.1.4"),
    },
    PackLookupPlant {
        name: "an installed template pack is a file, so it is missing",
        manifests: &[(
            "contoso.one",
            r#"{"A.Templates": {"kind": "Template", "version": "1.0.0-RC.1"}}"#,
        )],
        chain: "",
        installed: &["dotnet/template-packs/a.templates.1.0.0-rc.1.nupkg"],
        user_local: false,
        query: "A.Templates",
        answer: PlantedPackAnswer::Missing("1.0.0-RC.1"),
    },
    PackLookupPlant {
        name: "a tool pack is a directory under tool-packs",
        manifests: &[(
            "contoso.one",
            r#"{"A.Tool": {"kind": "tool", "version": "1.0.0"}}"#,
        )],
        chain: "",
        installed: &[
            "dotnet/packs/A.Tool/1.0.0",
            "dotnet/tool-packs/A.Tool/1.0.0",
        ],
        user_local: false,
        query: "A.Tool",
        answer: PlantedPackAnswer::Single("dotnet/tool-packs/A.Tool/1.0.0/Sdk"),
    },
];

/// Each [`PackLookupPlant`] on each installed resolver: the resolver gives the
/// planted answer, and we commit it.
#[cfg(unix)]
#[test]
fn planted_pack_lookups_resolve_as_planted() {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        for plant in PACK_LOOKUP_PLANTS {
            let dir = tempfile::TempDir::new().unwrap();
            let root = host_fs::canonicalize(dir.path()).unwrap();
            let dotnet_root = root.join("dotnet");
            let sdk_dir = dotnet_root.join("sdk").join(HOST);
            std::fs::create_dir_all(&sdk_dir).unwrap();
            write(&sdk_dir.join(RID_CHAIN), plant.chain);
            for (id, packs) in plant.manifests {
                write(
                    &dotnet_root
                        .join("sdk-manifests")
                        .join(HOST)
                        .join(id)
                        .join("1.0.0")
                        .join("WorkloadManifest.json"),
                    &format!(r#"{{"version": "1.0.0", "packs": {packs}}}"#),
                );
            }
            for entry in plant.installed {
                if entry.ends_with(".nupkg") {
                    write(&root.join(entry), "");
                } else {
                    std::fs::create_dir_all(root.join(entry)).unwrap();
                }
            }
            let user_root = root.join("user");
            std::fs::create_dir_all(&user_root).unwrap();
            if plant.user_local {
                write(
                    &dotnet_root
                        .join("metadata/workloads")
                        .join(HOST)
                        .join("userlocal"),
                    "",
                );
            }
            let expected = match plant.answer {
                PlantedPackAnswer::Null => PackAnswer::Null,
                PlantedPackAnswer::Single(path) => {
                    PackAnswer::Single(root.join(path).to_string_lossy().into_owned())
                }
                PlantedPackAnswer::Missing(version) => PackAnswer::Missing(version.to_owned()),
            };
            let env = WorkloadEnvironment {
                user_dotnet_root: Some(&user_root),
                overrides_present: false,
                resolver_switched_off: false,
                global_json: Default::default(),
                process_architecture: None,
            };
            let ours = ours_pack(plant.query, &dotnet_root, HOST, &env);
            let theirs = theirs_pack(
                &mut oracle,
                plant.query,
                &dotnet_root,
                HOST,
                Some(&user_root),
            );
            if theirs.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "{}, {}: the resolver says {theirs:?}, planted {expected:?}",
                    sdk.display(),
                    plant.name
                ));
            }
            if ours.as_ref() != Some(&expected) {
                failures.push(format!(
                    "{}, {}: we say {ours:?}, planted {expected:?}",
                    sdk.display(),
                    plant.name
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// A blank SDK name, which `WorkloadPackId` refuses before any lookup: each
/// installed resolver throws, and we decline.
#[cfg(unix)]
#[test]
fn a_blank_pack_name_throws_and_declines() {
    let dir = tempfile::TempDir::new().unwrap();
    let dotnet_root = host_fs::canonicalize(dir.path()).unwrap().join("dotnet");
    std::fs::create_dir_all(dotnet_root.join("sdk").join(HOST)).unwrap();
    let env = WorkloadEnvironment {
        user_dotnet_root: None,
        overrides_present: false,
        resolver_switched_off: false,
        global_json: Default::default(),
        process_architecture: None,
    };
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        for name in ["", " ", "\t"] {
            let theirs = theirs_pack(&mut oracle, name, &dotnet_root, HOST, None);
            assert!(theirs.is_err(), "{}: {name:?}: {theirs:?}", sdk.display());
            assert_eq!(ours_pack(name, &dotnet_root, HOST, &env), None, "{name:?}");
        }
    }
}

/// The literal SDK names the `<Import Sdk="…"/>` elements of every
/// `WorkloadManifest.targets` under `root` name (a name spelled through a
/// property is left out).
fn imported_sdk_names(root: &Path) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for targets in files_named(root, "WorkloadManifest.targets") {
        let text = host_fs::read_to_string(&targets).unwrap();
        let document = borzoi_msbuild::document::parse(&text)
            .unwrap_or_else(|e| panic!("{}: {e}", targets.display()));
        for node in document.descendants() {
            if node.has_tag_name("Import")
                && let Some(sdk) = borzoi_msbuild::document::attribute(node, "Sdk")
                && !sdk.contains('$')
            {
                names.insert(sdk.into_owned());
            }
        }
    }
    names
}

/// Every pack name the real manifests' targets import, on each graded SDK's
/// own installation and on a fresh root holding its manifests with every pack
/// they name installed ([`FreshPackRoot`]), held to that SDK's resolver: we
/// must commit its answer. The fresh root must answer some with an installed
/// pack.
#[cfg(unix)]
#[test]
fn the_installed_manifests_imported_packs_resolve_as_their_own_resolvers_do() {
    let mut failures = Vec::new();
    let user = tempfile::TempDir::new().unwrap();
    let user_root = host_fs::canonicalize(user.path()).unwrap();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let architecture = ProcessArchitecture::from_name(
            oracle.request(&json!({"op": "identity"}))["processArchitecture"]
                .as_str()
                .expect("the oracle names its architecture"),
        )
        .expect("the oracle names an Architecture member");
        let real_root = sdk.parent().unwrap().parent().unwrap();
        let version = sdk.file_name().unwrap().to_string_lossy().into_owned();
        let names = imported_sdk_names(&real_root.join("sdk-manifests"));
        assert!(
            !names.is_empty(),
            "{}: no manifest's targets import a pack",
            sdk.display()
        );
        let fresh = FreshPackRoot::new(&sdk);
        // Installed-pack answers on the fresh root, where every pack is.
        let mut installed = 0;
        for (dotnet_root, user_root, architecture) in [
            (real_root, Some(user_root.as_path()), Some(architecture)),
            (fresh.dotnet_root.as_path(), None, None),
        ] {
            let env = WorkloadEnvironment {
                user_dotnet_root: user_root,
                overrides_present: false,
                resolver_switched_off: false,
                global_json: Default::default(),
                process_architecture: architecture,
            };
            for name in &names {
                let ours = ours_pack(name, dotnet_root, &version, &env);
                let theirs = theirs_pack(&mut oracle, name, dotnet_root, &version, user_root);
                match (&ours, &theirs) {
                    (Some(ours), Ok(theirs)) if ours == theirs => {
                        installed += usize::from(
                            dotnet_root == fresh.dotnet_root
                                && matches!(ours, PackAnswer::Single(_)),
                        );
                    }
                    _ => failures.push(format!(
                        "{} under {}: {name}: we say {ours:?}, the resolver {theirs:?}",
                        sdk.display(),
                        dotnet_root.display()
                    )),
                }
            }
        }
        println!(
            "{}: {} imported pack names, {installed} answers an installed pack on the \
             fresh root",
            sdk.display(),
            names.len()
        );
        assert!(
            installed > 0,
            "{}: no answer on the fresh root was an installed pack",
            sdk.display()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
