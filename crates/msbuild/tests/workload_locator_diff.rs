//! The workload locator SDKs, held to MSBuild's own workload resolver.
//!
//! `borzoi_msbuild::workloads` reimplements what the workload MSBuild SDK
//! resolver answers for `Microsoft.NET.SDK.WorkloadManifestTargetsLocator` and
//! `Microsoft.NET.SDK.WorkloadAutoImportPropsLocator`. This differential asks
//! the real one, through `tools/workload-oracle`, which loads each installed
//! SDK's `Microsoft.NET.Sdk.WorkloadMSBuildSdkResolver.dll` and calls
//! `CachingWorkloadResolver.Resolve` (the call MSBuild makes) on generated
//! dotnet layouts. It grades every SDK of the devshell's corpus root
//! (`BORZOI_DOTNET_ROOT_SDK11`), so a prerelease SDK's resolver is graded as
//! well as the release ones.
//!
//! Four sweeps, each *certain-implies-exact* (an answer we commit must be the
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

use borzoi_msbuild::observed::host_fs::HostPath as _;
use borzoi_msbuild::observed::{Observer, host_fs};
use borzoi_msbuild::workloads::{
    WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR, WORKLOAD_MANIFEST_TARGETS_LOCATOR, WorkloadEnvironment,
    resolve_workload_locator,
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
/// resolve (plain release versions).
const MANIFEST_VERSIONS: &[(&str, bool)] = &[
    ("1.0.0", true),
    ("1.0.2", true),
    ("1.0.10", true),
    ("2.0.0", true),
    ("2.0.0-rc.1", false),
    ("2.0.0-preview.3.1", false),
];

/// The manifest versions in the domain we must resolve.
const PLAIN_MANIFEST_VERSIONS: &[(&str, bool)] = &[
    ("1.0.0", true),
    ("1.0.2", true),
    ("1.0.10", true),
    ("2.0.0", true),
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
        global_json_pins_workload_set: false,
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
    let mut cases: Vec<(String, Content, Option<(&str, &str)>)> = CONTENTS
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
