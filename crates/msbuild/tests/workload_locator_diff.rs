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
//! Three sweeps, each *certain-implies-exact* (an answer we commit must be the
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
//!   directories, and a missing `WorkloadManifest.targets`.

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
/// clears `in_domain` for a manifest version outside the plain spellings.
fn populate_band(rng: &mut SplitMix64, band_dir: &Path, in_domain: &mut bool) -> Vec<String> {
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
                    let (version, plain) = *rng.pick(MANIFEST_VERSIONS);
                    if !plain {
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

fn gen_layout(rng: &mut SplitMix64) -> Layout {
    let dir = tempfile::TempDir::new().unwrap();
    let dotnet_root = host_fs::canonicalize(dir.path()).unwrap().join("dotnet");
    let host = gen_host(rng);
    let mut description = format!("host {}\n", host.version);
    // The locators resolve a host whose spelling they certify; for the rest
    // they make no claim.
    let mut in_domain = test_support::workload_accepts_host_version(&host.version);

    let sdk_dir = dotnet_root.join("sdk").join(&host.version);
    std::fs::create_dir_all(&sdk_dir).unwrap();
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
            in_domain = false;
        }
        let band_dir = dotnet_root.join("sdk-manifests").join(&band);
        let contents = populate_band(rng, &band_dir, &mut in_domain);
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

fn sweep_locators(seed: u64, cases: usize) {
    let mut failures = Vec::new();
    for sdk in graded_sdks() {
        let mut oracle = Oracle::spawn_on(&sdk);
        let mut rng = SplitMix64(seed);
        let mut committed = 0;
        let mut prerelease_committed = 0;
        let mut hosts = BTreeSet::new();
        for case in 0..cases {
            let layout = gen_layout(&mut rng);
            for locator in [
                WORKLOAD_MANIFEST_TARGETS_LOCATOR,
                WORKLOAD_AUTO_IMPORT_PROPS_LOCATOR,
            ] {
                let ours = ours(&layout, locator);
                let theirs = theirs(&mut oracle, &layout, locator);
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
                    if layout.host.pre.is_some() {
                        prerelease_committed += 1;
                    }
                }
                hosts.insert(layout.host.version.clone());
                if let Some(verdict) = verdict
                    && failures.len() < 8
                {
                    failures.push(format!(
                        "{} case {case}, {locator}: {verdict}\n{}",
                        sdk.display(),
                        layout.description
                    ));
                }
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
