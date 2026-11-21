//! The environment reads [`borzoi_msbuild::fsc::environment_reads`] pins
//! (`src/fsc_environment_reads.txt`), held to each verified SDK as installed,
//! so an SDK bump fails here until its reads are scanned and recorded:
//!
//! - **properties**: every property a file of the SDK reads, its version
//!   directory's every MSBuild document and its verified workload manifests:
//!   each `$(Name)` the crate's own reference scan
//!   ([`borzoi_msbuild::test_support::property_references`], which never
//!   under-reports) finds in an attribute or an element's text. A name the
//!   SDK computes from an item's identity (`$(%(PropertyNames.Identity))`) is
//!   each name that item type's declarations in the SDK give: a literal one
//!   whole, else the literal text before its first expansion as a prefix. A
//!   name computed any other way, or from a declaration that starts with an
//!   expansion, cannot be listed, and fails the scan.
//! - **variables**: what the build's tools may read, from the binaries. Each
//!   managed assembly of the SDK and its runtime goes through
//!   `msbuild-condition-oracle`'s `envReads` op (the strings its IL passes to
//!   an environment read, and every user string shaped like a conventional
//!   variable name); each native binary of the host, the runtime and the SDK
//!   gives its strings of that shape, in ASCII and in UTF-16. Prefixes are the
//!   strings a composed read starts with, and the native strings ending in
//!   `_` (the runtime's `DOTNET_` and `COMPlus_` knobs).
//!
//! Regenerate with
//! `BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test fsc_environment_reads`.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use borzoi_msbuild::document;
use borzoi_msbuild::fsc::{
    EnvironmentReads, environment_read_sdks, environment_reads, parse_environment_reads,
    verified_manifests, verified_sdks,
};
use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::property_references;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::msbuild_oracle::build_environment;

const REGENERATE: &str = "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
                          --test fsc_environment_reads";

/// The SDK the devshell's `dotnet` resolves outside any `global.json`.
fn devshell_sdk() -> String {
    let tmp = tempfile::TempDir::new().unwrap();
    let mut cmd = std::process::Command::new("dotnet");
    cmd.current_dir(tmp.path())
        .arg("--version")
        .env_clear()
        .envs(build_environment());
    let output = BoundedCommand::new(cmd)
        .timeout(std::time::Duration::from_secs(300))
        .run()
        .expect("dotnet --version");
    assert!(output.status.success(), "dotnet --version failed");
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

/// The SDKs whose reads must be pinned: every verified one, and the
/// devshell's, which the grading of a new SDK needs before it is verified.
fn sdks_to_pin() -> BTreeSet<String> {
    verified_sdks()
        .map(str::to_string)
        .chain([devshell_sdk()])
        .collect()
}

/// Whether the SDK `sdk` is installed in the devshell's .NET install, so it
/// can be scanned here.
fn installed(sdk: &str) -> bool {
    common::dotnet_root_from_env()
        .join("sdk")
        .join(sdk)
        .host_is_dir()
}

/// The platform this scan runs on, which keys every list of the pin: the
/// binaries of one SDK version differ between platforms (their native code,
/// their runtime's build).
fn platform() -> String {
    format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH)
}

/// A version directory's name as numbers (`10.0.12`), or `None` for one
/// with a prerelease label or another shape.
fn version(name: &str) -> Option<Vec<u64>> {
    name.split('.').map(|part| part.parse().ok()).collect()
}

/// The directory under `parent` the .NET host would roll a request for
/// `wanted` forward to: the highest version of the same major and minor, at
/// least `wanted` (its default `LatestPatch`).
fn rolled_forward(parent: &Path, wanted: &str) -> PathBuf {
    let wanted = version(wanted).unwrap_or_else(|| panic!("a version {wanted:?}"));
    host_fs::read_dir(parent)
        .unwrap_or_else(|e| panic!("{}: {e}", parent.display()))
        .flatten()
        .filter_map(|entry| {
            let name = entry.file_name().to_string_lossy().into_owned();
            let v = version(&name)?;
            (v.len() == 3 && v[..2] == wanted[..2] && v >= wanted).then_some((v, entry.path()))
        })
        .max()
        .map(|(_, path)| path)
        .unwrap_or_else(|| {
            panic!(
                "no version under {} rolls {wanted:?} forward",
                parent.display()
            )
        })
}

/// The runtime the SDK `sdk` runs on: its `dotnet.runtimeconfig.json`'s
/// framework, rolled forward as the host rolls it, and the host resolver
/// (`host/fxr`) of the same version.
fn sdk_runtime(dotnet_root: &Path, sdk: &str) -> (PathBuf, PathBuf) {
    let config = dotnet_root
        .join("sdk")
        .join(sdk)
        .join("dotnet.runtimeconfig.json");
    let json: serde_json::Value =
        serde_json::from_str(&host_fs::read_to_string(&config).unwrap()).unwrap();
    let framework = &json["runtimeOptions"]["framework"];
    assert_eq!(
        framework["name"].as_str(),
        Some("Microsoft.NETCore.App"),
        "{}: the SDK runs on another framework",
        config.display()
    );
    let wanted = framework["version"].as_str().expect("a framework version");
    let runtime = rolled_forward(
        &dotnet_root.join("shared").join("Microsoft.NETCore.App"),
        wanted,
    );
    let fxr = rolled_forward(&dotnet_root.join("host").join("fxr"), wanted);
    (runtime, fxr)
}

/// Every regular file under `dir`, links followed (a Nix install is a farm
/// of them), each directory entered once.
fn files_under(dir: &Path, out: &mut Vec<PathBuf>) {
    fn walk(dir: &Path, seen: &mut BTreeSet<PathBuf>, out: &mut Vec<PathBuf>) {
        let Ok(canonical) = host_fs::canonicalize(dir) else {
            return;
        };
        if !seen.insert(canonical) {
            return;
        }
        let Ok(entries) = host_fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let Ok(meta) = host_fs::metadata(&path) else {
                continue;
            };
            if meta.is_dir() {
                walk(&path, seen, out);
            } else if meta.is_file() {
                out.push(path);
            }
        }
    }
    walk(dir, &mut BTreeSet::new(), out);
}

/// Every MSBuild document under the SDK `sdk_dir` and among its verified
/// workload manifests: each file whose root element is `Project`.
fn sdk_documents(dotnet_root: &Path, sdk: &str) -> Vec<(PathBuf, String)> {
    let mut files = Vec::new();
    files_under(&dotnet_root.join("sdk").join(sdk), &mut files);
    for manifest in verified_manifests(sdk) {
        files.push(dotnet_root.join("sdk-manifests").join(manifest));
    }
    files.sort();
    files
        .into_iter()
        .filter_map(|file| {
            let bytes = host_fs::read(&file).unwrap_or_else(|e| panic!("{}: {e}", file.display()));
            let body = decoded(&bytes)?;
            // Any XML document whose root is `Project` is one MSBuild may
            // import, so one the walk's reader refuses fails the scan.
            let candidate = roxmltree::Document::parse_with_options(
                &body,
                roxmltree::ParsingOptions {
                    allow_dtd: true,
                    ..Default::default()
                },
            )
            .ok()?;
            if candidate.root_element().tag_name().name() != "Project" {
                return None;
            }
            if let Err(e) = document::parse(&body) {
                panic!(
                    "{} is an MSBuild document the scan cannot read: {e}",
                    file.display()
                );
            }
            Some((file, body))
        })
        .collect()
}

/// `bytes` as text: UTF-16 behind its byte-order mark, else UTF-8 (its mark
/// dropped), else `None`.
fn decoded(bytes: &[u8]) -> Option<String> {
    let utf16 = |rest: &[u8], unit: fn([u8; 2]) -> u16| {
        let units: Vec<u16> = rest
            .chunks(2)
            .map(|pair| unit([pair[0], *pair.get(1).unwrap_or(&0)]))
            .collect();
        String::from_utf16(&units).ok()
    };
    match bytes {
        [0xff, 0xfe, rest @ ..] => utf16(rest, u16::from_le_bytes),
        [0xfe, 0xff, rest @ ..] => utf16(rest, u16::from_be_bytes),
        _ => std::str::from_utf8(bytes)
            .ok()
            .map(|text| text.trim_start_matches('\u{feff}').to_string()),
    }
}

/// The texts of `node`'s attributes and of its text children, each as the
/// walk reads it (`document::attribute`, `document::text`) and as XML
/// normalises it, so neither reading's references are missed; and its text
/// children joined, with and without the whitespace-only ones: MSBuild reads
/// an element's text across its comments as one, and drops a whitespace-only
/// text node between two comments before it joins the rest
/// (`$<!--a--> <!--b-->(X)` reads `X`).
#[allow(clippy::disallowed_methods)] // the XML reading too, beside the walk's
fn texts(node: roxmltree::Node<'_, '_>) -> Vec<String> {
    let mut out: Vec<String> = node
        .attributes()
        .flat_map(|a| {
            let walk = document::attribute(node, a.name()).map(|v| v.into_owned());
            walk.into_iter().chain([a.value().to_string()])
        })
        .collect();
    let readings = |walk: bool| -> Vec<String> {
        node.children()
            .filter(roxmltree::Node::is_text)
            .filter_map(|t| {
                if walk {
                    document::text(t).map(|v| v.into_owned())
                } else {
                    t.text().map(str::to_string)
                }
            })
            .collect()
    };
    for pieces in [readings(true), readings(false)] {
        out.push(pieces.concat());
        out.push(
            pieces
                .iter()
                .filter(|p| !p.trim().is_empty())
                .map(String::as_str)
                .collect(),
        );
    }
    out
}

/// The literal text of `spec` before its first expansion.
fn literal_head(spec: &str) -> &str {
    let end = ["$(", "@(", "%("]
        .iter()
        .filter_map(|open| spec.find(open))
        .min()
        .unwrap_or(spec.len());
    &spec[..end]
}

/// The properties the SDK `sdk` reads, and the prefixes of the names it
/// computes (see the module documentation).
fn sdk_properties(dotnet_root: &Path, sdk: &str) -> (BTreeSet<String>, BTreeSet<String>) {
    let documents = sdk_documents(dotnet_root, sdk);
    assert!(
        documents.len() > 100,
        "found only {} MSBuild documents in the SDK {sdk}",
        documents.len()
    );
    let mut names = BTreeSet::new();
    let mut computed_from: BTreeSet<String> = BTreeSet::new();
    // Each item type's `Include`s, by lowercased type.
    let mut includes: BTreeMap<String, Vec<(PathBuf, String)>> = BTreeMap::new();
    for (file, text) in &documents {
        let doc = document::parse(text).unwrap();
        for node in doc.descendants().filter(roxmltree::Node::is_element) {
            if node
                .parent_element()
                .is_some_and(|p| p.tag_name().name() == "ItemGroup")
                && let Some(include) = document::attribute(node, "Include")
            {
                includes
                    .entry(node.tag_name().name().to_ascii_lowercase())
                    .or_default()
                    .push((file.clone(), include.into_owned()));
            }
            for text in texts(node) {
                for name in property_references(&text) {
                    names.insert(name.to_ascii_lowercase());
                }
                // A name the reference scan cannot see: `$(` before
                // something other than a name or a static call.
                for (at, _) in text.match_indices("$(") {
                    let interior = text[at + 2..].trim_start();
                    let computed = match interior.chars().next() {
                        Some('%') => {
                            let item = interior
                                .strip_prefix("%(")
                                .and_then(|rest| rest.split_once(')'))
                                .and_then(|(inside, _)| {
                                    inside
                                        .trim()
                                        .strip_suffix(".Identity")
                                        .map(|t| t.trim().to_ascii_lowercase())
                                });
                            match item {
                                Some(item) => {
                                    computed_from.insert(item);
                                    continue;
                                }
                                None => true,
                            }
                        }
                        Some('$' | '@') => true,
                        _ => false,
                    };
                    assert!(
                        !computed,
                        "{} reads a property whose name it computes in a way this scan \
                         cannot list: {text:?}",
                        file.display()
                    );
                }
            }
        }
    }
    let mut prefixes = BTreeSet::new();
    for item in &computed_from {
        let specs = includes.get(item).unwrap_or_else(|| {
            panic!("the SDK {sdk} reads properties named by @({item}), which it never declares")
        });
        for (file, spec) in specs {
            for part in spec.split(';').map(str::trim).filter(|p| !p.is_empty()) {
                let head = literal_head(part);
                assert!(
                    !head.trim().is_empty(),
                    "{} declares @({item}), whose identities name properties, as {part:?}: \
                     a name this scan cannot list",
                    file.display()
                );
                if head.len() == part.len() {
                    names.insert(part.to_ascii_lowercase());
                } else {
                    prefixes.insert(head.to_ascii_lowercase());
                }
            }
        }
    }
    (names, prefixes)
}

/// Whether `bytes` start like a native binary (Mach-O, fat, ELF).
fn native(bytes: &[u8]) -> bool {
    matches!(
        bytes.get(..4),
        Some([0xcf, 0xfa, 0xed, 0xfe] | [0xca, 0xfe, 0xba, 0xbe] | [0x7f, b'E', b'L', b'F'])
    )
}

/// Whether `s` is shaped like a conventional variable name: ASCII capitals,
/// digits and `_`, two or more, starting with a capital or `_`, one a
/// capital.
fn conventional(s: &str) -> bool {
    s.len() >= 2
        && s.starts_with(|c: char| c.is_ascii_uppercase() || c == '_')
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && s.chars().any(|c| c.is_ascii_uppercase())
}

/// The strings of `bytes` between two NULs (ASCII) or two UTF-16 NULs, each
/// [`conventional`].
fn native_strings(bytes: &[u8], out: &mut BTreeSet<String>) {
    for run in bytes.split(|b| *b == 0) {
        if let Ok(s) = std::str::from_utf8(run)
            && conventional(s)
        {
            out.insert(s.to_string());
        }
    }
    for offset in 0..2 {
        let units: Vec<u16> = bytes[offset..]
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| u16::from_le_bytes(*pair))
            .collect();
        for run in units.split(|u| *u == 0) {
            if let Ok(s) = String::from_utf16(run)
                && conventional(&s)
            {
                out.insert(s);
            }
        }
    }
}

/// The variables the build's tools may read under the SDK `sdk`, and the
/// prefixes of the names they compose (see the module documentation), with
/// how many environment reads the IL scan found and could not resolve.
fn tool_variables(dotnet_root: &Path, sdk: &str) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut files = Vec::new();
    let (runtime, fxr) = sdk_runtime(dotnet_root, sdk);
    files_under(&dotnet_root.join("sdk").join(sdk), &mut files);
    files_under(&runtime, &mut files);
    files_under(&fxr, &mut files);
    files.push(host_fs::canonicalize(dotnet_root.join("dotnet")).expect("the dotnet muxer"));
    files.sort();
    let mut variables = BTreeSet::new();
    let mut prefixes = BTreeSet::new();
    let mut managed = Vec::new();
    let mut natives = 0;
    for file in &files {
        let Ok(bytes) = host_fs::read(file) else {
            continue;
        };
        if native(&bytes) {
            natives += 1;
            let mut strings = BTreeSet::new();
            native_strings(&bytes, &mut strings);
            for s in strings {
                if s.ends_with('_') && s.len() >= 4 {
                    prefixes.insert(s.to_ascii_lowercase());
                }
                variables.insert(s.to_ascii_lowercase());
            }
        } else if bytes.starts_with(b"MZ") {
            managed.push(file.clone());
        }
    }
    let mut oracle = common::Oracle::spawn();
    let (mut assemblies, mut calls, mut unresolved) = (0, 0, 0);
    for chunk in managed.chunks(64) {
        for assembly in oracle.env_reads(chunk) {
            assemblies += 1;
            calls += assembly["envCalls"].as_u64().unwrap();
            unresolved += assembly["unresolved"].as_u64().unwrap();
            let strings = |key: &str| -> Vec<String> {
                assembly[key]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|s| s.as_str().unwrap().to_ascii_lowercase())
                    .collect()
            };
            variables.extend(strings("names"));
            variables.extend(strings("upper"));
            prefixes.extend(strings("prefixes"));
        }
    }
    eprintln!(
        "{sdk}: {natives} native binaries, {assemblies} managed assemblies, \
         {calls} environment reads ({unresolved} with no name in reach, whose \
         method's every string is listed)"
    );
    assert!(
        assemblies > 100 && natives > 3,
        "the scan found too little of the SDK {sdk}"
    );
    (variables, prefixes)
}

/// The scan of the installed SDK `sdk`, once per run: one scan per SDK
/// whichever tests ask for it, and however many at once.
fn scanned(sdk: &str) -> EnvironmentReads {
    static SCANS: OnceLock<Mutex<BTreeMap<String, std::sync::Arc<OnceLock<EnvironmentReads>>>>> =
        OnceLock::new();
    let cell = SCANS
        .get_or_init(Default::default)
        .lock()
        .unwrap()
        .entry(sdk.to_string())
        .or_default()
        .clone();
    cell.get_or_init(|| {
        let root = common::dotnet_root_from_env();
        assert!(
            installed(sdk),
            "the SDK {sdk} is not installed under {}",
            root.display()
        );
        let (properties, property_prefixes) = sdk_properties(&root, sdk);
        let (variables, variable_prefixes) = tool_variables(&root, sdk);
        EnvironmentReads {
            properties,
            property_prefixes,
            variables,
            variable_prefixes,
        }
    })
    .clone()
}

/// `reads` as the pinned file spells the sections of the SDK `sdk` on the
/// platform `platform`, by section header.
fn render(sdk: &str, platform: &str, reads: &EnvironmentReads) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for (list, set) in [
        ("properties", &reads.properties),
        ("property-prefixes", &reads.property_prefixes),
        ("variables", &reads.variables),
        ("variable-prefixes", &reads.variable_prefixes),
    ] {
        let mut section = String::new();
        for name in set {
            // What the file's reading takes for a name.
            assert!(
                !name.is_empty() && !name.contains(char::is_whitespace),
                "{sdk} {list}: {name:?} cannot be pinned"
            );
            section.push_str(name);
            section.push('\n');
        }
        out.insert(format!("[{sdk} {list} {platform}]"), section);
    }
    out
}

/// The sections of the pinned file's text, by header, in order.
fn sections(text: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        if line.is_empty() || line == "#" || line.starts_with("# ") {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') && line.contains(' ') {
            current = Some(line.to_string());
            out.insert(line.to_string(), String::new());
        } else if let Some(header) = &current {
            let section = out.get_mut(header).unwrap();
            section.push_str(line);
            section.push('\n');
        }
    }
    out
}

/// The SDK a section header names.
fn header_sdk(header: &str) -> &str {
    header
        .trim_start_matches('[')
        .split(' ')
        .next()
        .unwrap_or_default()
}

/// The platform a section header names.
fn header_platform(header: &str) -> &str {
    header
        .trim_end_matches(']')
        .split(' ')
        .nth(2)
        .unwrap_or_default()
}

/// Every installed SDK that must be pinned is, on this platform, exactly as
/// its scan reads it; every other one that must be pinned is, on some
/// platform. Regeneration rewrites this platform's sections of the installed
/// SDKs alone, keeping every other platform's and those of an SDK no longer
/// installed (a bump grades the new one before it retires the old), and
/// drops those of an SDK neither verified nor the devshell's.
#[test]
fn the_pinned_reads_are_each_sdk_s_own() {
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/fsc_environment_reads.txt");
    let sdks = sdks_to_pin();
    let platform = platform();
    let text = host_fs::read_to_string(&file).unwrap_or_default();
    let pinned = sections(&text);
    let scans: BTreeMap<String, String> = sdks
        .iter()
        .filter(|sdk| installed(sdk))
        .flat_map(|sdk| render(sdk, &platform, &scanned(sdk)))
        .collect();
    if std::env::var_os("BORZOI_UPDATE_MANIFESTS").is_some() {
        let header: String = text
            .lines()
            .take_while(|line| line.starts_with('#'))
            .map(|line| format!("{line}\n"))
            .collect();
        let mut all: BTreeMap<String, String> = pinned
            .into_iter()
            .filter(|(header, _)| {
                !header_platform(header).is_empty()
                    && sdks.contains(header_sdk(header))
                    && !(installed(header_sdk(header)) && header_platform(header) == platform)
            })
            .collect();
        all.extend(scans);
        let body: String = all
            .iter()
            .map(|(header, section)| format!("{header}\n{section}"))
            .collect();
        std::fs::write(&file, format!("{header}{body}")).unwrap();
        return;
    }
    let mut failures = Vec::new();
    for (header, scan) in &scans {
        match pinned.get(header) {
            None => failures.push(format!("{header}: not pinned")),
            Some(pin) if pin != scan => {
                let lines = |s: &str| s.lines().map(str::to_string).collect::<BTreeSet<_>>();
                let (pin, scan) = (lines(pin), lines(scan));
                let extra: Vec<_> = pin.difference(&scan).take(10).collect();
                let missing: Vec<_> = scan.difference(&pin).take(10).collect();
                failures.push(format!(
                    "{header}: pinned but not scanned {extra:?}; scanned but not pinned {missing:?}"
                ));
            }
            Some(_) => {}
        }
    }
    for sdk in sdks.iter().filter(|sdk| !installed(sdk)) {
        if !pinned.keys().any(|header| header_sdk(header) == sdk) {
            failures.push(format!("{sdk}: not installed, and pinned on no platform"));
        }
    }
    if !failures.is_empty() {
        // This platform's scan whole, for a platform the regenerating
        // machine is not: paste its sections into the file.
        eprintln!("the scan on {platform}:");
        for (header, section) in &scans {
            eprint!("{header}\n{section}");
        }
    }
    assert!(
        failures.is_empty(),
        "the pinned environment reads are not the SDKs' own; regenerate with\n  {REGENERATE}\n{}",
        failures.join("\n")
    );
}

/// The pin's lists are its sections' union over platforms, so a variable a
/// tool reads on one platform declines on every platform.
#[test]
fn the_lists_are_the_union_over_platforms() {
    let parsed = parse_environment_reads(
        "# a comment\n[9.0.100 variables linux-x86_64]\nonly_linux\nshared\n\
         [9.0.100 variables macos-aarch64]\nonly_macos\nshared\n\
         [9.0.100 properties macos-aarch64]\nassemblyname\n",
    );
    let reads = &parsed["9.0.100"];
    assert_eq!(
        reads.variables,
        BTreeSet::from(["only_linux".into(), "only_macos".into(), "shared".into()])
    );
    assert_eq!(reads.properties, BTreeSet::from(["assemblyname".into()]));
}

/// Every verified SDK's reads are pinned, so the derivation never commits
/// for one it cannot classify a variable under, and the pin holds nothing
/// else.
#[test]
fn every_verified_sdk_has_its_reads_pinned() {
    for sdk in verified_sdks() {
        assert!(
            environment_reads(sdk).is_some(),
            "{sdk} is verified but its environment reads are not pinned; {REGENERATE}"
        );
    }
    let devshell = devshell_sdk();
    for sdk in environment_read_sdks() {
        assert!(
            verified_sdks().any(|v| v == sdk) || sdk == devshell,
            "{sdk}'s environment reads are pinned, but it is neither verified nor the \
             devshell's; {REGENERATE}"
        );
    }
}

/// The scan finds the reads it is known to have to: a list that lost them
/// would admit what the build reads.
#[test]
fn the_scan_finds_the_known_reads() {
    let reads = scanned(&devshell_sdk());
    for property in [
        "targetframework",
        "defineconstants",
        "otherflags",
        "intermediateoutputpath",
        "targetname",
        "language",
        "nugetpackageroot",
    ] {
        assert!(
            reads.properties.contains(property),
            "the SDK reads {property}, but the scan did not find it"
        );
    }
    assert!(
        reads.property_prefixes.contains("pkg"),
        "FSharp's targets read `Pkg…` properties named from package references"
    );
    for variable in [
        // FSharp.Build
        "dotnet_host_path",
        "fsharp_compiler_bin",
        // fsc
        "fsharp_experimental_features",
        // NuGet
        "nuget_packages",
        "nuget_fallback_packages",
        // MSBuild, by an environment read and by a property getter
        "msbuildnoinprocnode",
        "msbuildtreatwarningsaserrors",
        "msbuilddisablefeaturesfromversion",
        // the CLI
        "dotnet_cli_telemetry_optout",
        // the host
        "dotnet_root",
    ] {
        assert!(
            reads.variables.contains(variable),
            "the build's tools read {variable}, but the scan did not find it"
        );
    }
    // What NuGet's restore files read, though no SDK file need.
    for name in ["ExcludeRestorePackageImports", "Language"] {
        assert_eq!(
            borzoi_msbuild::fsc::classify_variable(&devshell_sdk(), name),
            Some(borzoi_msbuild::fsc::VariableClass::SdkRead),
            "{name}"
        );
    }
    for prefix in ["dotnet_", "complus_", "nugetpackagesourcecredentials_"] {
        assert!(
            reads.variable_prefixes.contains(prefix),
            "the build's tools read variables named {prefix}…, but the scan did not find it"
        );
    }
}

/// A report, not a gate: how the derivation classifies each variable of an
/// environment, by name alone, under each verified SDK, and whether the
/// environment as a whole keeps an evaluation in the domain. The names are
/// read one a line from `BORZOI_ENV_NAMES_FILE`, else this process's own.
///
/// ```sh
/// BORZOI_ENV_NAMES_FILE=names.txt nix develop -c cargo test -p borzoi-msbuild \
///   --test fsc_environment_reads environment_census -- --ignored --nocapture
/// ```
#[test]
#[ignore = "a report over the environment named by BORZOI_ENV_NAMES_FILE"]
fn environment_census() {
    let names: Vec<String> = match std::env::var_os("BORZOI_ENV_NAMES_FILE") {
        Some(file) => host_fs::read_to_string(Path::new(&file))
            .unwrap()
            .lines()
            .filter(|l| !l.is_empty())
            .map(str::to_string)
            .collect(),
        None => std::env::vars().map(|(name, _)| name).collect(),
    };
    let environment: std::collections::HashMap<String, String> =
        names.iter().map(|n| (n.clone(), String::new())).collect();
    for sdk in verified_sdks() {
        let mut by_class: BTreeMap<String, Vec<&String>> = BTreeMap::new();
        for name in &names {
            let class = borzoi_msbuild::fsc::classify_variable(sdk, name);
            by_class.entry(format!("{class:?}")).or_default().push(name);
        }
        eprintln!("{sdk}: {} variables", names.len());
        for (class, mut names) in by_class {
            names.sort();
            eprintln!("  {class} ({}): {names:?}", names.len());
        }
        eprintln!(
            "  verdict: {:?}",
            borzoi_msbuild::fsc::environment_decline(sdk, &environment)
        );
    }
}
