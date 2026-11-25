//! List (a) of the compiled-name derivation's environment rule
//! ([`borzoi_msbuild::fsc::environment_reads`], pinned in
//! `src/fsc_environment_reads.txt`): every property a file of each verified
//! SDK reads, held to the SDK as installed, so an SDK bump fails here until
//! its reads are scanned and recorded. The files are the SDK's version
//! directory's every MSBuild document and its verified workload manifests;
//! a read is each `$(Name)` the crate's own reference scan
//! ([`borzoi_msbuild::test_support::property_references`], which never
//! under-reports) finds in an attribute or an element's text. A name the
//! SDK computes from an item's identity (`$(%(PropertyNames.Identity))`) is
//! each name that item type's declarations in the SDK give: a literal one
//! whole, else the literal text before its first expansion as a prefix. A
//! name computed any other way, or from a declaration that starts with an
//! expansion, cannot be listed, and fails the scan.
//!
//! The list's one use is a guard on grading: no name on
//! [`ALLOWED_ENVIRONMENT`], and none the oracle can set ([`INPUT_NAMES`]),
//! is a property an SDK file reads, unless it is an allowed property (held to
//! its grammar) or one of NuGet's restore-file guards (`NUGET_GUARDS`). A
//! name graded inert by sampling a few values must not be one some value of
//! which moves the build.
//!
//! Regenerate with
//! `BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test fsc_environment_reads`.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use borzoi_msbuild::document;
use borzoi_msbuild::fsc::{
    ALLOWED_ENVIRONMENT, ALLOWED_PROPERTIES, EnvironmentReads, TOOLCHAIN_VARIABLES,
    environment_read_sdks, environment_reads, parse_environment_reads, verified_manifests,
    verified_sdks,
};
use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::property_references;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::msbuild_oracle::{
    self, INPUT_NAMES, build_environment, msbuild_user_extensions_path,
};

const REGENERATE: &str = "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
                          --test fsc_environment_reads";

/// The SDK the devshell's `dotnet` resolves outside any `global.json`.
fn devshell_sdk() -> String {
    let tmp = tempfile::TempDir::new().unwrap();
    // The host the grading's builds run, launched as they launch it.
    let mut cmd = std::process::Command::new(msbuild_oracle::dotnet_host());
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

/// The workload manifest files of the SDK `sdk`: those its grading recorded
/// ([`verified_manifests`]), and those a plain project evaluated under it
/// loads, which an SDK not yet graded has no record of.
fn loaded_manifests(dotnet_root: &Path, sdk: &str) -> BTreeSet<String> {
    let mut manifests: BTreeSet<String> = verified_manifests(sdk).map(str::to_string).collect();
    // A plain project resolves the devshell's SDK; another one's loads are
    // its record alone.
    if sdk != devshell_sdk() {
        return manifests;
    }
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = host_fs::canonicalize(tmp.path()).unwrap();
    let project = dir.join("Probe.fsproj");
    std::fs::write(
        &project,
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
         <TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>",
    )
    .unwrap();
    let mut environment: std::collections::HashMap<String, String> =
        build_environment().into_iter().collect();
    environment.insert(
        "MSBuildUserExtensionsPath".to_string(),
        msbuild_user_extensions_path().to_string(),
    );
    let parsed =
        common::assembly_name::evaluate(&project, &Default::default(), &environment, dotnet_root)
            .expect("a plain project evaluates");
    manifests.extend(parsed.workload_manifest_files);
    manifests
}

/// Every MSBuild document under the SDK `sdk_dir` and among its workload
/// manifests ([`loaded_manifests`]): each file whose root element is
/// `Project`.
fn sdk_documents(dotnet_root: &Path, sdk: &str) -> Vec<(PathBuf, String)> {
    let mut files = Vec::new();
    files_under(&dotnet_root.join("sdk").join(sdk), &mut files);
    for manifest in loaded_manifests(dotnet_root, sdk) {
        files.push(dotnet_root.join("sdk-manifests").join(manifest));
    }
    files.sort();
    files
        .into_iter()
        .filter_map(|file| {
            let bytes = host_fs::read(&file).unwrap_or_else(|e| panic!("{}: {e}", file.display()));
            let Some(body) = decoded(&bytes) else {
                assert!(
                    !starts_like_xml(&bytes),
                    "{} looks like an XML document in an encoding this scan cannot read",
                    file.display()
                );
                return None;
            };
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

/// Whether `bytes`, which [`decoded`] cannot read, start like XML: a file
/// MSBuild may import in another encoding (it reads an XML encoding
/// declaration), whose reads would go unlisted. A binary (an assembly, a
/// native image) starts otherwise.
fn starts_like_xml(bytes: &[u8]) -> bool {
    bytes
        .iter()
        .position(|b| !b.is_ascii_whitespace())
        .is_some_and(|i| bytes[i] == b'<')
}

/// A Latin-1 project file is no text this scan decodes, and fails the scan;
/// an assembly holding the same bytes does not.
#[test]
fn an_undecodable_xml_document_fails_the_scan() {
    let latin1 = b"<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n<Project><PropertyGroup><X>\xe9$(Read)</X></PropertyGroup></Project>";
    assert_eq!(decoded(latin1), None);
    assert!(starts_like_xml(latin1));
    let assembly = b"MZ\x90\x00<Project\xff";
    assert_eq!(decoded(assembly), None);
    assert!(!starts_like_xml(assembly));
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

/// The text from the start of `after` (just past a `$(`) to the parenthesis
/// that closes it, nested ones counted, or `None` when none does (MSBuild
/// then reads the text as it stands).
fn parenthesised(after: &str) -> Option<&str> {
    let mut depth = 1usize;
    for (i, c) in after.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&after[..i]);
                }
            }
            _ => {}
        }
    }
    None
}

/// The name a property reference's interior reads: the text before its first
/// `.` or `:` outside parentheses (a property function or a member's start).
fn name_part(interior: &str) -> &str {
    let mut depth = 0usize;
    for (i, c) in interior.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            '.' | ':' if depth == 0 => return &interior[..i],
            _ => {}
        }
    }
    interior
}

/// A property whose name the SDK computes from an item's identity and more,
/// or from a name and an identity, is no shape the scan can list: it fails.
#[test]
fn computed_names_beyond_an_identity_fail_the_scan() {
    for (text, listed) in [
        ("$(%(PropertyNames.Identity))", true),
        ("$( %(PropertyNames.Identity) )", true),
        ("$(%(PropertyNames.Identity).Length)", true),
        ("$(%(PropertyNames.Identity)Bar)", false),
        ("$(Foo%(Names.Identity))", false),
        ("$($(Inner))", false),
        ("$(@(Items))", false),
    ] {
        let interior = parenthesised(&text[2..]).unwrap().trim();
        let name = name_part(interior).trim();
        let item = name
            .strip_prefix("%(")
            .and_then(|rest| rest.strip_suffix(')'))
            .and_then(|inside| inside.trim().strip_suffix(".Identity"))
            .map(str::trim)
            .filter(|item| !item.contains(['(', ')', '$', '@', '%', '.']));
        assert_eq!(item.is_some(), listed, "{text}");
    }
    assert_eq!(name_part("Foo.Replace('a', '$(B)')"), "Foo");
    assert_eq!(parenthesised("A) rest"), Some("A"));
    assert_eq!(parenthesised("unclosed"), None);
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
                // A name the reference scan cannot see: one computed from
                // an expansion anywhere in the name (before its first `.` or
                // `:` outside parentheses). The one shape listed is a name
                // that is exactly an item's identity.
                for (at, _) in text.match_indices("$(") {
                    let Some(interior) = parenthesised(&text[at + 2..]) else {
                        continue;
                    };
                    let interior = interior.trim();
                    if interior.starts_with('[') {
                        continue;
                    }
                    let name = name_part(interior).trim();
                    if !name.contains(['$', '@', '%']) {
                        continue;
                    }
                    let item = name
                        .strip_prefix("%(")
                        .and_then(|rest| rest.strip_suffix(')'))
                        .and_then(|inside| inside.trim().strip_suffix(".Identity"))
                        .map(str::trim)
                        .filter(|item| !item.contains(['(', ')', '$', '@', '%', '.']));
                    match item {
                        Some(item) => {
                            computed_from.insert(item.to_ascii_lowercase());
                        }
                        None => panic!(
                            "{} reads a property whose name it computes in a way this scan \
                             cannot list: {text:?}",
                            file.display()
                        ),
                    }
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
        EnvironmentReads {
            properties,
            property_prefixes,
        }
    })
    .clone()
}

/// `reads` as the pinned file spells the sections of the SDK `sdk`, by
/// section header.
fn render(sdk: &str, reads: &EnvironmentReads) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for (list, set) in [
        ("properties", &reads.properties),
        ("property-prefixes", &reads.property_prefixes),
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
        out.insert(format!("[{sdk} {list}]"), section);
    }
    out
}

/// The sections of the pinned file's text, by header.
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

/// Every installed SDK that must be pinned is, exactly as its scan reads it;
/// every other one that must be pinned is pinned. Regeneration rewrites the
/// sections of the installed SDKs, keeps those of an SDK that must be pinned
/// but is not installed (a bump grades the new one before it retires the
/// old), and drops those of an SDK neither verified nor the devshell's.
#[test]
fn the_pinned_reads_are_each_sdk_s_own() {
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/fsc_environment_reads.txt");
    let sdks = sdks_to_pin();
    let text = host_fs::read_to_string(&file).unwrap_or_default();
    let pinned = sections(&text);
    let scans: BTreeMap<String, String> = sdks
        .iter()
        .filter(|sdk| installed(sdk))
        .flat_map(|sdk| render(sdk, &scanned(sdk)))
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
                sdks.contains(header_sdk(header)) && !installed(header_sdk(header))
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
            failures.push(format!("{sdk}: not installed, and not pinned"));
        }
    }
    assert!(
        failures.is_empty(),
        "the pinned environment reads are not the SDKs' own; regenerate with\n  {REGENERATE}\n{}",
        failures.join("\n")
    );
}

/// The pin's file reads back as written: each list of each SDK, comments and
/// all.
#[test]
fn the_pin_parses_its_sections() {
    let parsed = parse_environment_reads(
        "# a comment\n[9.0.100 properties]\nassemblyname\nother\n\
         [9.0.100 property-prefixes]\npkg\n[9.0.200 properties]\nx\n",
    );
    let reads = &parsed["9.0.100"];
    assert_eq!(
        reads.properties,
        BTreeSet::from(["assemblyname".into(), "other".into()])
    );
    assert!(reads.reads("AssemblyName") && reads.reads("PkgFSharp_Core"));
    assert!(!reads.reads("Unread"));
    assert_eq!(parsed["9.0.200"].properties, BTreeSet::from(["x".into()]));
}

/// Every verified SDK's reads are pinned, so the derivation never commits
/// for one it cannot check a graded name against, and the pin holds nothing
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
/// would let a name some SDK file reads be graded inert.
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
        // Read from the environment by name in the SDK's own files.
        "temp",
        "source_date_epoch",
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
}

/// No name graded inert, and none the oracle can set, is a property a file of
/// a verified SDK reads, unless it is an allowed property (held to its
/// grammar) or a toolchain variable (held fixed). Grading a name by a few
/// values says nothing of one some value of which moves the build.
#[test]
fn no_graded_name_is_read_by_an_sdk_file() {
    let excepted = |name: &str| {
        ALLOWED_PROPERTIES
            .iter()
            .any(|(allowed, _)| allowed.eq_ignore_ascii_case(name))
            || TOOLCHAIN_VARIABLES
                .iter()
                .any(|(toolchain, _)| toolchain.eq_ignore_ascii_case(name))
    };
    let mut failures = Vec::new();
    for sdk in verified_sdks() {
        let reads =
            environment_reads(sdk).expect("pinned, by every_verified_sdk_has_its_reads_pinned");
        for name in ALLOWED_ENVIRONMENT.iter().chain(INPUT_NAMES) {
            if !excepted(name) && reads.reads(name) {
                failures.push(format!("{sdk}: {name} is graded, and an SDK file reads it"));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
