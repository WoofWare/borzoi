//! A revision's walk over the points `path_fixup_expansion_diff`'s fixed seed
//! generates, recorded so that the sweep can hold the walk under test to it:
//! a claim the baseline made rightly, or declined, must not be one the walk
//! under test makes wrongly.
//!
//! `tools/path-fixup-baseline.sh <revision>` runs this file in a checkout of
//! the baseline revision, over the points the sweep dumped
//! (`BORZOI_PATH_FIXUP_DUMP`), and writes
//! `tests/manifests/path_fixup_baseline.txt`. It reads the walk only through
//! the crate's public surface, and lays out the sweep's fixture itself, so
//! that it builds at a revision older than the sweep.

#![cfg(unix)]

mod common;

use std::collections::HashMap;
use std::path::PathBuf;

use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::test_support::{EvaluationReads, ReadProbe, parse_fsproj_reads};
use borzoi_msbuild::{GlobResolver, ItemKind, ParsedProject, PropertyRead, glob_resolver};

/// The fixture's working directories, as the sweep lays them out, and the
/// relative segments each holds.
const DIRECTORIES: &[(&str, &[&str])] = &[
    ("cwd-empty", &[]),
    ("cwd-full", &["seg", "obj"]),
    ("cwd-seg", &["seg"]),
    ("cwd-obj", &["obj"]),
    ("proj-full", &["seg", "obj"]),
    ("proj-empty", &[]),
];

/// Files under `proj-full`'s segments, and beside both projects.
const ITEM_FILES: &[&str] = &["seg/a.fs", "seg/b c.fs", "obj/a.fs"];

/// Each project's starts, as the sweep evaluates it from them.
fn starts_of(project: &str) -> [&'static str; 5] {
    match project {
        "proj-full" => ["cwd-empty", "cwd-full", "cwd-seg", "cwd-obj", "proj-full"],
        "proj-empty" => ["cwd-empty", "cwd-full", "cwd-seg", "cwd-obj", "proj-empty"],
        other => panic!("no project {other}"),
    }
}

#[test]
#[ignore = "run by tools/path-fixup-baseline.sh in a checkout of the baseline revision"]
fn record_baseline() {
    let dump = PathBuf::from(
        std::env::var("BORZOI_PATH_FIXUP_DUMP").expect("BORZOI_PATH_FIXUP_DUMP names the dump"),
    );
    let tmp = tempfile::Builder::new()
        .tempdir_in(fixture_parent())
        .unwrap();
    // One level inside the temporary directory, as the sweep lays it out.
    let root = host_fs::canonicalize(tmp.path()).unwrap().join("fixture");
    std::fs::create_dir(&root).unwrap();
    let root_text = root.to_str().unwrap().to_owned();
    for (dir, segments) in DIRECTORIES {
        std::fs::create_dir_all(root.join(dir)).unwrap();
        for segment in *segments {
            std::fs::create_dir_all(root.join(dir).join(segment)).unwrap();
        }
    }
    for file in ITEM_FILES {
        std::fs::write(root.join("proj-full").join(file), "").unwrap();
    }
    for dir in ["proj-full", "proj-empty"] {
        std::fs::write(root.join(dir).join("a.fs"), "").unwrap();
    }
    let uext = common::oracle_environment()
        .get("MSBuildUserExtensionsPath")
        .cloned()
        .unwrap_or_default();
    let parent_text = root
        .parent()
        .and_then(std::path::Path::to_str)
        .unwrap_or(&root_text)
        .to_owned();
    let unplace = |text: &str| {
        text.replace("{ROOT}", &root_text)
            .replace("{TMP}", &parent_text)
            .replace("{UEXT}", &uext)
    };
    // A claim is recorded in the sweep's spelling, the root and the host's
    // `MSBuildUserExtensionsPath` placeholders, so that it compares on any
    // host.
    let place = |claim: Option<Vec<String>>| {
        claim.map(|values| {
            values
                .into_iter()
                .map(|value| {
                    let value = value
                        .replace(&root_text, "{ROOT}")
                        .replace(&parent_text, "{TMP}");
                    if uext.is_empty() {
                        value
                    } else {
                        value.replace(&uext, "{UEXT}")
                    }
                })
                .collect::<Vec<_>>()
        })
    };
    let mut env = common::oracle_environment();
    let env_text = host_fs::read_to_string(dump.join("env.txt")).unwrap();
    for line in env_text.lines() {
        let (name, value) = line.split_once('\t').expect("a name and a value");
        env.insert(name.to_owned(), unplace(&unescape(value)));
    }
    let mut cases: Vec<(String, PathBuf)> = host_fs::read_dir(&dump)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|e| e == "xml"))
        .map(|path| {
            (
                path.file_stem().unwrap().to_string_lossy().into_owned(),
                path,
            )
        })
        .collect();
    cases.sort();
    assert!(!cases.is_empty(), "no point dumped in {}", dump.display());
    let globs = Some(&glob_resolver::resolve as &GlobResolver<'_>);
    let probe = ReadProbe {
        item_types: vec!["Foo".to_owned()],
        ..ReadProbe::default()
    };
    let mut out = String::new();
    for (key, path) in cases {
        let text = host_fs::read_to_string(&path).unwrap();
        let meta = host_fs::read_to_string(path.with_extension("meta")).unwrap();
        let (mut project, mut read, mut globals) = (String::new(), String::new(), Vec::new());
        for line in meta.lines() {
            let mut fields = line.splitn(3, '\t');
            match fields.next() {
                Some("project") => project = fields.next().unwrap().to_owned(),
                Some("read") => read = fields.collect::<Vec<_>>().join("\t"),
                Some("global") => {
                    let name = fields.next().unwrap().to_owned();
                    globals.push((name, unplace(&unescape(fields.next().unwrap()))));
                }
                other => panic!("{key}: unknown meta line {other:?}"),
            }
        }
        // A document spells the fixture's paths in XML.
        let xml = text
            .replace("{ROOT}", &xml_attribute(&root_text))
            .replace("{TMP}", &xml_attribute(&parent_text))
            .replace("{UEXT}", &xml_attribute(&uext));
        let extra: HashMap<String, String> = globals.into_iter().collect();
        let project_path = root.join(&project).join("Demo.fsproj");
        let file = borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
            .expect("a project path spelt as its full path");
        let with_imports = common::parse_fsproj_with_imports(&file, &extra, &env, None, globs).ok();
        let served_reads = parse_fsproj_reads(&file, &extra, &env, None, globs, None, &probe).ok();
        let pure = borzoi_msbuild::parse_fsproj(&file, &extra, &env).ok();
        // Every generated input, hashed as the sweep's `point_fingerprint`.
        let fingerprint = fnv1a(&format!("{text}\n--\n{meta}\n--\n{env_text}"));
        let mut row = format!("{key}\t{fingerprint}");
        let mut push = |mode: &str, claim: Option<Vec<String>>| {
            row.push_str(&format!("\t{mode} {}", encode_claim(&place(claim))));
        };
        push(
            "wi",
            with_imports.as_ref().and_then(|p| claim(p, None, &read)),
        );
        push(
            "rd",
            served_reads
                .as_ref()
                .and_then(|(p, r)| claim(p, Some(r), &read)),
        );
        push("pu", pure.as_ref().and_then(|p| claim(p, None, &read)));
        for label in starts_of(&project) {
            let dir = root.join(label);
            let supplied =
                parse_fsproj_reads(&file, &extra, &env, None, globs, Some(&dir), &probe).ok();
            push(
                &format!("s:{label}"),
                supplied
                    .as_ref()
                    .and_then(|(p, r)| claim(p, Some(r), &read)),
            );
        }
        out.push_str(&row);
        out.push('\n');
    }
    std::fs::write(dump.join("baseline.txt"), out).unwrap();
}

/// Where the fixture's temporary directory goes, as the sweep puts it: the host's, where its
/// spelling is plain, else `/tmp`. Its path is written into generated
/// documents (a `'` would end a condition's operand, a `&` begin an entity),
/// so a spelling that changed their grammar would change the points, and the
/// manifests would measure the host rather than the walk.
fn fixture_parent() -> PathBuf {
    // Checked as the documents spell it: canonical, past any symbolic link.
    let host = host_fs::canonicalize(std::env::temp_dir()).unwrap_or_else(|_| std::env::temp_dir());
    let plain = host.to_str().is_some_and(|text| {
        text.chars()
            .all(|c| c.is_ascii_alphanumeric() || "/._-".contains(c))
    });
    if plain { host } else { PathBuf::from("/tmp") }
}

/// What one evaluation claims about the point, as the sweep reads it.
fn claim(
    parsed: &ParsedProject,
    reads: Option<&EvaluationReads>,
    read: &str,
) -> Option<Vec<String>> {
    if let Some(name) = read.strip_prefix("property\t") {
        return match parsed.property(name) {
            PropertyRead::Value(value) => Some(vec![value]),
            PropertyRead::Unset => Some(vec![String::new()]),
            _ => None,
        };
    }
    match read {
        "items" => (!parsed.items_uncertain && parsed.rejection.is_none()).then(|| {
            parsed
                .items
                .iter()
                .filter(|item| item.kind == ItemKind::Compile)
                .map(|item| item.include.to_string_lossy().into_owned())
                .collect()
        }),
        "identities" => {
            let list = reads?.items.get("Foo")?;
            (list.exact && !list.tainted && !list.untracked && parsed.rejection.is_none())
                .then_some(list.items.as_ref())
                .flatten()
                .map(|rows| rows.iter().map(|row| row.identity.clone()).collect())
        }
        other => panic!("no read {other}"),
    }
}

/// The sweep's encoding of a claim (`encode_claim` there).
fn encode_claim(claim: &Option<Vec<String>>) -> String {
    match claim {
        None => "-".to_owned(),
        Some(values) => {
            let mut out = String::from("=");
            for value in values {
                out.push('|');
                out.push_str(
                    &value
                        .escape_default()
                        .to_string()
                        .replace(' ', "\\x20")
                        .replace('|', "\\x7c"),
                );
            }
            out
        }
    }
}

/// XML text for an attribute value, as the sweep writes one.
fn xml_attribute(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('"', "&quot;")
}

/// The inverse of Rust's `escape_default` over the escapes it writes.
fn unescape(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('0') => out.push('\0'),
            Some('u') => {
                let code: String = chars.by_ref().skip(1).take_while(|&c| c != '}').collect();
                out.push(char::from_u32(u32::from_str_radix(&code, 16).unwrap()).unwrap());
            }
            Some(other) => out.push(other),
            None => out.push('\\'),
        }
    }
    out
}

/// FNV-1a over `text`'s bytes, as hex: the sweep's key for a point's text.
fn fnv1a(text: &str) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    format!("{hash:016x}")
}
