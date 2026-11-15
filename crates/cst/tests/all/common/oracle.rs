//! The two `fcs-dump` oracles, and which one grades a request.
//!
//! [`Oracle::Current`] is `tools/fcs-dump`, on the `FSharp.Compiler.Service`
//! package built from the compiler the feature table transcribes. That
//! compiler refuses every language version below [`ORACLE_SUPPORT_FLOOR`]
//! (FS3880, `LanguageVersion.IsVersionSupported`); the oracles lift the refusal
//! with `SKIP_VERSION_SUPPORTED_CHECK`, but below the floor it no longer
//! behaves as the older compilers did, because it deleted the features
//! introduced there (`docs/ast-versioning-plan.md`, D12). It answers every
//! request at or above the floor, and every request that names no version.
//!
//! [`Oracle::Legacy`] is `tools/fcs-dump-legacy`: a frozen copy of the oracle
//! on FCS 43.12.204, the last package before the deletions, never edited. It
//! answers every request below the floor. A request there always reaches a
//! retired gate: the lex-filter's offside rule below 8.0 is decided by the
//! retired `RelaxWhitespace`, `RelaxWhitespace2` and `StrictIndentation`
//! rows, so it governs every file. The legacy oracle is spawned only when a
//! request below the floor arrives, so a suite that never makes one never
//! builds or starts it.
//!
//! The two packages write a few AST shapes differently. [`upgrade_legacy_record`]
//! rewrites the legacy oracle's record into the current shapes, so the FCS
//! projection (`normalised_ast::from_fcs`) and the range audit read one shape.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::Duration;

use borzoi_cst::language_version::LanguageVersion;
use borzoi_oracle_harness::BoundedCommand;
use serde_json::{Value, json};

/// The lowest language version the current oracle's compiler supports: the
/// version `IsVersionSupported` compares against. It is
/// `borzoi_oracle_harness::FCS_SUPPORT_FLOOR`, which `language_features`
/// holds to the compiler's source.
pub const ORACLE_SUPPORT_FLOOR: LanguageVersion = LanguageVersion::V8_0;

/// One of the two `fcs-dump` builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Oracle {
    /// `tools/fcs-dump`.
    Current,
    /// `tools/fcs-dump-legacy`.
    Legacy,
}

impl Oracle {
    /// The oracle that grades a request at the `<LangVersion>` `lang_text`.
    ///
    /// # Panics
    ///
    /// Panics if `lang_text` is not a version FCS reads.
    pub fn for_lang_text(lang_text: &str) -> Oracle {
        let lang = LanguageVersion::from_lang_version_text(lang_text)
            .unwrap_or_else(|| panic!("{lang_text:?} is not a <LangVersion> FCS reads"));
        Oracle::for_version(lang)
    }

    /// The oracle that grades a request at `lang`.
    pub fn for_version(lang: LanguageVersion) -> Oracle {
        if lang < ORACLE_SUPPORT_FLOOR {
            Oracle::Legacy
        } else {
            Oracle::Current
        }
    }

    /// The tool's project directory under `tools/`.
    pub fn project_dir(self) -> PathBuf {
        super::workspace_root().join("tools").join(self.name())
    }

    /// The project's directory name, which is also its assembly name.
    fn name(self) -> &'static str {
        match self {
            Oracle::Current => "fcs-dump",
            Oracle::Legacy => "fcs-dump-legacy",
        }
    }

    /// The variable naming a prebuilt framework-dependent binary, which the
    /// harness then runs instead of building the project.
    fn prebuilt_variable(self) -> &'static str {
        match self {
            Oracle::Current => "BORZOI_FCS_DUMP",
            Oracle::Legacy => "BORZOI_FCS_DUMP_LEGACY",
        }
    }

    /// The executable: the prebuilt one its variable names, else the apphost
    /// [`ensure_built`] produces.
    pub fn bin(self) -> OsString {
        std::env::var_os(self.prebuilt_variable())
            .unwrap_or_else(|| ensure_built(self).as_os_str().to_os_string())
    }

    /// `<bin> <subcommand>`, its pipes and arguments left to the caller.
    pub fn command(self, subcommand: &str) -> Command {
        let mut c = Command::new(self.bin());
        c.arg(subcommand);
        c
    }

    /// A one-shot `ast` record for `source` at the `<LangVersion>` `lang_text`,
    /// in the current oracle's shapes ([`upgrade_legacy_record`]).
    pub fn ast_at(self, source: &Path, lang_text: &str) -> String {
        let mut cmd = self.command("ast");
        cmd.arg(source);
        cmd.env("BORZOI_FCS_LANGVERSION", lang_text);
        let out = BoundedCommand::new(cmd).run_ok(format_args!(
            "{} ast (langversion {lang_text})",
            self.name()
        ));
        let json = String::from_utf8(out.stdout).expect("fcs-dump stdout is UTF-8");
        match self {
            Oracle::Current => json,
            Oracle::Legacy => upgrade_legacy_record(&json),
        }
    }
}

/// Build `oracle`'s project (when no prebuilt binary is named) and return the
/// path to the produced **apphost** — the directly-executable native launcher
/// sitting next to the `.dll` — so callers exec it without the `dotnet`
/// front-end.
///
/// A per-process `OnceLock` alone would re-run `dotnet build` once per test
/// binary (~2 s apiece). This crate is a single binary (`tests/all/`), but the
/// *other* crates' harnesses build the current oracle too, and a plain `cargo
/// test` runs their binaries back to back — so the gate still earns its keep.
/// To avoid the rebuild while staying correct, it is a **single** marker file
/// (`bin/.fcs-dump-built`) whose *contents* are the source hash
/// ([`source_fingerprint`]) of the apphost currently on disk. The build runs
/// only when that recorded hash doesn't match the current sources (or the
/// apphost is missing); otherwise the binary skips straight to exec.
///
/// The marker records the *built output's* hash rather than merely "some build
/// with this hash once happened" — because the apphost is one mutable file, so
/// a per-hash marker would be unsound: after building hash A then hash B (which
/// overwrites the apphost), reverting/branch-switching back to A would find a
/// stale `built-A` marker and skip the build, running the B binary as the
/// oracle for A's sources. One content-bearing marker makes a revert mismatch
/// (recorded B ≠ wanted A) and correctly rebuild. The oracle is thus always
/// fresh, unlike pinning a binary path in the devshell.
///
/// Cargo runs test binaries serially, so the first-builds / rest-skip handoff
/// needs no inter-process lock; the marker write is atomic (temp + rename) so a
/// partially-written hash can never read as a match.
fn ensure_built(oracle: Oracle) -> &'static Path {
    static CURRENT: OnceLock<PathBuf> = OnceLock::new();
    static LEGACY: OnceLock<PathBuf> = OnceLock::new();
    let cell = match oracle {
        Oracle::Current => &CURRENT,
        Oracle::Legacy => &LEGACY,
    };
    cell.get_or_init(|| {
        let project = oracle.project_dir();
        let bin = project.join("bin");
        let apphost = bin.join("Release").join("net10.0").join(oracle.name());
        let marker = bin.join(".fcs-dump-built");
        let want = format!("{:016x}", source_fingerprint(&project));

        let fresh = apphost.exists()
            && std::fs::read_to_string(&marker)
                .map(|recorded| recorded.trim() == want)
                .unwrap_or(false);
        if !fresh {
            let mut cmd = Command::new("dotnet");
            cmd.args(["build", "-c", "Release", "--nologo"])
                .arg(&project);
            // Generous, but bounded: a cold build (restore + compile against
            // FCS) is legitimately minutes, while a *stalled* one — say,
            // blocked on a NuGet lock held by a concurrent run in a sibling
            // worktree — would otherwise hang the suite forever.
            BoundedCommand::new(cmd)
                .timeout(Duration::from_secs(1800))
                .run_ok(format_args!("dotnet build {}", oracle.name()));
            assert!(
                apphost.exists(),
                "dotnet build {} produced no apphost at {apphost:?}",
                oracle.name()
            );
            // Write the marker only after a successful build, so it always
            // names the hash of the apphost actually on disk.
            write_marker_atomically(&marker, &want);
        }
        apphost
    })
    .as_path()
}

/// Hash the inputs whose change should force a rebuild: the tool's own sources
/// (`*.fs` / `*.fsproj`) and the flake lock (which pins the SDK and thus the
/// FCS package set). A plain non-cryptographic content hash — just a freshness
/// key for the build marker — so editing the oracle reliably invalidates a
/// prior build. Missing files hash as empty, keeping the fingerprint defined
/// when run outside a Nix checkout.
fn source_fingerprint(project: &Path) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut sources: Vec<PathBuf> = std::fs::read_dir(project)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            matches!(
                p.extension().and_then(|s| s.to_str()),
                Some("fs" | "fsproj")
            )
        })
        .collect();
    sources.sort();
    sources.push(super::workspace_root().join("flake.lock"));

    let mut h = DefaultHasher::new();
    for p in &sources {
        // File name first so a rename can't alias two contents to one hash.
        p.file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .hash(&mut h);
        std::fs::read(p).unwrap_or_default().hash(&mut h);
    }
    h.finish()
}

/// Write `contents` to `marker` atomically: write a pid-tagged sibling temp
/// file and rename it into place, so a reader never observes a half-written
/// hash. Best-effort — any failure just means the next test binary rebuilds
/// (still correct, only slower).
fn write_marker_atomically(marker: &Path, contents: &str) {
    let Some(dir) = marker.parent() else {
        return;
    };
    let tmp = dir.join(format!(".fcs-dump-built.tmp-{}", std::process::id()));
    if std::fs::write(&tmp, contents).is_ok() && std::fs::rename(&tmp, marker).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
}

/// The legacy oracle's `ast` record `json`, its tree rewritten into the
/// current oracle's shapes. Each rewrite is one change to `SyntaxTree.fsi`
/// between the two packages:
///
/// - `SynComponentInfo.longId: LongIdent` became `synType: SynType option`; a
///   name is `Some(SynType.LongIdent(SynLongIdent(path, [], [])))`, as the
///   current parser builds a module head, and no name is `None`.
/// - A record type's `SynField list` became a `SynFieldOrSpread list`; each
///   field is wrapped in `Field`.
/// - `SynExprRecordField` lost its `blockSeparator`, which moved to the
///   `SynExprRecordFieldOrSpread.Field` that now wraps it.
/// - An anonymous record expression's `(SynLongIdent * range option *
///   SynExpr)` fields became `SynExprAnonRecordFieldOrSpread.Field`s over
///   `SynExprAnonRecordField(fieldName, equalsRange, expr, range)`, with no
///   separator. The legacy record has no field range, so it is `null`, which
///   no reader reads.
/// - `FillExpr`'s `qualifiers: Ident option` became `formatting:
///   SynInterpolationFormatting`. The qualifier becomes `DotNet(None,
///   qualifier)` and the hole is left as parsed: the projection folds the
///   current oracle's alignment and printf split back into exactly that form
///   (`from_fcs::fcs_interp_parts`), so the two read alike although the
///   current oracle would have split `{x,5}` and `%d{x}`.
///
/// `DebugPointAtLeafExpr.Yes` also gained a field; no reader reads debug
/// points, so it is left alone.
pub fn upgrade_legacy_record(json: &str) -> String {
    let mut record = super::fcs_record::read_fcs_record(json);
    if let Some(tree) = record.get_mut("ParseTree") {
        upgrade(tree);
    }
    serde_json::to_string(&record).expect("an upgraded fcs-dump record serialises")
}

/// Rewrite `v` and everything under it, children first.
fn upgrade(v: &mut Value) {
    match v {
        Value::Array(items) => items.iter_mut().for_each(upgrade),
        Value::Object(map) => {
            map.values_mut().for_each(upgrade);
            let case = map.get("Case").and_then(Value::as_str).map(str::to_owned);
            let Some(case) = case else { return };
            let Some(Value::Array(fields)) = map.get_mut("Fields") else {
                return;
            };
            upgrade_case(&case, fields);
            if case == "SynExprRecordField" && fields.len() == 5 {
                let separator = fields.pop().expect("five fields");
                let field = json!({ "Case": "SynExprRecordField", "Fields": fields.clone() });
                *v = json!({ "Case": "Field", "Fields": [field, separator] });
            }
        }
        _ => {}
    }
}

/// The in-place rewrites of one union case's `fields`.
fn upgrade_case(case: &str, fields: &mut [Value]) {
    match case {
        "SynComponentInfo" => {
            let long_id = std::mem::take(&mut fields[3]);
            let Value::Array(path) = long_id else {
                panic!("legacy SynComponentInfo.longId is not a list: {long_id}");
            };
            fields[3] = if path.is_empty() {
                Value::Null
            } else {
                json!({
                    "Case": "Some",
                    "Fields": [{
                        "Case": "LongIdent",
                        "Fields": [{ "Case": "SynLongIdent", "Fields": [path, [], []] }],
                    }],
                })
            };
        }
        // `SynTypeDefnSimpleRepr.Record(accessibility, recordFields, range)`:
        // three fields, the second a list of `SynField`s. `SynExpr.Record` has
        // four and `SynPat.Record` two.
        "Record" if fields.len() == 3 && is_list_of(&fields[1], "SynField") => {
            for field in fields[1].as_array_mut().expect("a list") {
                *field = json!({ "Case": "Field", "Fields": [std::mem::take(field)] });
            }
        }
        // `SynExpr.AnonRecd(isStruct, copyInfo, recordFields, range, trivia)`:
        // five fields. `SynType.AnonRecd` has three.
        "AnonRecd" if fields.len() == 5 => {
            for field in fields[2].as_array_mut().expect("AnonRecd recordFields") {
                let Value::Array(mut tuple) = std::mem::take(field) else {
                    panic!("legacy AnonRecd field is not a (name, mEquals, expr) tuple");
                };
                tuple.push(Value::Null);
                let inner = json!({ "Case": "SynExprAnonRecordField", "Fields": tuple });
                *field = json!({ "Case": "Field", "Fields": [inner, Value::Null] });
            }
        }
        "FillExpr" => {
            let qualifier = std::mem::take(&mut fields[1]);
            fields[1] = json!({ "Case": "DotNet", "Fields": [Value::Null, qualifier] });
        }
        _ => {}
    }
}

/// Whether `v` is a non-empty list whose items are all the union case `case`.
fn is_list_of(v: &Value, case: &str) -> bool {
    v.as_array().is_some_and(|items| {
        !items.is_empty()
            && items
                .iter()
                .all(|item| item.get("Case").and_then(Value::as_str) == Some(case))
    })
}

#[test]
fn the_routing_floor_is_the_harnesses_floor() {
    assert_eq!(
        ORACLE_SUPPORT_FLOOR.to_string(),
        borzoi_oracle_harness::FCS_SUPPORT_FLOOR
    );
}
