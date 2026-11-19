//! `fcs-dump`'s resident ops under hostile input: the wire, and the files a
//! project-check request names.
//!
//! `fcs-dump`'s `…-batch` ops read one request per line and write one answer
//! line, matched by position, so a request read as none or as several moves
//! every later answer onto the wrong request. A resident child also outlives
//! the files it read, so an answer may come from what a file held before.
//! Two censuses hold the boundary:
//!
//! - **`fcs_dump_wire`** sends every [`hostile::wire::mutations`] entry of a
//!   good request to each op that reads JSON (`file-batch`,
//!   `uses-project-batch`, `xmldoc-batch`). The driver
//!   ([`BatchChild::try_request`]) must refuse, sending nothing, what cannot
//!   be one request line; everything else it sends. The oracle must answer
//!   each line it reads with one answer, never crash or hang, and stay in
//!   step: the good request sent next gets exactly what a fresh child gives
//!   it. What each line must get is [`expected_for_line`].
//! - **`fcs_dump_project`** puts a small project (two sources and a
//!   referenced assembly) to `uses-project-batch` with each file-system state
//!   at a source's path and at the reference's, each change made to a source
//!   and to the reference between two requests, each hostile name for a
//!   source (alone, and beside its twin), each spelling of a source's path
//!   and of the reference's after a change the stamp does not show, and each
//!   source-text mutation. The resident child must answer exactly as a fresh
//!   child answers the same world, and a successful answer must describe the
//!   files as they are ([`check_records`]).
//!
//! Both are `#[ignore]`d because they drive FCS, as this crate's other FCS
//! tests are; the whole-project gate runs them.

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::Mutex;
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::time::Duration;

use borzoi_corpus_diff::fcs_dump_command;
use borzoi_oracle_harness::hostile::fs::{Change, HostileFs, State, Unmakeable};
use borzoi_oracle_harness::hostile::name::{self, Name, Rendered};
use borzoi_oracle_harness::hostile::source::{self, Mutation};
use borzoi_oracle_harness::hostile::spelling::{self, Spelling};
use borzoi_oracle_harness::hostile::{Dimension, Entry, coverage, wire};
use borzoi_oracle_harness::{BatchChild, BatchFailure};
use serde_json::{Value, json};

/// The bound on one answer. A tiny project checks in a second or two; this
/// bounds "never answers", on a loaded machine.
const ANSWER_TIMEOUT: Duration = Duration::from_secs(300);

/// The bound on one answer to a request line of the wire census, whose
/// project is checked once warm and every other line of which is refused
/// before any check: a line the oracle reads as no request waits this long.
const WIRE_TIMEOUT: Duration = Duration::from_secs(60);

/// The command that regenerates both censuses' manifests.
const REGENERATE: &str = "BORZOI_UPDATE_MANIFESTS=1 cargo test -p borzoi-corpus-diff --test \
                          project_resolution fcs_dump_boundary:: -- --ignored";

/// The `fcs-dump` command for `op`, located once per process.
fn command(op: &str) -> Command {
    fcs_dump_command(op).unwrap_or_else(|e| panic!("locate fcs-dump {op}: {e}"))
}

/// A resident `op` child behind the driver every harness uses, one attempt
/// per request: a retry would hide a hang behind a second child.
fn driver(op: &str) -> BatchChild {
    driver_within(op, ANSWER_TIMEOUT)
}

/// [`driver`], each answer bounded by `timeout`.
fn driver_within(op: &str, timeout: Duration) -> BatchChild {
    let built = command(op);
    let program = built.get_program().to_os_string();
    let args: Vec<OsString> = built.get_args().map(OsString::from).collect();
    BatchChild::with_factory(
        Box::new(move || {
            let mut cmd = Command::new(&program);
            cmd.args(&args);
            cmd
        }),
        format!("fcs-dump {op}"),
        timeout,
        1,
    )
}

/// A fresh `op` child's answer to `request`: what no earlier request can
/// have influenced.
fn fresh_answer(op: &str, request: &str) -> Result<String, BatchFailure> {
    driver(op).try_request(request)
}

/// The message of a refusal (`{"BatchError": …}`), or `None` for an answer.
///
/// # Panics
///
/// If the line is not one JSON object: the oracle wrote something that is no
/// answer at all.
fn refusal(line: &str) -> Option<String> {
    let value: Value =
        serde_json::from_str(line).unwrap_or_else(|e| panic!("an answer is JSON ({e}): {line}"));
    let object = value
        .as_object()
        .unwrap_or_else(|| panic!("an answer is an object: {line}"));
    object.get("BatchError").map(|message| {
        assert_eq!(object.len(), 1, "a refusal holds only its message: {line}");
        let message = message
            .as_str()
            .unwrap_or_else(|| panic!("a refusal's message is text: {line}"));
        assert!(
            !message.trim().is_empty(),
            "a refusal names its reason: {line}"
        );
        message.to_owned()
    })
}

// ---------------------------------------------------------------------------
// The wire.
// ---------------------------------------------------------------------------

/// An `fcs-dump` child spoken to in raw bytes, for the lines no driver should
/// send: what the oracle does with them is the oracle's half of the contract.
struct RawChild {
    child: Child,
    stdin: ChildStdin,
    answers: Receiver<String>,
}

impl RawChild {
    fn spawn(op: &str) -> Self {
        let mut cmd = command(op);
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        let mut child = borzoi_spawn::spawn_serialised(&mut cmd)
            .unwrap_or_else(|e| panic!("start fcs-dump {op}: {e}"));
        let stdin = child.stdin.take().expect("piped stdin");
        let stdout = child.stdout.take().expect("piped stdout");
        let (tx, answers) = mpsc::channel();
        std::thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        if tx.send(line).is_err() {
                            break;
                        }
                    }
                }
            }
        });
        RawChild {
            child,
            stdin,
            answers,
        }
    }

    /// Write `bytes` and a line feed.
    fn send(&mut self, bytes: &[u8]) {
        self.stdin
            .write_all(bytes)
            .and_then(|()| self.stdin.write_all(b"\n"))
            .and_then(|()| self.stdin.flush())
            .expect("write to the oracle");
    }

    /// The next answer line.
    fn answer(&self) -> Result<String, String> {
        match self.answers.recv_timeout(WIRE_TIMEOUT) {
            Ok(line) => Ok(line),
            Err(RecvTimeoutError::Timeout) => Err(format!("no answer within {WIRE_TIMEOUT:?}")),
            Err(RecvTimeoutError::Disconnected) => Err("the oracle closed its output".into()),
        }
    }

    /// Whether an answer is waiting that no line asked for.
    fn stray(&self) -> Option<String> {
        self.answers.recv_timeout(Duration::from_millis(200)).ok()
    }
}

impl Drop for RawChild {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// The lines the oracle reads from `bytes` and the line feed after them: a
/// line ends at a line feed, and a carriage return just before one is the
/// line end's. A carriage return anywhere else is part of the line (JSON
/// whitespace, between tokens).
fn oracle_lines(bytes: &[u8]) -> Vec<Vec<u8>> {
    let terminated: Vec<u8> = [bytes, b"\n"].concat();
    let mut lines: Vec<Vec<u8>> = terminated
        .split(|b| *b == b'\n')
        .map(|line| line.strip_suffix(b"\r").unwrap_or(line).to_vec())
        .collect();
    // What follows the last line feed is no line.
    lines.pop();
    lines
}

/// Whether the driver must refuse `text`: it is no request line, being blank
/// (as .NET's `String.Trim` sees blankness) or holding a line feed or a
/// carriage return (each a line end to some line reader).
fn not_one_line(text: &str) -> bool {
    text.trim().is_empty() || text.contains(['\n', '\r'])
}

/// The fields every op takes that may be left out, with the value leaving one
/// out means. A good request carries each at that value, so that leaving one
/// out is the same request.
fn default_of(field: &str) -> Option<Value> {
    match field {
        "refs" | "defines" => Some(json!([])),
        "langversion" => Some(Value::Null),
        "exclusiveRefs" => Some(json!(false)),
        _ => None,
    }
}

/// What a line the oracle reads must get.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expect {
    /// A refusal on that line.
    Error,
    /// The good request's answer: the line is the good request, or differs
    /// from it only by leaving out a field at its default.
    SameAnswer,
}

/// What the oracle owes `line`, one of the lines of a mutation of
/// `dimension` derived from the request `good`.
///
/// Every dimension is refused except where the line is the good request
/// (one of the two requests a [`Dimension::MultiLine`] entry puts on one
/// line, or the request with a carriage return between its tokens, which is
/// JSON whitespace) or leaves out an optional field the good request holds
/// at its default ([`Dimension::MissingField`], [`default_of`]). In
/// particular a line with Unicode whitespace around the JSON is refused, not
/// trimmed: a reader that trims takes it for a request that a strict one
/// refuses.
fn expected_for_line(dimension: Dimension, line: &[u8], good: &Value) -> Expect {
    match dimension {
        Dimension::MultiLine
            if serde_json::from_slice::<Value>(line).ok().as_ref() == Some(good) =>
        {
            Expect::SameAnswer
        }
        Dimension::MissingField => {
            let mutated: Value = serde_json::from_slice(line).expect("a missing field is JSON");
            let missing: Vec<&String> = good
                .as_object()
                .expect("an object")
                .keys()
                .filter(|k| mutated.get(k.as_str()).is_none())
                .collect();
            assert_eq!(missing.len(), 1, "one field is left out: {mutated}");
            let field = missing[0];
            if default_of(field).as_ref() == good.get(field.as_str()) {
                Expect::SameAnswer
            } else {
                Expect::Error
            }
        }
        _ => Expect::Error,
    }
}

/// Hold `answer`, to the line it answered, to what the line is owed.
fn check_line(answer: &str, expect: Expect, good_answer: &str) -> Result<&'static str, String> {
    match (expect, refusal(answer)) {
        (Expect::Error, Some(_)) => Ok("error"),
        (Expect::SameAnswer, None) if answer == good_answer => Ok("same-answer"),
        (expect, _) => Err(format!("expected {expect:?}, got {}", answer.trim_end())),
    }
}

/// One op that reads a JSON request, and its good request over `files`.
struct JsonOp {
    name: &'static str,
    good: fn(&[String]) -> Value,
}

const JSON_OPS: &[JsonOp] = &[
    JsonOp {
        name: "file-batch",
        good: |files| json!({"kind": "uses", "path": files[0], "refs": [], "langversion": null}),
    },
    JsonOp {
        name: "uses-project-batch",
        good: |files| json!({"paths": files, "refs": [], "defines": [], "langversion": null, "exclusiveRefs": false}),
    },
    JsonOp {
        name: "xmldoc-batch",
        good: |files| json!({"paths": files, "refs": [], "defines": [], "langversion": null, "exclusiveRefs": false}),
    },
];

/// Send every wire mutation of each op's good request, through the driver and
/// straight to the oracle, and hold both to the contract in the module docs.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn every_hostile_request_line_is_refused_on_its_line_and_the_oracle_stays_in_step() {
    let census = coverage::open(file!(), "fcs_dump_wire", &[]);
    let fs = HostileFs::new();
    let a = fs
        .place(
            "src",
            &plain("A", ".fs"),
            State::Regular,
            b"module A\nlet a : int = 1\n",
        )
        .expect("a plain source")
        .path;
    let lib = fs
        .place(
            "src",
            &plain("Lib", ".fs"),
            State::Regular,
            b"module Lib\nlet b = A.a + 1\n",
        )
        .expect("a plain source")
        .path;
    let files = vec![text_of(&a), text_of(&lib)];
    let mut failures = Vec::new();
    for op in JSON_OPS {
        let good = (op.good)(&files);
        let good_line = good.to_string();
        let good_answer = fresh_answer(op.name, &good_line)
            .unwrap_or_else(|e| panic!("{}: the good request: {e}", op.name));
        assert_eq!(
            refusal(&good_answer),
            None,
            "{}: the good request is answered",
            op.name
        );
        // Each child's first line is the good request: a reader may treat
        // the first bytes of its input apart (a byte order mark there is no
        // part of any line).
        let mut through_driver = driver_within(op.name, WIRE_TIMEOUT);
        let mut raw = RawChild::spawn(op.name);
        raw.send(good_line.as_bytes());
        for (child, answer) in [
            (
                "driver",
                through_driver
                    .try_request(&good_line)
                    .map_err(|e| e.to_string()),
            ),
            ("raw", raw.answer()),
        ] {
            assert_eq!(
                answer.as_deref(),
                Ok(good_answer.as_str()),
                "{}: the {child} child answers the good request as a fresh one does",
                op.name
            );
        }
        census.reached(&BTreeSet::new(), "same-answer");

        for entry in wire::mutations(&good).entries() {
            let label = format!(
                "{} {} ({}): {:?}",
                op.name,
                entry.dimension,
                entry.why,
                String::from_utf8_lossy(&entry.value)
            );
            match wire_case(
                &mut through_driver,
                &mut raw,
                entry,
                &good,
                &good_line,
                &good_answer,
            ) {
                Ok(outcome) => census.reached(&BTreeSet::from([entry.dimension]), &outcome),
                Err(why) => {
                    failures.push(format!("{label}: {why}"));
                    // A child out of step answers every later request wrongly.
                    through_driver = driver_within(op.name, WIRE_TIMEOUT);
                    raw = RawChild::spawn(op.name);
                    raw.send(good_line.as_bytes());
                    let _ = through_driver.try_request(&good_line);
                    let _ = raw.answer();
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} hostile request lines broke the contract:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    census.finish(REGENERATE);
}

/// One wire mutation through the driver and, where the driver refuses it or
/// cannot carry it, straight to the oracle; then the good request to each
/// child that saw it. The outcome is `<driver>:<oracle>`.
fn wire_case(
    through_driver: &mut BatchChild,
    raw: &mut RawChild,
    entry: &Entry<Vec<u8>>,
    good: &Value,
    good_line: &str,
    good_answer: &str,
) -> Result<String, String> {
    let lines = oracle_lines(&entry.value);
    let text = std::str::from_utf8(&entry.value).ok();
    let driver_verdict = match text {
        // A request that is not text is one the driver's API cannot hold.
        None => "unsendable",
        Some(text) => match (not_one_line(text), through_driver.try_request(text)) {
            (true, Err(BatchFailure::NotOneLine)) => "refused",
            (true, other) => {
                return Err(format!(
                    "the driver must refuse a request that is not one line, and got {other:?}"
                ));
            }
            (false, Ok(answer)) => {
                assert_eq!(lines.len(), 1, "one line");
                let expect = expected_for_line(entry.dimension, &lines[0], good);
                let verdict = check_line(&answer, expect, good_answer)
                    .map_err(|why| format!("through the driver: {why}"))?;
                after_good(
                    through_driver
                        .try_request(good_line)
                        .map_err(|e| e.to_string()),
                    good_answer,
                    "driver",
                )?;
                return Ok(format!("sent:{verdict}"));
            }
            (false, Err(e)) => return Err(format!("the driver failed: {e}")),
        },
    };
    // The driver sent nothing: its next request must find the child in step.
    after_good(
        through_driver
            .try_request(good_line)
            .map_err(|e| e.to_string()),
        good_answer,
        "driver",
    )?;
    raw.send(&entry.value);
    let mut verdicts = BTreeSet::new();
    for (i, line) in lines.iter().enumerate() {
        let answer = raw
            .answer()
            .map_err(|why| format!("line {i} of {}: {why}", lines.len()))?;
        let expect = expected_for_line(entry.dimension, line, good);
        verdicts.insert(
            check_line(&answer, expect, good_answer)
                .map_err(|why| format!("line {i} {:?}: {why}", String::from_utf8_lossy(line)))?,
        );
    }
    raw.send(good_line.as_bytes());
    after_good(raw.answer(), good_answer, "raw")?;
    if let Some(stray) = raw.stray() {
        return Err(format!("an answer no line asked for: {}", stray.trim_end()));
    }
    let oracle = if verdicts.len() == 1 {
        verdicts.into_iter().next().expect("one").to_owned()
    } else {
        "per-line".to_owned()
    };
    Ok(format!("{driver_verdict}:{oracle}"))
}

/// Hold the answer to the good request, sent after a hostile line, to a fresh
/// child's.
fn after_good(
    answer: Result<String, String>,
    good_answer: &str,
    child: &str,
) -> Result<(), String> {
    match answer {
        Ok(answer) if answer == good_answer => Ok(()),
        Ok(answer) => Err(format!(
            "the {child} child, asked the good request next, answered otherwise than a fresh \
             child: {}",
            answer.trim_end()
        )),
        Err(why) => Err(format!(
            "the {child} child, asked the good request next, did not answer: {why}"
        )),
    }
}

// ---------------------------------------------------------------------------
// The files of a project-check request.
// ---------------------------------------------------------------------------

/// The first source: what the second uses.
const A_FS: &[u8] = b"module A\nlet a : int = 1\n";
/// The second source, which uses the first and the reference.
const LIB_FS: &[u8] =
    b"module Lib\nlet b = A.a + 1\nlet t = typeof<System.CommandLine.RootCommand>\n";
/// [`LIB_FS`] rewritten to other bytes of the same length: another binding.
const LIB_FS_REWRITTEN: &[u8] =
    b"module Lib\nlet c = A.a + 1\nlet t = typeof<System.CommandLine.RootCommand>\n";
/// [`LIB_FS`] rewritten to bytes of another length.
const LIB_FS_RESIZED: &[u8] =
    b"module Lib\nlet longer = A.a + 1\nlet t = typeof<System.CommandLine.RootCommand>\n";
/// A source beside a hostile name's twin.
const TWIN_FS: &[u8] = b"module Twin\nlet z = 0\n";
/// What follows each source mutation: a declaration FCS reports an error in.
/// Text before it that moves the positions FCS reports (a line directive)
/// moves the error out of the file's record or past its last line, which
/// [`check_records`] sees.
const SENTINEL: &[u8] = b"\nmodule HostileSentinel =\n    let sentinel : int = \"\"\n";
/// What names [`SENTINEL`] in a source's text.
const SENTINEL_NAME: &[u8] = b"HostileSentinel";

/// The assembly the project references: `System.CommandLine`, which no
/// framework reference holds, from the SDK's own directory.
fn reference_assembly() -> &'static [u8] {
    static BYTES: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    BYTES.get_or_init(|| {
        let root = std::env::var_os("DOTNET_ROOT")
            .map(PathBuf::from)
            .expect("DOTNET_ROOT unset (run under `nix develop`)");
        let sdk = root.join("sdk");
        let mut found: Vec<PathBuf> = std::fs::read_dir(&sdk)
            .unwrap_or_else(|e| panic!("list {}: {e}", sdk.display()))
            .map(|e| e.expect("an entry").path().join("System.CommandLine.dll"))
            .filter(|p| p.is_file())
            .collect();
        found.sort();
        let dll = found
            .first()
            .unwrap_or_else(|| panic!("no System.CommandLine.dll under {}", sdk.display()));
        std::fs::read(dll).unwrap_or_else(|e| panic!("read {}: {e}", dll.display()))
    })
}

/// The suffix of every metadata string the renamed assembly changes.
const RENAMED_FROM: &[u8] = b"RootCommand\0";
const RENAMED_TO: &[u8] = b"XootCommand\0";

/// [`reference_assembly`] with `RootCommand` renamed, in the same number of
/// bytes: the type [`LIB_FS`] names is gone.
fn renamed_assembly() -> Vec<u8> {
    let original = reference_assembly();
    let mut out = Vec::with_capacity(original.len());
    let mut i = 0;
    let mut renamed = 0;
    while i < original.len() {
        if original[i..].starts_with(RENAMED_FROM) {
            out.extend(RENAMED_TO);
            i += RENAMED_FROM.len();
            renamed += 1;
        } else {
            out.push(original[i]);
            i += 1;
        }
    }
    assert!(renamed > 0, "the assembly names RootCommand");
    out
}

/// [`renamed_assembly`] with bytes after the image: another length.
fn renamed_padded_assembly() -> Vec<u8> {
    let mut out = renamed_assembly();
    out.extend(std::iter::repeat_n(0, 4096));
    out
}

/// The plain name `stem` `ext`.
fn plain(stem: &str, ext: &str) -> Rendered {
    Name {
        parts: name::PLAIN,
        twin: None,
    }
    .render(stem, ext)
}

/// A path as the request's JSON carries it.
///
/// # Panics
///
/// If it is not UTF-8: JSON holds no such path, and the census excludes the
/// names that make one.
fn text_of(path: impl AsRef<std::ffi::OsStr>) -> String {
    path.as_ref()
        .to_str()
        .unwrap_or_else(|| panic!("{:?} is no text", path.as_ref()))
        .to_owned()
}

/// One case of the project census, as data: which file is made hostile, and
/// how.
#[derive(Debug, Clone, Copy)]
enum Case {
    /// The project as it is.
    Plain,
    /// The second source in a state.
    SourceState(State),
    /// The reference in a state.
    ReferenceState(State),
    /// The second source changed after a first request.
    SourceChange(Change),
    /// The reference changed after a first request.
    ReferenceChange(Change),
    /// The second source under a hostile name.
    SourceName(&'static Entry<Name>),
    /// The second source under a hostile name, beside a source under the
    /// name's twin.
    SourceTwins(&'static Entry<Name>),
    /// The second source rewritten after a first request, then named by a
    /// hostile spelling.
    SourceSpelling(&'static Entry<Spelling>),
    /// The reference rewritten after a first request, then named by a hostile
    /// spelling.
    ReferenceSpelling(&'static Entry<Spelling>),
    /// The second source mutated after a first request.
    SourceMutation(&'static Entry<Mutation>),
    /// The second source a script (`.fsx`), mutated after a first request: a
    /// script reads `#r` and `#load` where a compiled source refuses them.
    ScriptMutation(&'static Entry<Mutation>),
}

impl Case {
    fn hostile(&self) -> BTreeSet<Dimension> {
        let one = |d: Dimension| BTreeSet::from([d]);
        match self {
            Case::Plain => BTreeSet::new(),
            Case::SourceState(s) | Case::ReferenceState(s) => one(s.dimension()),
            Case::SourceChange(c) | Case::ReferenceChange(c) => one(c.dimension()),
            Case::SourceName(e) | Case::SourceTwins(e) => one(e.dimension),
            Case::SourceSpelling(e) | Case::ReferenceSpelling(e) => one(e.dimension),
            Case::SourceMutation(e) | Case::ScriptMutation(e) => one(e.dimension),
        }
    }

    /// Every case.
    fn all() -> Vec<Case> {
        let mut cases = vec![Case::Plain];
        cases.extend(State::ALL.iter().map(|s| Case::SourceState(*s)));
        cases.extend(State::ALL.iter().map(|s| Case::ReferenceState(*s)));
        cases.extend(Change::ALL.iter().map(|c| Case::SourceChange(*c)));
        cases.extend(Change::ALL.iter().map(|c| Case::ReferenceChange(*c)));
        for entry in name::alphabet().entries() {
            // JSON holds no path that is not text.
            if entry.dimension == Dimension::NonUtf8 || !entry.value.varies("Lib", ".fs") {
                continue;
            }
            cases.push(Case::SourceName(entry));
            if entry.value.twin.is_some() {
                cases.push(Case::SourceTwins(entry));
            }
        }
        for entry in spelling::alphabet().entries() {
            cases.push(Case::SourceSpelling(entry));
            cases.push(Case::ReferenceSpelling(entry));
        }
        cases.extend(
            source::alphabet()
                .entries()
                .iter()
                .map(Case::SourceMutation),
        );
        cases.extend(
            source::alphabet()
                .entries()
                .iter()
                .map(Case::ScriptMutation),
        );
        // `BORZOI_HOSTILE_CASES=<text>` keeps the cases whose description
        // holds the text, for iterating on one; the census then fails.
        if let Some(filter) = std::env::var_os("BORZOI_HOSTILE_CASES") {
            let filter = filter.to_string_lossy().into_owned();
            cases.retain(|c| format!("{c:?}").contains(&filter));
        }
        cases
    }
}

/// What a case's request names, and what each source holds when the request
/// is answered.
struct World {
    fs: HostileFs,
    /// The request a resident child is asked first, if the case has one.
    prime: Option<String>,
    /// The request both children are asked.
    request: String,
    /// What each source of `request` holds, or `None` where it holds no text
    /// (missing, a FIFO, a directory): a successful answer then is wrong.
    texts: Vec<Option<Vec<u8>>>,
}

/// The request over `paths` and `refs`, every optional field at its default.
fn project_request(paths: &[String], refs: &[String]) -> String {
    json!({"paths": paths, "refs": refs, "defines": [], "langversion": null, "exclusiveRefs": false})
        .to_string()
}

/// The text a reader of `state`, made with `content`, finds.
fn text_in(state: State, content: &[u8]) -> Option<Vec<u8>> {
    match state {
        State::Regular
        | State::Symlink
        | State::SymlinkOutOfTree
        | State::Unreadable
        | State::ReadOnly => Some(content.to_vec()),
        State::Empty | State::CharDevice => Some(Vec::new()),
        State::Fifo
        | State::Socket
        | State::DanglingSymlink
        | State::SymlinkLoop
        | State::Directory
        | State::Missing => None,
    }
}

/// The change a case makes between its two requests, returning what each
/// source then holds.
type Mutate = Box<dyn FnOnce(&HostileFs) -> Result<Vec<Option<Vec<u8>>>, Unmakeable>>;

/// The project made plain except where `case` says, and the change the case
/// makes between its two requests: [`run_case`] applies it after the
/// resident child has answered the first.
fn build(case: Case) -> Result<(World, Option<Mutate>), Unmakeable> {
    let fs = HostileFs::new();
    let a = text_of(
        &fs.place("src", &plain("A", ".fs"), State::Regular, A_FS)?
            .path,
    );
    let place_lib = |state: State, content: &[u8]| -> Result<String, Unmakeable> {
        Ok(text_of(
            &fs.place("src", &plain("Lib", ".fs"), state, content)?.path,
        ))
    };
    let place_ref = |state: State, content: &[u8]| -> Result<String, Unmakeable> {
        Ok(text_of(
            &fs.place("refs", &plain("Ref", ".dll"), state, content)?
                .path,
        ))
    };
    let plain_texts = plain_texts_owned;
    let (prime, request, texts, change): (Option<String>, String, _, Option<Mutate>) = match case {
        Case::Plain => {
            let lib = place_lib(State::Regular, LIB_FS)?;
            let dll = place_ref(State::Regular, reference_assembly())?;
            (
                None,
                project_request(&[a, lib], &[dll]),
                plain_texts(),
                None,
            )
        }
        Case::SourceState(state) => {
            let lib = place_lib(state, LIB_FS)?;
            let dll = place_ref(State::Regular, reference_assembly())?;
            (
                None,
                project_request(&[a, lib], &[dll]),
                vec![Some(A_FS.to_vec()), text_in(state, LIB_FS)],
                None,
            )
        }
        Case::ReferenceState(state) => {
            let lib = place_lib(State::Regular, LIB_FS)?;
            let dll = place_ref(state, reference_assembly())?;
            (
                None,
                project_request(&[a, lib], &[dll]),
                plain_texts(),
                None,
            )
        }
        Case::SourceChange(change) => {
            let initial = if change == Change::Appears {
                State::Missing
            } else {
                State::Regular
            };
            let lib = place_lib(initial, LIB_FS)?;
            let dll = place_ref(State::Regular, reference_assembly())?;
            let request = project_request(&[a, lib.clone()], &[dll]);
            let (new, after): (&[u8], Option<Vec<u8>>) = match change {
                Change::SameStampRewrite | Change::SameStampReplace => {
                    (LIB_FS_REWRITTEN, Some(LIB_FS_REWRITTEN.to_vec()))
                }
                Change::SameStampResize => (LIB_FS_RESIZED, Some(LIB_FS_RESIZED.to_vec())),
                Change::Appears => (LIB_FS, Some(LIB_FS.to_vec())),
                Change::Disappears => (b"", None),
            };
            (
                Some(request.clone()),
                request,
                Vec::new(),
                Some(Box::new(move |fs: &HostileFs| {
                    fs.change(Path::new(&lib), change, new)?;
                    Ok(vec![Some(A_FS.to_vec()), after])
                })),
            )
        }
        Case::ReferenceChange(change) => {
            let lib = place_lib(State::Regular, LIB_FS)?;
            let initial = if change == Change::Appears {
                State::Missing
            } else {
                State::Regular
            };
            let dll = place_ref(initial, reference_assembly())?;
            let request = project_request(&[a, lib], std::slice::from_ref(&dll));
            let new = match change {
                Change::SameStampRewrite | Change::SameStampReplace => renamed_assembly(),
                Change::SameStampResize => renamed_padded_assembly(),
                Change::Appears => reference_assembly().to_vec(),
                Change::Disappears => Vec::new(),
            };
            (
                Some(request.clone()),
                request,
                Vec::new(),
                Some(Box::new(move |fs: &HostileFs| {
                    fs.change(Path::new(&dll), change, &new)?;
                    Ok(vec![Some(A_FS.to_vec()), Some(LIB_FS.to_vec())])
                })),
            )
        }
        Case::SourceName(entry) => {
            let lib = text_of(
                &fs.place(
                    "src",
                    &entry.value.render("Lib", ".fs"),
                    State::Regular,
                    LIB_FS,
                )?
                .path,
            );
            let dll = place_ref(State::Regular, reference_assembly())?;
            (
                None,
                project_request(&[a, lib], &[dll]),
                plain_texts(),
                None,
            )
        }
        Case::SourceTwins(entry) => {
            let hostile_name = entry.value.render("Lib", ".fs");
            let twin_name = entry.value.twin("Lib", ".fs").expect("a twinned name");
            fs.holds_apart(&hostile_name, &twin_name)?;
            let twin = text_of(&fs.place("src", &twin_name, State::Regular, TWIN_FS)?.path);
            let lib = text_of(&fs.place("src", &hostile_name, State::Regular, LIB_FS)?.path);
            let dll = place_ref(State::Regular, reference_assembly())?;
            (
                None,
                project_request(&[a, twin, lib], &[dll]),
                vec![
                    Some(A_FS.to_vec()),
                    Some(TWIN_FS.to_vec()),
                    Some(LIB_FS.to_vec()),
                ],
                None,
            )
        }
        Case::SourceSpelling(entry) => {
            let lib = place_lib(State::Regular, LIB_FS)?;
            let dll = place_ref(State::Regular, reference_assembly())?;
            spelling::prepare(&fs, "src");
            let spelt = spelt(&fs, entry, "src", "Lib.fs");
            let prime = project_request(&[a.clone(), lib.clone()], std::slice::from_ref(&dll));
            (
                Some(prime),
                project_request(&[a, spelt], &[dll]),
                Vec::new(),
                Some(Box::new(move |fs: &HostileFs| {
                    fs.change(Path::new(&lib), Change::SameStampRewrite, LIB_FS_REWRITTEN)?;
                    Ok(vec![Some(A_FS.to_vec()), Some(LIB_FS_REWRITTEN.to_vec())])
                })),
            )
        }
        Case::ReferenceSpelling(entry) => {
            let lib = place_lib(State::Regular, LIB_FS)?;
            let dll = place_ref(State::Regular, reference_assembly())?;
            spelling::prepare(&fs, "refs");
            let spelt = spelt(&fs, entry, "refs", "Ref.dll");
            let prime = project_request(&[a.clone(), lib.clone()], std::slice::from_ref(&dll));
            (
                Some(prime),
                project_request(&[a, lib], &[spelt]),
                Vec::new(),
                Some(Box::new(move |fs: &HostileFs| {
                    fs.change(
                        Path::new(&dll),
                        Change::SameStampRewrite,
                        &renamed_assembly(),
                    )?;
                    Ok(plain_texts_owned())
                })),
            )
        }
        Case::SourceMutation(entry) | Case::ScriptMutation(entry) => {
            let lib = match case {
                Case::ScriptMutation(_) => text_of(
                    &fs.place("src", &plain("Lib", ".fsx"), State::Regular, LIB_FS)?
                        .path,
                ),
                _ => place_lib(State::Regular, LIB_FS)?,
            };
            let dll = place_ref(State::Regular, reference_assembly())?;
            let request = project_request(&[a, lib.clone()], &[dll]);
            let mutated = [
                entry
                    .value
                    .apply(std::str::from_utf8(LIB_FS).expect("text")),
                SENTINEL.to_vec(),
            ]
            .concat();
            (
                Some(request.clone()),
                request,
                Vec::new(),
                Some(Box::new(move |_: &HostileFs| {
                    // The file is the fixture's own, in its own tree.
                    std::fs::write(&lib, &mutated).expect("write the mutated source");
                    Ok(vec![Some(A_FS.to_vec()), Some(mutated)])
                })),
            )
        }
    };
    Ok((
        World {
            fs,
            prime,
            request,
            texts,
        },
        change,
    ))
}

fn plain_texts_owned() -> Vec<Option<Vec<u8>>> {
    vec![Some(A_FS.to_vec()), Some(LIB_FS.to_vec())]
}

/// `entry`'s spelling of the file `name` in the directory `dir` of `fs`'s
/// tree: relative where the dimension is a relative path, absolute otherwise.
fn spelt(fs: &HostileFs, entry: &Entry<Spelling>, dir: &str, name: &str) -> String {
    let spelt = if entry.dimension == Dimension::Relative {
        entry.value.relative(dir, name)
    } else {
        entry.value.absolute(fs.tree(), dir, name)
    };
    text_of(spelt)
}

/// Every count of line ends a reader may see in `text`: a line feed, a
/// carriage return, and the two together each end one. One more than that is
/// the last line a range in the file can start on.
fn last_line(text: &[u8]) -> usize {
    let mut lines = 1;
    let mut i = 0;
    while i < text.len() {
        match text[i] {
            b'\n' => lines += 1,
            b'\r' => {
                lines += 1;
                if text.get(i + 1) == Some(&b'\n') {
                    i += 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    lines
}

/// The module a source declares on its first line, after any byte order
/// mark.
fn declared_module(text: &[u8]) -> Option<String> {
    let text = std::str::from_utf8(text).ok()?;
    let first = text.trim_start_matches('\u{feff}').lines().next()?;
    let name = first.strip_prefix("module ")?.trim();
    (!name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric())).then(|| name.to_owned())
}

/// Hold a successful answer to what the files hold: one record per source,
/// each source's record holding the definition of the module it declares
/// and, where the source ends in [`SENTINEL`], an error, and no range in a
/// record starting past its file's last line.
fn check_records(answer: &Value, texts: &[Option<Vec<u8>>]) -> Result<(), String> {
    let files = answer["Files"]
        .as_array()
        .ok_or_else(|| format!("no Files: {answer}"))?;
    if files.len() != texts.len() {
        return Err(format!(
            "{} records for {} sources",
            files.len(),
            texts.len()
        ));
    }
    for (i, (file, text)) in files.iter().zip(texts).enumerate() {
        let Some(text) = text else {
            return Err(format!(
                "source {i} holds no text, and the oracle answered: {file}"
            ));
        };
        let last = last_line(text);
        let uses = file["Uses"].as_array().cloned().unwrap_or_default();
        let diagnostics = file["Diagnostics"].as_array().cloned().unwrap_or_default();
        for range in uses
            .iter()
            .chain(diagnostics.iter())
            .filter_map(|r| r.get("Range"))
            .filter(|r| !r.is_null())
        {
            let line = range["Start"]["Line"].as_u64().unwrap_or(0) as usize;
            if line > last {
                return Err(format!(
                    "source {i} has {last} lines, and its record holds a range on line {line}: \
                     {range}"
                ));
            }
        }
        let holds_sentinel = text
            .windows(SENTINEL_NAME.len())
            .any(|w| w == SENTINEL_NAME);
        if holds_sentinel && !diagnostics.iter().any(|d| d["Severity"] == "Error") {
            return Err(format!(
                "source {i} ends in a declaration FCS reports an error in, and its record holds \
                 no error: {file}"
            ));
        }
        if let Some(module) = declared_module(text) {
            let defined = uses.iter().any(|u| {
                u["IsFromDefinition"] == Value::Bool(true) && u["SymbolName"] == module.as_str()
            });
            if !defined {
                return Err(format!(
                    "source {i} declares module {module}, and its record does not define it: \
                     {file}"
                ));
            }
        }
    }
    Ok(())
}

/// What became of one case.
enum Verdict {
    /// Both children answered alike, with this outcome.
    Reached(&'static str),
    /// The platform could not make the world.
    Unmakeable(Unmakeable),
}

/// Run `case` against `resident` and a fresh child.
fn run_case(resident: &mut BatchChild, case: Case) -> Result<Verdict, String> {
    let (world, change) = match build(case) {
        Ok(built) => built,
        Err(refusal) => return Ok(Verdict::Unmakeable(refusal)),
    };
    let op = "uses-project-batch";
    let mut texts = world.texts;
    if let Some(prime) = &world.prime {
        resident
            .try_request(prime)
            .map_err(|e| format!("the resident child, asked the first request: {e}"))?;
    }
    if let Some(change) = change {
        match change(&world.fs) {
            Ok(after) => texts = after,
            Err(refusal) => return Ok(Verdict::Unmakeable(refusal)),
        }
    }
    let resident_answer = resident
        .try_request(&world.request)
        .map_err(|e| format!("the resident child: {e}"))?;
    let fresh = fresh_answer(op, &world.request).map_err(|e| format!("a fresh child: {e}"))?;
    if resident_answer != fresh {
        return Err(format!(
            "the resident child answered\n    {}\n  and a fresh child\n    {}",
            resident_answer.trim_end(),
            fresh.trim_end()
        ));
    }
    if refusal(&fresh).is_some() {
        return Ok(Verdict::Reached("refused"));
    }
    let value: Value = serde_json::from_str(&fresh).expect("an answer is JSON");
    check_records(&value, &texts)?;
    let errors = value["Files"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|f| f["Diagnostics"].as_array().cloned().unwrap_or_default())
        .chain(value["Diagnostics"].as_array().cloned().unwrap_or_default())
        .any(|d| d["Severity"] == "Error");
    if matches!(case, Case::Plain) && errors {
        return Err(format!("the plain project checks cleanly: {fresh}"));
    }
    Ok(Verdict::Reached(if errors {
        "answered-with-errors"
    } else {
        "answered"
    }))
}

/// How many resident children share the cases, each taking every
/// `RESIDENTS`th case in order.
const RESIDENTS: usize = 3;

/// Every file-system state, change, name, spelling and source mutation of the
/// project, each answered by a resident child as a fresh one answers it.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn every_hostile_project_is_answered_as_a_fresh_oracle_answers_it() {
    let census = coverage::open(
        file!(),
        "fcs_dump_project",
        &[(
            Dimension::NonUtf8,
            "a request is JSON, which holds no path that is not UTF-8",
        )],
    );
    // The changes and spellings must change the answer, or a stale answer
    // would pass for a fresh one.
    assert_ne!(
        renamed_assembly().len(),
        renamed_padded_assembly().len(),
        "the resize changes the length"
    );
    let cases = Case::all();
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for worker in 0..RESIDENTS {
            let (cases, census, failures) = (&cases, &census, &failures);
            scope.spawn(move || {
                let mut resident = driver("uses-project-batch");
                for case in cases.iter().skip(worker).step_by(RESIDENTS) {
                    match run_case(&mut resident, *case) {
                        Ok(Verdict::Reached(outcome)) => census.reached(&case.hostile(), outcome),
                        Ok(Verdict::Unmakeable(refusal)) => census.unmakeable(&refusal),
                        Err(why) => {
                            failures
                                .lock()
                                .unwrap_or_else(|p| p.into_inner())
                                .push(format!("{case:?}: {why}"));
                            // The next case gets a child no failure touched.
                            resident = driver("uses-project-batch");
                        }
                    }
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap_or_else(|p| p.into_inner());
    assert!(
        failures.is_empty(),
        "{} hostile projects broke the contract:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    census.finish(REGENERATE);
}
