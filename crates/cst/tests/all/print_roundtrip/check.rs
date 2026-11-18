//! The round-trip property's second half: FCS's checker must accept what the
//! tree's types allow.
//!
//! A parse sees only syntax, but F#'s checker refuses some of what parses: a
//! parenthesised control construct in a computation expression, `return` in a
//! list, a feature gated at a version only the checker knows. So trees whose
//! every name is one this module declares are type-checked too, after
//! [`PRELUDE`], and must draw no error. The statement table
//! ([`super::statements`]) and the gates ([`super::gates`]) are written over
//! these names; the generated and corpus trees use any name, so the checker
//! would only report them unbound.

use std::collections::BTreeMap;
use std::io::Write as _;

use borzoi_print::print_impl_file;
use borzoi_print::tree::ImplFile;
use borzoi_print::version::{LanguageVersion, Version};

use crate::common::{fcs_check_diagnostics_at, par_map};

/// The names a checked tree may use, each with the type its slot natively
/// takes (a condition `bool`, a loop's source a sequence, a statement or `do!`
/// operand `unit`, a bound or used value a disposable, a destructured one a
/// pair), and `builder`, with every method a computation expression can
/// call, over `obj`. A checked tree that fails is one F# cannot express,
/// whatever its leaves meant.
pub const PRELUDE: &str = "\
type B() =
    member this.Bind (m: 'a, f: 'a -> obj) : obj = f m
    member this.BindReturn (m: 'a, f: 'a -> 'b) : obj = box (f m)
    member this.MergeSources (a: 'a, b: 'b) : 'a * 'b = (a, b)
    member this.Return (x: obj) : obj = x
    member this.ReturnFrom (x: obj) : obj = x
    member this.Yield (x: obj) : obj = x
    member this.YieldFrom (x: obj) : obj = x
    member this.Zero () : obj = null
    member this.Combine (a: obj, b: obj) : obj = b
    member this.Delay (f: unit -> obj) : obj = f ()
    member this.For (s: seq<'a>, f: 'a -> obj) : obj = null
    member this.While (g: unit -> bool, b: obj) : obj = b
    member this.TryWith (b: obj, h: exn -> obj) : obj = b
    member this.TryFinally (b: obj, f: unit -> unit) : obj = b
    member this.Using (r: 'a, f: 'a -> obj) : obj = f r
let builder = B ()
let c = true
let u = ()
let e : obj = null
let r : obj = null
let z : obj = null
let xs : seq<obj> = Seq.empty
let ss : seq<string> = Seq.empty
let a = 1
let b = 3
let s = 1
let f = ()
let v = { new System.IDisposable with member this.Dispose () = () }
let t = (1, 2)
";

/// How many trees share one checked source.
const CHECK_CHUNK: usize = 64;

/// A tree FCS's checker rejected: its printing, and each error's code and
/// message.
pub type CheckFailure = (String, Vec<(i64, String)>);

/// Each of `files` that FCS's checker rejects at `lang`, with the errors it
/// reports. Warnings are not graded: the leaves' values go unused. The files
/// are checked [`CHECK_CHUNK`] at a time after [`PRELUDE`], each in a module
/// of its own, indented whole so its layout is unchanged.
pub fn check_failures<V: Version>(
    files: &[ImplFile<V>],
    lang: LanguageVersion,
) -> Vec<CheckFailure> {
    let chunks: Vec<&[ImplFile<V>]> = files.chunks(CHECK_CHUNK).collect();
    par_map(chunks.len(), |n| {
        let mut source = String::from(PRELUDE);
        let mut starts = Vec::new();
        let mut printed = Vec::new();
        for (i, file) in chunks[n].iter().enumerate() {
            let text = print_impl_file(file);
            starts.push(source.lines().count() + 1);
            source.push_str(&format!("module M{i} =\n"));
            for line in text.lines() {
                source.push_str("    ");
                source.push_str(line);
                source.push('\n');
            }
            printed.push(text);
        }
        let mut tmp = tempfile::Builder::new()
            .prefix("Checked")
            .suffix(".fs")
            .tempfile()
            .expect("create tempfile");
        tmp.write_all(source.as_bytes()).expect("write source");
        let json = fcs_check_diagnostics_at(tmp.path(), &lang.to_string());
        let record: serde_json::Value = serde_json::from_str(&json).expect("check JSON");
        let diagnostics = record["Diagnostics"]
            .as_array()
            .unwrap_or_else(|| panic!("no check diagnostics: {json}"));
        let mut errors: Vec<Vec<(i64, String)>> = vec![Vec::new(); printed.len()];
        for d in diagnostics.iter().filter(|d| d["Severity"] == "Error") {
            let line = d["StartLine"].as_u64().expect("a line") as usize;
            let code = d["Code"].as_i64().expect("a code");
            let message = d["Message"].as_str().expect("a message").to_owned();
            let i = starts
                .iter()
                .rposition(|&start| start <= line)
                .unwrap_or_else(|| panic!("FCS rejects the prelude at {lang}: {code} {message}"));
            errors[i].push((code, message));
        }
        printed
            .into_iter()
            .zip(errors)
            .filter(|(_, errors)| !errors.is_empty())
            .collect::<Vec<_>>()
    })
    .into_iter()
    .flatten()
    .collect()
}

/// `failures`, grouped by error, with a few printed examples each.
pub fn check_report(failures: &[CheckFailure]) -> String {
    let mut groups: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for (printed, errors) in failures {
        let mut keys: Vec<String> = errors
            .iter()
            .map(|(code, message)| {
                let first: String = message
                    .lines()
                    .next()
                    .unwrap_or("")
                    .chars()
                    .take(90)
                    .collect();
                format!("FS{code:04} {first}")
            })
            .collect();
        keys.dedup();
        for key in keys {
            groups.entry(key).or_default().push(printed);
        }
    }
    groups
        .iter()
        .map(|(key, examples)| {
            let shown: Vec<&str> = examples.iter().take(3).copied().collect();
            format!("{} × {key}\n{}", examples.len(), shown.join("\n"))
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}
