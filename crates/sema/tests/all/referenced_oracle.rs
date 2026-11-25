//! Self-tests of the project-graph oracle's `referenced` op
//! (`common::referenced`): what FCS reads of a producer project from source.
//!
//! The oracle's claim, and all of it: for a producer A that FCS checks as a
//! project reference, the op reports either A's in-memory signature, which
//! decodes into existence rows equal to those of the DLL FCS compiles from the
//! same arguments (D1) and equal to FCS's own view of A's entities, or a
//! refusal naming why the oracle describes no source reading of A
//! ([`RefusalCause`]), or the reader marks the reading unknown because the
//! decoder cannot read A's signature. These tests hold it to that:
//!
//! - every cell of [`cells`], an inventory of FCS features, is read and
//!   checked, and its verdict pinned in `tests/manifests/referenced_oracle.txt`;
//! - every way a cell can go ungraded has a cell that triggers it and a
//!   near miss that must be graded ([`every_excuse_has_its_witnesses`]);
//! - the subject's parse, built from the same [`GraphCell`], reads the `#if`
//!   branches FCS reads ([`the_cell_parse_reads_the_branches_fcs_reads`]);
//! - each request is answered from fresh state, and a planted cache across
//!   requests is caught ([`a_planted_cross_request_cache_is_caught`]).

use std::collections::BTreeSet;
use std::path::PathBuf;

use borzoi_cst::syntax::SyntaxKind;
use borzoi_oracle_harness::BatchChild;
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::{
    FixtureFile, GraphCell, GraphProject, GraphRequest, LangVersion, PlainName, RefLib, Reference,
    ReferencedResponse, RefusalCause, ResponseError, Target, framework_references, parse_response,
};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::common::referenced::{D1, Reading, Unknown, View, parse_cell, prepare, read};
use crate::common::{invoke_fcs_dump_graph, with_fcs_graph_child};

fn plain(s: &str) -> PlainName {
    PlainName::new(s).expect("a plain name")
}

fn files(files: &[(&str, &str)]) -> Vec<FixtureFile> {
    files
        .iter()
        .map(|(name, text)| FixtureFile {
            name: (*name).to_owned(),
            text: (*text).to_owned(),
        })
        .collect()
}

/// A library producer of one file, `Lib.fs`.
fn one(text: &str) -> GraphCell {
    GraphCell::library(plain("Producer"), files(&[("Lib.fs", text)]))
}

/// The inventory: one producer per FCS feature whose signature a dependant
/// reads, and the producers each excuse needs ([`witnesses`]).
fn cells() -> Vec<(&'static str, GraphCell)> {
    let mut cells = vec![
        ("namespace", one("namespace N\ntype T = { X: int }\n")),
        (
            "namespace_dotted_and_fragments",
            one(
                "namespace A.B.C\ntype T = int list\nnamespace A.D\ntype U = { Y: int }\nnamespace A.B.C\ntype V = | V1 | V2\n",
            ),
        ),
        ("namespace_empty", one("namespace Empty.Inner\n")),
        (
            "namespace_rec",
            one("namespace rec R\ntype A = { B: B option }\ntype B = { A: A }\n"),
        ),
        (
            "namespace_global",
            one("namespace global\ntype TopType = { X: int }\nmodule TopModule =\n    let x = 1\n"),
        ),
        (
            "namespace_quoted_segment_with_dot",
            one("namespace N.``a.b``\ntype T = int\n"),
        ),
        (
            "namespace_two_files",
            GraphCell::library(
                plain("Producer"),
                files(&[
                    ("A.fs", "namespace Shared.Ns\ntype First = int\n"),
                    ("B.fs", "namespace Shared.Ns\ntype Second = string\n"),
                ]),
            ),
        ),
        (
            "module_header",
            one("module Top.Level.Mod\nlet x = 1\ntype Inner = { A: int }\n"),
        ),
        (
            "module_nested_deep",
            one(
                "namespace Deep\nmodule L1 =\n    module L2 =\n        module L3 =\n            type Bottom = { X: int }\n",
            ),
        ),
        (
            "module_rec",
            one(
                "module rec RecMod\ntype A = { B: B }\nand B = { A: A option }\nmodule Inner =\n    type C = int\n",
            ),
        ),
        (
            "module_abbreviation",
            one("namespace N\nmodule Real =\n    let x = 1\nmodule Alias = Real\n"),
        ),
        (
            "module_suffix",
            one(
                "namespace Suffix\n[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]\nmodule Explicit =\n    let x = 1\ntype Implicit = { X: int }\nmodule Implicit =\n    let y = 1\n",
            ),
        ),
        (
            "headerless_exe",
            GraphCell {
                target: Target::Exe,
                ..one("let x = 1\ntype InHeaderless = { A: int }\n")
            },
        ),
        (
            "access",
            one(
                "namespace Acc\nmodule private Priv =\n    type InPriv = int\nmodule internal Int =\n    type internal I = { X: int }\n    type private P = { Y: int }\ntype private PT() = member _.X = 1\nexception internal IE of string\n",
            ),
        ),
        (
            "type_kinds",
            one(
                "namespace Kinds\ntype Cls(x: int) = member _.X = x\n[<Struct>] type Str = { S: int }\ntype IExplicit = interface abstract M: int end\n[<AbstractClass>] type Abs() = abstract M: int\ntype Uni = | U1 | U2 of int\ntype En = | A = 1 | B = 2\ntype Del = delegate of int -> int\ntype Empty = class end\n",
            ),
        ),
        (
            "type_generic_and_measures",
            one(
                "namespace Gen\ntype G<'a> = { V: 'a }\ntype G2<'a, 'b> = | P of 'a * 'b\n[<Measure>] type m\n[<Measure>] type s\n[<Measure>] type speed = m / s\ntype Measured<[<Measure>] 'u> = { V: float<'u> }\n",
            ),
        ),
        (
            "abbreviations",
            one(
                "namespace Abbr\ntype I = int\ntype L<'a> = 'a list\ntype F = int -> string\ntype Tup = int * string\n",
            ),
        ),
        (
            "exceptions",
            one(
                "namespace Exn\nexception E1\nexception E2 of string\nexception E3 of code: int * msg: string\nexception E4 = E2\n",
            ),
        ),
        (
            "auto_open_spellings",
            one(
                "namespace AO\n[<AutoOpen>]\nmodule A1 =\n    let x = 1\n[<Microsoft.FSharp.Core.AutoOpen>]\nmodule A2 =\n    let x = 1\nmodule Outer =\n    [<AutoOpen>]\n    module Inner =\n        let y = 1\n",
            ),
        ),
        (
            "compiled_name",
            one(
                "namespace CN\n[<CompiledName(\"RenamedType\")>]\ntype T() = member _.X = 1\n[<CompiledName(\"RenamedModule\")>]\nmodule M =\n    let x = 1\n",
            ),
        ),
        (
            "extension_fsharp",
            one(
                "namespace Ext\nmodule Members =\n    type System.Collections.Generic.List<'T> with\n        member s.Method() = s.Count\n        member s.Prop = s.Count\n        static member Static() = 1\n",
            ),
        ),
        (
            "extension_csharp_style",
            one(
                "namespace ExtCs\nopen System.Runtime.CompilerServices\n[<Extension>]\ntype Exts =\n    [<Extension>]\n    static member Twice(s: string) = s + s\nmodule Lets =\n    [<Extension>]\n    let shout (s: string) = s.ToUpper()\n",
            ),
        ),
        (
            "intrinsic_augmentation",
            one("namespace Aug\ntype R = { X: int }\ntype R with\n    member r.Y = r.X\n"),
        ),
        (
            "signature_pair_hiding",
            GraphCell::library(
                plain("Producer"),
                files(&[
                    (
                        "Lib.fsi",
                        "namespace Pair\ntype Shown = { X: int }\nmodule M =\n    val x: int\n",
                    ),
                    (
                        "Lib.fs",
                        "namespace Pair\ntype Shown = { X: int }\ntype Hidden = { Y: int }\nmodule M =\n    let x = 1\n    type HiddenInModule = int\n",
                    ),
                ]),
            ),
        ),
        (
            "defines",
            GraphCell {
                defines: vec!["A_ONLY".to_owned()],
                ..one(
                    "namespace Def\n#if A_ONLY\ntype Shown = { X: int }\n#else\ntype Hidden = { Y: int }\n#endif\n#if B_ONLY\ntype NotA = int\n#endif\n",
                )
            },
        ),
        (
            "compiled_symbol",
            one(
                "namespace Compiled\n#if COMPILED\ntype Shown = { X: int }\n#else\ntype Hidden = { Y: int }\n#endif\n",
            ),
        ),
        (
            "lang_version_9",
            GraphCell {
                lang_version: LangVersion::new(9, 0),
                ..one("namespace Nine\ntype T = { X: int }\n")
            },
        ),
        (
            "assembly_name_dotted",
            GraphCell::library(
                plain("My.Dotted.Producer"),
                files(&[("Lib.fs", "namespace Dotted\ntype T = int\n")]),
            ),
        ),
        (
            "reference_library",
            GraphCell {
                ref_libs: vec![RefLib {
                    assembly_name: plain("RefLib"),
                    files: files(&[("Ref.fs", "namespace RefLib\ntype T = { X: int }\n")]),
                }],
                ..one("namespace UsesRef\ntype Ab = RefLib.T\ntype R = { T: RefLib.T }\n")
            },
        ),
        (
            "compiled_name_collision",
            one(
                "namespace Collide\n[<CompiledName(\"Same\")>]\ntype A = { X: int }\ntype Same = { Y: int }\n",
            ),
        ),
        (
            "module_path_with_plus",
            one(
                "namespace Plus\nmodule A =\n    module B =\n        type T = int\nmodule ``A+B`` =\n    type U = int\n",
            ),
        ),
        (
            "extension_csharp_style_getter_named_method",
            one(
                "namespace ExtGet\nopen System.Runtime.CompilerServices\n[<Extension>]\ntype Exts =\n    [<Extension>]\n    static member Foo(s: string) = s\n    [<Extension>]\n    static member get_Foo(s: string) = s\n",
            ),
        ),
        (
            "hash_reference_in_source",
            one("module HashRef\nmodule Inner =\n    #r \"x.dll\"\n    let x = 1\n"),
        ),
        (
            "names_unicode",
            one("namespace Ünïcödé\ntype Élan = { X: int }\nmodule Мир =\n    type Tуpe = int\n"),
        ),
    ];
    cells.extend(witness_cells());
    cells
}

/// The cells [`witnesses`] names: each excuse's trigger, and its near miss.
fn witness_cells() -> Vec<(&'static str, GraphCell)> {
    vec![
        (
            "type_provider_assembly",
            one(
                "namespace Tp\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\ntype T = int\n",
            ),
        ),
        (
            "assembly_other_attribute",
            one(
                "namespace AsmOther\n[<assembly: System.Reflection.AssemblyDescription(\"d\")>]\ndo ()\ntype T = int\n",
            ),
        ),
        (
            "type_provider_assembly_failing",
            one(
                "namespace TpFail\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\nmodule M =\n    let x: int = \"s\"\n",
            ),
        ),
        (
            "failing_type_error",
            one("namespace Fails\ntype T = { X: int }\nmodule M =\n    let x: int = \"s\"\n"),
        ),
        (
            "line_directive",
            one("namespace Line\n# 3 \"Other.fs\"\ntype T = int\n"),
        ),
        (
            "line_directive_shaped_string",
            one(
                "namespace Line\nmodule M =\n    let s = \"#line\"\n    let t = \"# 3\"\ntype T = int\n",
            ),
        ),
        (
            "undecodable_rec_extension_and_augmentation",
            one(
                "module M\nmodule rec Item =\n    type R = { X: int }\n    [<System.Runtime.CompilerServices.Extension>]\n    let f591 (s: string) = s\n    type R with\n        member x.P = 1\n",
            ),
        ),
        (
            "rec_extension_alone",
            one(
                "module M\nmodule rec Item =\n    [<System.Runtime.CompilerServices.Extension>]\n    let f591 (s: string) = s\n",
            ),
        ),
        (
            "rec_augmentation_alone",
            one(
                "module M\nmodule rec Item =\n    type R = { X: int }\n    type R with\n        member x.P = 1\n",
            ),
        ),
        (
            "assembly_auto_open_local_namesake",
            GraphCell::library(
                plain("Producer"),
                files(&[
                    (
                        "Attr.fs",
                        "namespace Microsoft.FSharp.Core\ntype AutoOpenAttribute(path: string) =\n    inherit System.Attribute()\n    member _.Path = path\n",
                    ),
                    (
                        "Lib.fs",
                        "namespace N\n[<assembly: Microsoft.FSharp.Core.AutoOpen(\"N\")>]\ndo ()\ntype T = { X: int }\n",
                    ),
                ]),
            ),
        ),
        (
            "assembly_auto_open",
            one(
                "namespace AsmAO\nmodule M =\n    let x = 1\n[<assembly: AutoOpen(\"AsmAO\")>]\n[<assembly: AutoOpen(@\"AsmAO.M\")>]\ndo ()\n",
            ),
        ),
    ]
}

/// Every way a producer can go ungraded: each refusal, a signature the
/// decoder cannot read, and an assembly-level auto-open D1 does not hold to
/// the in-memory list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Excuse {
    Refused(RefusalCause),
    Undecodable,
    AutoOpenSplit,
}

impl Excuse {
    /// Every excuse.
    fn all() -> Vec<Excuse> {
        RefusalCause::ALL
            .iter()
            .map(|c| Excuse::Refused(*c))
            .chain([Excuse::Undecodable, Excuse::AutoOpenSplit])
            .collect()
    }

    /// The excuse `reading` takes, if any.
    fn of(reading: &Reading) -> Option<Excuse> {
        match (&reading.view, &reading.d1) {
            (View::Unknown(Unknown::Refused(cause)), _) => Some(Excuse::Refused(*cause)),
            (View::Unknown(Unknown::Undecodable(_)), _) => Some(Excuse::Undecodable),
            (
                View::Found(_),
                D1::Held {
                    auto_open_split: Some(_),
                },
            ) => Some(Excuse::AutoOpenSplit),
            (View::Found(_), _) => None,
        }
    }
}

/// How a witness is read: a cell of [`cells`], or a request no cell builds.
#[derive(Clone, Copy, Debug)]
enum Witness {
    Cell(&'static str),
    /// [`unnamed_reference_request`].
    UnnamedReference,
}

/// Each excuse's trigger, which must take it, and its near miss, a producer
/// as close to the trigger as the excuse allows, which must be graded: read
/// from source, decoded, and held to D1 where its check is clean.
fn witnesses(excuse: Excuse) -> (Witness, Witness) {
    match excuse {
        Excuse::Refused(RefusalCause::ReadsDll) => (
            Witness::Cell("type_provider_assembly"),
            Witness::Cell("assembly_other_attribute"),
        ),
        Excuse::Refused(RefusalCause::MayReadDll) => (
            Witness::Cell("type_provider_assembly_failing"),
            Witness::Cell("failing_type_error"),
        ),
        Excuse::Refused(RefusalCause::LineDirective) => (
            Witness::Cell("line_directive"),
            Witness::Cell("line_directive_shaped_string"),
        ),
        Excuse::Refused(RefusalCause::UnnamedReference) => {
            (Witness::UnnamedReference, Witness::Cell("namespace"))
        }
        Excuse::Undecodable => (
            Witness::Cell("undecodable_rec_extension_and_augmentation"),
            Witness::Cell("rec_extension_alone"),
        ),
        Excuse::AutoOpenSplit => (
            Witness::Cell("assembly_auto_open_local_namesake"),
            Witness::Cell("assembly_auto_open"),
        ),
    }
}

fn cell_named(name: &str) -> GraphCell {
    cells()
        .into_iter()
        .find(|(n, _)| *n == name)
        .map(|(_, c)| c)
        .unwrap_or_else(|| panic!("no cell {name}"))
}

fn read_witness(witness: Witness) -> Reading {
    match witness {
        Witness::Cell(name) => read(&cell_named(name)),
        Witness::UnnamedReference => {
            let line = unnamed_reference_request()
                .referenced_line(&plain("Producer"))
                .expect("the consumer references the producer");
            match parse_response::<ReferencedResponse>(&invoke_fcs_dump_graph(&line)) {
                Ok(ReferencedResponse::Refused(refusal)) => Reading {
                    view: View::Unknown(Unknown::Refused(refusal.cause)),
                    errors: Vec::new(),
                    d1: D1::NotApplicable,
                },
                Ok(ReferencedResponse::Found(_)) => Reading {
                    view: View::Found(Default::default()),
                    errors: Vec::new(),
                    d1: D1::NotApplicable,
                },
                Err(e) => panic!("the unnamed-reference witness: {e:?}"),
            }
        }
    }
}

/// A producer checked against the framework without `System.Runtime.dll`,
/// read by a consumer with the whole framework: FCS resolves, for the
/// producer, an assembly the request does not give it. Built by hand,
/// since a [`GraphCell`]'s producer and consumer share one framework.
fn unnamed_reference_request() -> GraphRequest {
    let framework = framework_references();
    let without_runtime: Vec<Reference> = framework
        .iter()
        .filter(|p| p.file_name().is_none_or(|n| n != "System.Runtime.dll"))
        .cloned()
        .map(Reference::Dll)
        .collect();
    assert!(
        without_runtime.len() < framework.len(),
        "the framework set holds System.Runtime.dll"
    );
    let producer = crate::common::temp_fs_file(
        "referenced_unnamed_producer",
        "namespace N\ntype T = { X: int }\n",
    );
    let consumer = crate::common::temp_fs_file(
        "referenced_unnamed_consumer",
        "module Consumer.Use\nlet x = 1\n",
    );
    let mut consumer_refs: Vec<Reference> = framework.iter().cloned().map(Reference::Dll).collect();
    consumer_refs.push(Reference::Project(plain("Producer")));
    let project = |id: &str, sources: Vec<PathBuf>, references: Vec<Reference>| GraphProject {
        id: plain(id),
        assembly_name: plain(id),
        target: Target::Library,
        lang_version: LangVersion::F10,
        sources,
        defines: Vec::new(),
        references,
    };
    GraphRequest::new(
        vec![
            project("Producer", vec![producer], without_runtime),
            project("Consumer", vec![consumer], consumer_refs),
        ],
        plain("Consumer"),
    )
    .expect("a valid graph request")
}

/// Every cell read and checked (the module docs), its verdict pinned.
#[test]
fn the_oracle_reads_every_cell() {
    let cells = cells();
    let names: BTreeSet<&str> = cells.iter().map(|(n, _)| *n).collect();
    assert_eq!(names.len(), cells.len(), "two cells share a name");
    let results = borzoi_oracle_harness::par_map::par_map(cells.len(), |i| {
        let (name, cell) = &cells[i];
        let _silence = borzoi_oracle_harness::panic_silence::silence_panics_here();
        let read = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| read(cell)));
        (*name, read.map_err(|panic| panic_message(&*panic)))
    });
    let mut entries = Vec::new();
    let mut failures = Vec::new();
    for (name, read) in results {
        match read {
            Ok(reading) => entries.push((name.to_owned(), reading.verdict())),
            Err(message) => failures.push(format!("{name}: {message}")),
        }
    }
    assert!(
        failures.is_empty(),
        "{} cells fail:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "referenced_oracle",
        &manifest,
        &regenerate("referenced_oracle::the_oracle_reads_every_cell"),
    );
}

fn panic_message(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap_or_default()
}

/// Each excuse is taken by its trigger and not by its near miss, which is
/// graded: read from source, decoded, and held to D1 where it checks clean.
#[test]
fn every_excuse_has_its_witnesses() {
    let excuses = Excuse::all();
    let results = borzoi_oracle_harness::par_map::par_map(excuses.len(), |i| {
        let excuse = excuses[i];
        let (trigger, near_miss) = witnesses(excuse);
        (excuse, read_witness(trigger), read_witness(near_miss))
    });
    let mut failures = Vec::new();
    for (excuse, trigger, near_miss) in results {
        if Excuse::of(&trigger) != Some(excuse) {
            failures.push(format!(
                "{excuse:?}: its trigger takes {:?}: {}",
                Excuse::of(&trigger),
                trigger.verdict()
            ));
        }
        let graded = Excuse::of(&near_miss).is_none()
            && matches!(near_miss.view, View::Found(_))
            && (!near_miss.errors.is_empty()
                || near_miss.d1
                    == D1::Held {
                        auto_open_split: None,
                    });
        if !graded {
            failures.push(format!(
                "{excuse:?}: its near miss is not graded: {}",
                near_miss.verdict()
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The identifiers our parse of `cell` reads outside inactive `#if` regions
/// that start with `prefix`.
fn active_identifiers(cell: &GraphCell, prefix: &str) -> BTreeSet<String> {
    parse_cell(cell)
        .iter()
        .flat_map(|parse| {
            parse
                .root
                .descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .filter(|t| t.kind() == SyntaxKind::IDENT_TOK && t.text().starts_with(prefix))
                .map(|t| t.text().to_owned())
                .collect::<Vec<_>>()
        })
        .collect()
}

/// The subject's parse of a cell, built from the cell's own symbols and
/// language version, reads exactly the `#if` branches FCS's check of the
/// producer read: every combination of two defines, over conditions on
/// them, on `COMPILED` (which FCS defines for a project) and on
/// `INTERACTIVE` (which it does not).
#[test]
fn the_cell_parse_reads_the_branches_fcs_reads() {
    let conditions = [
        "A",
        "B",
        "A && B",
        "A || !B",
        "COMPILED",
        "!COMPILED",
        "INTERACTIVE",
        "COMPILED && !INTERACTIVE",
    ];
    let mut text = "namespace Branches\n".to_owned();
    for (i, condition) in conditions.iter().enumerate() {
        text.push_str(&format!(
            "#if {condition}\ntype T_{i}_yes = int\n#else\ntype T_{i}_no = int\n#endif\n"
        ));
    }
    let define_sets: [&[&str]; 4] = [&[], &["A"], &["B"], &["A", "B"]];
    let mut failures = Vec::new();
    let mut fcs_names_seen = BTreeSet::new();
    for defines in define_sets {
        let cell = GraphCell {
            defines: defines.iter().map(|d| (*d).to_owned()).collect(),
            ..one(&text)
        };
        let reading = read(&cell);
        let View::Found(rows) = &reading.view else {
            panic!("{defines:?}: {}", reading.verdict());
        };
        let theirs: BTreeSet<String> = rows
            .entities
            .iter()
            .filter(|r| r.logical_name.starts_with("T_"))
            .map(|r| r.logical_name.clone())
            .collect();
        let ours = active_identifiers(&cell, "T_");
        assert_eq!(
            theirs.len(),
            conditions.len(),
            "one branch of each condition"
        );
        fcs_names_seen.extend(theirs.iter().cloned());
        if ours != theirs {
            failures.push(format!(
                "defines {defines:?}: ours {ours:?}, FCS {theirs:?}"
            ));
        }
    }
    // The sweep reaches both branches of every condition but the ones on
    // `COMPILED` and `INTERACTIVE` alone, which no define set moves.
    assert!(
        fcs_names_seen.len() > conditions.len() + 2,
        "the define sets move too few branches: {fcs_names_seen:?}"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Ask one child, spawned with `env`, about a producer twice, its source
/// rewritten in between with its modification time put back, and then a
/// fresh child about the second text. Returns the three answers: the first
/// child's two, and the fresh child's.
fn same_path_probe(env: &[(&'static str, &'static str)]) -> (String, String, String) {
    // One length, so a cache keyed by path, modification time and size
    // would miss nothing.
    let first = "namespace Probe\ntype First = { X: int }\n";
    let second = "namespace Probe\ntype Other = { X: int }\n";
    assert_eq!(first.len(), second.len());
    let cell = GraphCell::library(plain("Probe"), files(&[("Lib.fs", first)]));
    let prepared = prepare(&cell);
    let line = prepared.referenced_line();
    let path = &prepared.paths()[0];
    let stamp = std::fs::metadata(path)
        .and_then(|m| m.modified())
        .expect("the source's modification time");
    let (a1, a2) = with_fcs_graph_child(env, |child: &mut BatchChild| {
        let a1 = child.request(&line);
        std::fs::write(path, second).expect("rewrite the source");
        std::fs::File::options()
            .write(true)
            .open(path)
            .and_then(|f| f.set_modified(stamp))
            .expect("put the modification time back");
        (a1, child.request(&line))
    });
    let fresh = with_fcs_graph_child(&[], |child: &mut BatchChild| child.request(&line));
    (a1, a2, fresh)
}

/// The `referenced` op answers each request from fresh state: a source
/// rewritten under one path, its modification time unchanged, is answered
/// as a fresh child answers it. And the probe sees a cache that crosses
/// requests, planted in the oracle (`BORZOI_FCS_DUMP_PLANT`): it is not
/// vacuous.
#[test]
fn a_planted_cross_request_cache_is_caught() {
    // What an answer says, apart from the signature's bytes, which name the
    // child's own output directory (`fcs-dump`'s `unwrittenRoot`): the
    // decoded rows, FCS's view and the diagnostics.
    let decode = |line: &str| {
        let response: ReferencedResponse =
            parse_response(line).unwrap_or_else(|e| panic!("referenced: {e:?}"));
        let ReferencedResponse::Found(found) = response else {
            panic!("the probe is refused: {response:?}");
        };
        (
            crate::common::referenced::decode("Probe", &found),
            found.signature.auto_opens.clone(),
            found.signature.internals_visible_to.clone(),
            found.entities.clone(),
            found.extension_members.clone(),
            found.read_errors.clone(),
            found.diagnostics.clone(),
        )
    };
    let (a1, a2, fresh) = same_path_probe(&[]);
    assert_ne!(
        decode(&a1),
        decode(&fresh),
        "the two texts must be told apart, or the probe is vacuous"
    );
    assert_eq!(
        decode(&a2),
        decode(&fresh),
        "the oracle answered a rewritten source from an earlier request"
    );
    let (p1, p2, planted_fresh) = same_path_probe(&[("BORZOI_FCS_DUMP_PLANT", "referenced-cache")]);
    assert_eq!(p1, p2, "the planted cache answered the second request");
    assert_ne!(
        decode(&p2),
        decode(&planted_fresh),
        "the probe does not see a planted cross-request cache"
    );
}

/// A project of the request that FCS would read from its DLL instead (here a
/// type provider) refuses the request, naming that project, wherever it sits
/// in the graph: below the producer, or beside it under the consumer. A
/// dependant's check never meets a DLL the request does not name, so each
/// shape is refused, never an oracle error.
#[test]
fn a_type_provider_project_anywhere_in_the_graph_is_refused() {
    let framework: Vec<Reference> = framework_references()
        .iter()
        .cloned()
        .map(Reference::Dll)
        .collect();
    let source = |label: &str, text: &str| crate::common::temp_fs_file(label, text);
    let project = |id: &str, sources: Vec<PathBuf>, refs: &[&str]| GraphProject {
        id: plain(id),
        assembly_name: plain(id),
        target: Target::Library,
        lang_version: LangVersion::F10,
        sources,
        defines: Vec::new(),
        references: framework
            .iter()
            .cloned()
            .chain(refs.iter().map(|r| Reference::Project(plain(r))))
            .collect(),
    };
    // (shape, the producer's text, the producer's project references)
    let shapes: [(&str, &str, &[&str]); 2] = [
        (
            "below",
            "namespace Producer\ntype Ab = Provider.T\n",
            &["Provider"],
        ),
        ("beside", "namespace Producer\ntype T = int\n", &[]),
    ];
    let mut failures = Vec::new();
    for (shape, producer_text, producer_refs) in shapes {
        let request = GraphRequest::new(
            vec![
                project(
                    "Provider",
                    vec![source(
                        "referenced_tp_provider",
                        "namespace Provider\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\ntype T = int\n",
                    )],
                    &[],
                ),
                project(
                    "Producer",
                    vec![source("referenced_tp_producer", producer_text)],
                    producer_refs,
                ),
                project(
                    "Consumer",
                    vec![source(
                        "referenced_tp_consumer",
                        "module Consumer.Use\nlet x = 1\n",
                    )],
                    &["Provider", "Producer"],
                ),
            ],
            plain("Consumer"),
        )
        .expect("a valid graph request");
        let line = request
            .referenced_line(&plain("Producer"))
            .expect("the consumer references the producer");
        let answer = parse_response::<ReferencedResponse>(&invoke_fcs_dump_graph(&line));
        let refused = matches!(
            &answer,
            Ok(ReferencedResponse::Refused(r))
                if r.cause == RefusalCause::ReadsDll && r.detail.contains("Provider")
        );
        if !refused {
            failures.push(format!("{shape}: {answer:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A language version the compiler does not know, or one below the compiler's
/// support floor (whose features it has deleted, so it no longer checks as
/// that version did, `docs/ast-versioning-plan.md` D12), is refused as such
/// before FCS checks anything under it. The floor itself is answered.
#[test]
fn a_language_version_the_compiler_cannot_check_is_refused() {
    let floor = borzoi_oracle_harness::FCS_SUPPORT_FLOOR;
    let (major, minor) = floor
        .split_once('.')
        .and_then(|(a, b)| Some((a.parse::<u8>().ok()?, b.parse::<u8>().ok()?)))
        .unwrap_or_else(|| panic!("the support floor {floor} is <major>.<minor>"));
    let answer_at = |version: LangVersion| {
        let cell = GraphCell {
            lang_version: version,
            ..one("namespace N\ntype T = int\n")
        };
        let prepared = prepare(&cell);
        parse_response::<ReferencedResponse>(&invoke_fcs_dump_graph(&prepared.referenced_line()))
    };
    let mut failures = Vec::new();
    for version in [LangVersion::new(99, 0), LangVersion::new(major - 1, 0)] {
        let answer = answer_at(version);
        if !matches!(&answer, Err(ResponseError::Refused(why)) if why.contains("language version"))
        {
            failures.push(format!("{version}: {answer:?}"));
        }
    }
    let at_floor = answer_at(LangVersion::new(major, minor));
    if !matches!(at_floor, Ok(ReferencedResponse::Found(_))) {
        failures.push(format!("the floor {floor}: {at_floor:?}"));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The cell's language version is the one FCS checks the producer under: a
/// union's generated case testers (`u.IsA`) are an F# 9 feature, so the same
/// producer is rejected at F# 8 and accepted at F# 9 and 10.
#[test]
fn the_cells_language_version_reaches_fcs() {
    let text = "module Testers\ntype U = A | B\nlet isA (u: U) = u.IsA\n";
    let errors_at = |major: u8| {
        read(&GraphCell {
            lang_version: LangVersion::new(major, 0),
            ..one(text)
        })
        .errors
    };
    let (eight, nine, ten) = (errors_at(8), errors_at(9), errors_at(10));
    assert!(!eight.is_empty(), "F# 8 accepted a case tester");
    assert!(nine.is_empty(), "F# 9 rejected a case tester: {nine:?}");
    assert!(ten.is_empty(), "F# 10 rejected a case tester: {ten:?}");
}

/// What a `referenced` answer says, apart from the signature's bytes, which
/// name the child's own output directory (`fcs-dump`'s `unwrittenRoot`): the
/// decoded rows, FCS's view and the diagnostics of a reading, the cause of a
/// refusal, or the oracle's message for a request it does not answer.
fn essence(line: &str, producer: &str) -> String {
    match parse_response::<ReferencedResponse>(line) {
        Ok(ReferencedResponse::Found(found)) => format!(
            "found {:?} {:?} {:?} {:?} {:?} {:?}",
            crate::common::referenced::decode(producer, &found),
            found.signature.auto_opens,
            found.signature.internals_visible_to,
            found.entities,
            found.extension_members,
            found.diagnostics,
        ),
        Ok(ReferencedResponse::Refused(refusal)) => format!("refused {:?}", refusal.cause),
        Err(ResponseError::Refused(why)) => format!("batch error {why}"),
        Err(e) => panic!("referenced: {e:?}"),
    }
}

/// The regeneration command for `referenced_oracle`'s hostile census.
const REGENERATE_CHANGES: &str = "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-sema \
     --test all referenced_oracle::every_source_change_is_answered_as_a_fresh_child_answers_it";

/// Each way the producer's source can change between two requests to one
/// child (`hostile::fs::Change`) is answered by that child as a fresh child
/// answers it, and moves the answer, so a stale one could not pass.
#[test]
fn every_source_change_is_answered_as_a_fresh_child_answers_it() {
    use borzoi_oracle_harness::hostile::coverage;
    use borzoi_oracle_harness::hostile::fs::{Change, HostileFs};
    let census = coverage::open(file!(), "referenced_change", &[]);
    let before = b"namespace Probe\ntype First = { X: int }\n";
    let rewritten = b"namespace Probe\ntype Other = { X: int }\n";
    let resized = b"namespace Probe\ntype Resized = { X: int }\n";
    assert_eq!(before.len(), rewritten.len());
    assert_ne!(before.len(), resized.len());
    let mut failures = Vec::new();
    // `None` first: the plain case, no change, against which a mishandled
    // change would show.
    for change in std::iter::once(None).chain(Change::ALL.iter().copied().map(Some)) {
        let fs = HostileFs::new();
        let dir = fs.tree().join("src");
        std::fs::create_dir(&dir).expect("the source directory");
        let producer = dir.join("Lib.fs");
        let consumer = dir.join("Use.fs");
        std::fs::write(&consumer, "module Consumer.Use\nlet x = 1\n").expect("the consumer");
        if change != Some(Change::Appears) {
            std::fs::write(&producer, before).expect("the producer");
        }
        let after: &[u8] = match change {
            Some(Change::SameStampRewrite | Change::SameStampReplace) => rewritten,
            Some(Change::SameStampResize) => resized,
            Some(Change::Appears) | None => before,
            Some(Change::Disappears) => b"",
        };
        let framework: Vec<Reference> = framework_references()
            .iter()
            .cloned()
            .map(Reference::Dll)
            .collect();
        let project = |id: &str, source: &PathBuf, refs: &[&str]| GraphProject {
            id: plain(id),
            assembly_name: plain(id),
            target: Target::Library,
            lang_version: LangVersion::F10,
            sources: vec![source.clone()],
            defines: Vec::new(),
            references: framework
                .iter()
                .cloned()
                .chain(refs.iter().map(|r| Reference::Project(plain(r))))
                .collect(),
        };
        let line = GraphRequest::new(
            vec![
                project("Probe", &producer, &[]),
                project("Consumer", &consumer, &["Probe"]),
            ],
            plain("Consumer"),
        )
        .expect("a valid graph request")
        .referenced_line(&plain("Probe"))
        .expect("the consumer references the producer");
        let changed = with_fcs_graph_child(&[], |child: &mut BatchChild| {
            let first = child.request(&line);
            change
                .map_or(Ok(()), |change| fs.change(&producer, change, after))
                .map(|()| (first, child.request(&line)))
        });
        let Ok((first, second)) = changed else {
            failures.push(format!(
                "{change:?}: the change could not be made: {changed:?}"
            ));
            continue;
        };
        let fresh = with_fcs_graph_child(&[], |child: &mut BatchChild| child.request(&line));
        let (first, second, fresh) = (
            essence(&first, "Probe"),
            essence(&second, "Probe"),
            essence(&fresh, "Probe"),
        );
        if change.is_some() == (first == fresh) {
            failures.push(format!(
                "{change:?}: the first answer is {first}, the fresh one {fresh}"
            ));
        }
        if second != fresh {
            failures.push(format!(
                "{change:?}: the child answered {second}, a fresh child {fresh}"
            ));
        }
        let outcome = fresh.split(' ').next().unwrap_or_default().to_owned();
        census.reached(&change.iter().map(|c| c.dimension()).collect(), &outcome);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    census.finish(REGENERATE_CHANGES);
}

/// A type provider as a reference is refused before FCS reads it: the CLR
/// never unloads a provider's design-time assembly, so a later request in
/// the child could be answered from it.
#[test]
fn a_type_provider_reference_is_refused() {
    let cell = GraphCell {
        ref_libs: vec![RefLib {
            assembly_name: plain("ProviderLib"),
            files: files(&[(
                "Provider.fs",
                "namespace ProviderLib\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\ntype T = int\n",
            )]),
        }],
        ..one("namespace UsesProvider\ntype Ab = ProviderLib.T\n")
    };
    let prepared = prepare(&cell);
    let answer =
        parse_response::<ReferencedResponse>(&invoke_fcs_dump_graph(&prepared.referenced_line()));
    assert!(
        matches!(&answer, Err(ResponseError::Refused(why)) if why.contains("is a type provider")),
        "{answer:?}"
    );
}

/// Every refusal cause `fcs-dump` raises is one [`RefusalCause`] reads, and
/// every one it reads is raised there: the two lists are one.
#[test]
fn the_oracle_raises_exactly_the_refusal_causes() {
    let program =
        std::fs::read_to_string(crate::common::workspace_root().join("tools/fcs-dump/Program.fs"))
            .expect("read fcs-dump's source");
    let raised: BTreeSet<String> = program
        .split("OracleRefusal(")
        .skip(1)
        .filter_map(|rest| rest.trim_start().strip_prefix('"'))
        .map(|rest| rest.split('"').next().unwrap_or_default().to_owned())
        .collect();
    let read: BTreeSet<String> = RefusalCause::ALL.iter().map(|c| format!("{c:?}")).collect();
    assert_eq!(raised, read);
}
