//! Generative **record-label table** differential vs FCS
//! ([`ResolvedFile::field_label_on_unknown_receiver`]).
//!
//! `let f p = p.A` gives `p` a type through the label alone: FCS's member
//! lookup on a receiver it knows nothing about finds nothing, so it looks `A`
//! up in its record-label table, where the latest declaration of the label
//! wins (`ResolveExprDotLongIdent`, NameResolution.fs). Which declaration is
//! latest depends on everything that adds labels to the environment, so the
//! harness generates programs from those additions rather than naming shapes
//! one at a time:
//!
//! - **records** — one per `type`, or an `and` pair; generic or not; struct or
//!   not; `[<RequireQualifiedAccess>]` (whose labels FCS never adds) or not;
//!   each declaring a random subset of three labels, so labels collide;
//! - **nested modules** — plain, `[<AutoOpen>]` (whose records join the
//!   enclosing scope when it closes) or `rec` (whose records are all in scope
//!   from its start);
//! - **opens** — of an earlier file's module, or of a module declared earlier
//!   in the same block;
//! - **cross-file** — an earlier file's fragment of the probe's own namespace,
//!   which entering the namespace opens;
//! - **types that are not records** declaring a member, union field or
//!   abbreviation of the label, which add nothing;
//! - **extensions** — an `[<AutoOpen>]` module extending `obj` with a member of
//!   the label's name, which FCS's member lookup finds before the table;
//! - **`System.Object`'s members** — a field named `ToString`, which that
//!   lookup also finds first, on the `obj` every type variable's hierarchy
//!   holds;
//! - **FSharp.Core** — the label `contents`, which its `Ref` cell puts in the
//!   table ahead of everything, and `open`s of its namespaces, one of which
//!   adds it again;
//! - the probe itself, `p.L` or `(id p).L`, wherever an item may stand.
//!
//! Three properties are checked at every probe:
//!
//! 1. **The model is FCS.** The harness's own model of the table (the events
//!    above, scanned latest first) must predict exactly what FCS reports: the
//!    field, no field use (the label is not in the table, FS0072), or a member
//!    that is not a field (an extension). It is a check on the harness, and the
//!    specification the resolver is held to.
//! 2. **Certain implies exact.** Where the resolver answers, FCS must report
//!    that very field.
//! 3. **Must commit.** Where the model's winner is a record the resolver
//!    models — declared in the file in the probe's scope, directly or through
//!    an `[<AutoOpen>]` module, with no `open` after it in scope, outside a
//!    `rec` module, in a file whose opens and extensions leave the label's
//!    name provably unextended — the resolver must answer.
//!
//! The probes run in four files of one project: the earlier file holding the
//! opened modules and namespace fragments, then a file with none of the
//! below, a file with extensions, and a file with opens and `rec` modules.
//! The extension gate is file-wide (`ExtensionScope`), and declines every
//! label in a file with an open of a project module or with an attribute
//! the resolver does not pin (as in a `rec` module), and in every file after
//! the latter; so the files keep each kind of item from silencing the
//! others' probes. Floors on every dimension the generator mixes keep the
//! sweep from going vacuous.

use std::ops::Range;
use std::path::PathBuf;

use crate::common::project_grade::{Cell, Tally as GradeTally, assert_clean, check};
use crate::common::{
    NormalisedProjectUse, fsharp_core_env, invoke_fcs_dump_project_with_refs,
    parse_fcs_uses_project, temp_fs_file,
};
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange};
use borzoi_sema::{
    ProjectFile, SourceFile, SyntaxRecovery, qualified_names, resolve_project_files,
};

/// The labels records draw from, so that they collide. `contents` is also
/// FSharp.Core's `Ref` cell's field, which the implicit open of
/// `Microsoft.FSharp.Core` puts in every table first.
const LABELS: [&str; 4] = ["A", "B", "C", "contents"];

/// A label that is also a public member of `System.Object`, which FCS's
/// member lookup on an unknown receiver finds before the table.
const OBJECT_MEMBER: &str = "ToString";

/// FSharp.Core's `Ref.contents`.
fn core_contents() -> FieldId {
    FieldId {
        file: usize::MAX,
        record: "Ref".to_string(),
        label: "contents",
    }
}

/// splitmix64: deterministic, so a failure reproduces from its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(n).unwrap()).unwrap()
    }

    /// `true` with probability `num / den`.
    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.next() % den < num
    }

    fn label(&mut self) -> &'static str {
        if self.chance(1, 12) {
            OBJECT_MEMBER
        } else {
            LABELS[self.below(LABELS.len())]
        }
    }

    /// A non-empty subset of the labels, in a random order.
    fn labels(&mut self) -> Vec<&'static str> {
        loop {
            let mut out: Vec<&'static str> = LABELS
                .iter()
                .copied()
                .filter(|_| self.chance(1, 2))
                .collect();
            if out.is_empty() {
                continue;
            }
            if self.chance(1, 8) {
                out.push(OBJECT_MEMBER);
            }
            for i in (1..out.len()).rev() {
                out.swap(i, self.below(i + 1));
            }
            return out;
        }
    }
}

/// The project's files, in Compile order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FileKind {
    /// The earlier file: the opened modules and the probe namespaces'
    /// fragments.
    Lib,
    /// Probe blocks with no extension and no open of a project module.
    Clean,
    /// Probe blocks with extensions.
    Ext,
    /// Probe blocks with opens of project modules, and attributes in `rec`
    /// modules, last: such an attribute is one the resolver does not pin,
    /// which the extension gate reads as a possible extension in this file
    /// and every later one.
    Opens,
}

const FILES: [FileKind; 4] = [
    FileKind::Lib,
    FileKind::Clean,
    FileKind::Ext,
    FileKind::Opens,
];

/// One field of one generated record.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FieldId {
    file: usize,
    record: String,
    label: &'static str,
}

/// Who may read a record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Access {
    Public,
    /// `type private R`: only its module, which no `open` or
    /// `[<AutoOpen>]` close leaves.
    PrivateType,
    /// `type internal R`: the whole project.
    InternalType,
    /// `type R = private { … }`: the type is public, its fields are its
    /// module's.
    PrivateRepr,
}

impl Access {
    /// Whether a public record may name the type in a field, or a public
    /// abbreviation abbreviate it.
    fn nameable(self) -> bool {
        matches!(self, Access::Public | Access::PrivateRepr)
    }
}

#[derive(Clone, Debug)]
struct RecordSpec {
    name: String,
    generic: bool,
    rqa: bool,
    is_struct: bool,
    access: Access,
    labels: Vec<&'static str>,
    /// Whether the first field of a non-generic record has the type of the
    /// latest nameable record in scope, if any, for a chain to read through.
    linked: bool,
    /// A member whose body is a probe of this label: FCS reads the record's
    /// own labels there ahead of the table.
    member_probe: Option<&'static str>,
}

/// A field's type, as a chain through it reads it.
#[derive(Clone, Debug)]
enum FieldTy {
    Prim,
    /// The record's type parameter: FCS freshens it, so a label after it is
    /// on an unknown receiver again.
    Param,
    /// Another generated record, by its file and name.
    Record(usize, String),
}

#[derive(Clone, Copy, Debug)]
enum NonRecord {
    Class,
    UnionField,
    Abbreviation,
}

#[derive(Clone, Debug)]
enum OpenTarget {
    /// `L{i}.M` in the earlier file.
    Lib,
    /// A module declared earlier in the same block, at its top level.
    Sibling(String),
    /// `Microsoft.FSharp.Core`, which adds `Ref.contents` again.
    Core,
    /// `Microsoft.FSharp.Collections`, which adds no label.
    Collections,
}

#[derive(Clone, Debug)]
enum Item {
    Records(Vec<RecordSpec>),
    Module {
        name: String,
        auto_open: bool,
        rec: bool,
        private: bool,
        items: Vec<Item>,
    },
    Open(OpenTarget),
    NonRecord(NonRecord, &'static str),
    /// An `[<AutoOpen>]` module extending `obj` with a member of this name.
    Extension(&'static str),
    Probe {
        label: &'static str,
        dot_get: bool,
        /// A second label after the first, `p.L1.L2`, chosen at emission
        /// by this seed: one of the first field's record's labels, where the
        /// model's first field has a record type, so the chain reads through
        /// it.
        chain: Option<u64>,
    },
}

/// Fresh names, unique across the project.
#[derive(Default)]
struct Names(usize);

impl Names {
    fn next(&mut self, prefix: &str) -> String {
        self.0 += 1;
        format!("{prefix}{}", self.0)
    }
}

/// A record; with `attributes` false, one with none (`[<Struct>]`,
/// `[<RequireQualifiedAccess>]`).
fn gen_record(rng: &mut Rng, names: &mut Names, attributes: bool) -> RecordSpec {
    RecordSpec {
        name: names.next("R"),
        generic: rng.chance(1, 4),
        rqa: attributes && rng.chance(1, 5),
        is_struct: attributes && rng.chance(1, 7),
        access: match rng.below(8) {
            0 => Access::PrivateType,
            1 => Access::InternalType,
            2 => Access::PrivateRepr,
            _ => Access::Public,
        },
        labels: rng.labels(),
        linked: rng.chance(1, 2),
        member_probe: rng.chance(1, 6).then(|| rng.label()),
    }
}

/// A probe, with a second label after the first now and then.
///
/// No chain follows `ToString`: a label after a method value is one on a
/// function type, which FCS reads off its table too, and which the model
/// leaves alone.
fn gen_probe(rng: &mut Rng, dot_get: bool) -> Item {
    let label = rng.label();
    Item::Probe {
        label,
        dot_get,
        chain: (label != OBJECT_MEMBER && rng.chance(1, 3)).then(|| rng.next()),
    }
}

fn gen_records(rng: &mut Rng, names: &mut Names, attributes: bool) -> Item {
    let n = if rng.chance(1, 4) { 2 } else { 1 };
    Item::Records((0..n).map(|_| gen_record(rng, names, attributes)).collect())
}

/// The items of one block or module body. `siblings` collects the modules a
/// later sibling `open` may name: top-level, not `rec`, with no nested module.
fn gen_items(
    rng: &mut Rng,
    names: &mut Names,
    kind: FileKind,
    depth: usize,
    in_rec: bool,
    siblings: &mut Vec<String>,
) -> Vec<Item> {
    let len = 1 + rng.below(if depth == 0 { 8 } else { 4 });
    let mut items = Vec::new();
    for _ in 0..len {
        let pick = rng.below(16);
        let item = match pick {
            // An attribute in a `rec` module is one the resolver does not
            // pin, which shuts the extension gate on the whole file.
            0..=4 => gen_records(rng, names, !in_rec || kind == FileKind::Opens),
            5..=8 => {
                let dot_get = rng.chance(1, 4);
                gen_probe(rng, dot_get)
            }
            9..=10 if depth < 2 && !in_rec => {
                let rec = kind != FileKind::Ext && rng.chance(1, 3);
                let auto_open = rng.chance(1, 2);
                let private = rng.chance(1, 5);
                let name = names.next("Mod");
                let mut inner_siblings = Vec::new();
                let mut body = gen_items(rng, names, kind, depth + 1, rec, &mut inner_siblings);
                if rec {
                    // A `rec` module's records are in scope from its start: a
                    // probe ahead of them is where that shows.
                    body.insert(0, gen_probe(rng, false));
                    body.push(gen_records(rng, names, kind == FileKind::Opens));
                }
                let opens_ok =
                    depth == 0 && !rec && !body.iter().any(|i| matches!(i, Item::Module { .. }));
                if opens_ok {
                    siblings.push(name.clone());
                }
                Item::Module {
                    name,
                    auto_open,
                    rec,
                    private,
                    items: body,
                }
            }
            11..=12 if kind == FileKind::Opens && !in_rec => {
                if !siblings.is_empty() && rng.chance(1, 2) {
                    let s = siblings[rng.below(siblings.len())].clone();
                    Item::Open(OpenTarget::Sibling(s))
                } else {
                    Item::Open(OpenTarget::Lib)
                }
            }
            // An open of an assembly namespace keeps the extension gate open.
            11..=12 if !in_rec => Item::Open(if rng.chance(1, 2) {
                OpenTarget::Core
            } else {
                OpenTarget::Collections
            }),
            13 if kind == FileKind::Ext && depth == 0 => Item::Extension(rng.label()),
            14 => {
                let nr = match rng.below(3) {
                    0 => NonRecord::Class,
                    1 => NonRecord::UnionField,
                    _ => NonRecord::Abbreviation,
                };
                Item::NonRecord(nr, rng.label())
            }
            _ => gen_probe(rng, false),
        };
        items.push(item);
    }
    items
}

/// Where a label in the model's table came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Origin {
    /// A record declared in the probe file, in scope.
    InFile,
    /// An in-file record an `[<AutoOpen>]` module's close brought into scope.
    Copied,
    /// A `rec` module's record, in scope from the module's start.
    RecUpfront,
    /// A record an `open` brought into scope.
    Opened,
    /// An earlier file's record in the probe's namespace.
    Implicit,
    /// FSharp.Core's `Ref`, by the implicit open of its namespace.
    Assembly,
}

#[derive(Clone, Debug)]
struct Event {
    label: &'static str,
    field: FieldId,
    origin: Origin,
    /// Where the label entered the scope.
    pos: usize,
    generic: bool,
    /// The second record of an `and` pair.
    and_second: bool,
    /// An `[<AutoOpen>]` module's close brought it here.
    copied: bool,
    access: Access,
}

#[derive(Default)]
struct Frame {
    events: Vec<Event>,
    /// Labels a skipped declaration carries: `[<RequireQualifiedAccess>]`
    /// records and the non-record types, by position.
    skipped: Vec<(&'static str, usize)>,
    opens: Vec<usize>,
    extensions: Vec<&'static str>,
    rec: bool,
}

/// What the model says FCS reports at a probe.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Prediction {
    Field(FieldId),
    /// No use: the label is not in the table (FS0072).
    Nothing,
    /// A use of something that is not a field (an extension member).
    NotAField,
}

struct Probe {
    file: usize,
    /// The probe function's name.
    binder: String,
    range: TextRange,
    label: &'static str,
    prediction: Prediction,
    winner: Option<Event>,
    must_commit: bool,
    /// The model's scan passed a skipped declaration of the label after the
    /// winner.
    passed_skipped: bool,
    /// The second label of a chain, `p.L1.L2`: its range, label and what
    /// FCS reports there, and whether FCS reads it off its label table (the
    /// first field's type is a type parameter, freshened) or off a known
    /// type.
    chain: Option<(TextRange, &'static str, Prediction, bool)>,
    /// A probe in a record's member body.
    in_member: bool,
}

/// A record's non-`[<RequireQualifiedAccess>]` labels, as the events an
/// addition of it brings. An addition from outside the record's module
/// (`foreign`) leaves a `private` record out.
fn record_events(
    file: usize,
    specs: &[RecordSpec],
    origin: Origin,
    pos: usize,
    foreign: bool,
) -> Vec<Event> {
    specs
        .iter()
        .enumerate()
        .filter(|(_, r)| !r.rqa && !(foreign && r.access == Access::PrivateType))
        .flat_map(|(i, r)| {
            r.labels.iter().map(move |&label| Event {
                label,
                field: FieldId {
                    file,
                    record: r.name.clone(),
                    label,
                },
                origin,
                pos,
                generic: r.generic,
                and_second: i == 1,
                copied: false,
                access: r.access,
            })
        })
        .collect()
}

/// FSharp.Core's `Ref.contents` entering the table.
fn core_event(origin: Origin, pos: usize) -> Event {
    Event {
        label: "contents",
        field: core_contents(),
        origin,
        pos,
        generic: true,
        and_second: false,
        copied: false,
        access: Access::Public,
    }
}

/// One file's text, the fields it declares, and its probes.
struct Emitter {
    file: usize,
    kind: FileKind,
    src: String,
    fields: Vec<(FieldId, Range<usize>)>,
    probes: Vec<Probe>,
    names: Names,
    /// The extension names the file declares anywhere (the gate is
    /// file-wide).
    file_extensions: Vec<&'static str>,
    /// Each sibling module's records, as an `open` of it adds them.
    module_records: Vec<(String, Vec<RecordSpec>)>,
    /// The nameable records declared so far and in scope, for an
    /// abbreviation or a field to name.
    abbreviable: Vec<(String, usize)>,
    /// Every generated field's type, the earlier files' included.
    field_types: std::collections::HashMap<FieldId, FieldTy>,
    /// Every generated record's labels, the earlier files' included.
    record_labels: std::collections::HashMap<(usize, String), Vec<&'static str>>,
    /// Member probes emitted with a `type` group, waiting for the group's
    /// labels to enter the table: `(binder, range, label, own record)`.
    pending_members: Vec<(String, TextRange, &'static str, RecordSpec)>,
}

fn range(start: usize, end: usize) -> TextRange {
    TextRange::new(
        u32::try_from(start).unwrap().into(),
        u32::try_from(end).unwrap().into(),
    )
}

impl Emitter {
    fn line(&mut self, indent: usize, text: &str) {
        self.src.push_str(&" ".repeat(indent * 4));
        self.src.push_str(text);
        self.src.push('\n');
    }

    /// Emit a `type` group, returning the position its labels enter at.
    /// Its member probes wait in [`Self::pending_members`].
    fn emit_records(&mut self, indent: usize, specs: &[RecordSpec]) -> usize {
        let pos = self.src.len();
        let pad = " ".repeat(indent * 4);
        for (i, r) in specs.iter().enumerate() {
            let mut attrs = Vec::new();
            if r.rqa {
                attrs.push("RequireQualifiedAccess");
            }
            if r.is_struct {
                attrs.push("Struct");
            }
            let attrs = if attrs.is_empty() {
                String::new()
            } else {
                format!("[<{}>] ", attrs.join("; "))
            };
            let access = match r.access {
                Access::PrivateType => "private ",
                Access::InternalType => "internal ",
                Access::Public | Access::PrivateRepr => "",
            };
            let repr_access = if r.access == Access::PrivateRepr {
                "private "
            } else {
                ""
            };
            let typars = if r.generic { "<'a>" } else { "" };
            if i == 0 {
                if !attrs.is_empty() {
                    self.line(indent, &attrs);
                }
                self.line(indent, &format!("type {access}{}{typars} =", r.name));
            } else {
                self.line(indent, &format!("and {attrs}{access}{}{typars} =", r.name));
            }
            self.src.push_str(&format!("{pad}    {repr_access}{{ "));
            let link = (r.linked && !r.generic)
                .then(|| self.abbreviable.last().map(|(n, _)| n.clone()))
                .flatten();
            for (k, &label) in r.labels.iter().enumerate() {
                if k > 0 {
                    self.src.push_str("; ");
                }
                let start = self.src.len();
                self.src.push_str(label);
                let end = self.src.len();
                let (ty, field_ty) = match (k, r.generic, &link) {
                    (0, true, _) => ("'a".to_string(), FieldTy::Param),
                    (0, false, Some(target)) => {
                        (target.clone(), FieldTy::Record(self.file, target.clone()))
                    }
                    (0, false, None) => ("int".to_string(), FieldTy::Prim),
                    _ => ("string".to_string(), FieldTy::Prim),
                };
                self.src.push_str(&format!(": {ty}"));
                let id = FieldId {
                    file: self.file,
                    record: r.name.clone(),
                    label,
                };
                self.field_types.insert(id.clone(), field_ty);
                self.fields.push((id, start..end));
            }
            self.src.push_str(" }\n");
            self.record_labels
                .insert((self.file, r.name.clone()), r.labels.clone());
            if let Some(label) = r.member_probe {
                let m = self.names.next("M");
                self.src.push_str(&format!("{pad}    member _.{m} p = p."));
                let start = self.src.len();
                self.src.push_str(label);
                let end = self.src.len();
                self.src.push('\n');
                self.pending_members
                    .push((m, range(start, end), label, r.clone()));
            }
        }
        pos
    }

    /// The second label of a chain whose first FCS reports as `first`: one
    /// of its record's labels where its field has a record type, any label
    /// otherwise.
    fn chain_label(&self, first: &Prediction, seed: u64) -> &'static str {
        let pick = |labels: &[&'static str]| {
            labels[usize::try_from(seed % u64::try_from(labels.len()).unwrap()).unwrap()]
        };
        if let Prediction::Field(f) = first
            && let Some(FieldTy::Record(file, name)) = self.field_types.get(f)
        {
            let labels: Vec<&'static str> = self.record_labels[&(*file, name.clone())]
                .iter()
                .copied()
                .filter(|l| *l != OBJECT_MEMBER)
                .collect();
            if !labels.is_empty() {
                return pick(&labels);
            }
        }
        pick(&LABELS)
    }

    /// The second label of a chain, after a first FCS reported as `first`.
    fn predict_chain(
        &self,
        stack: &[Frame],
        first: &Prediction,
        label: &'static str,
    ) -> Option<(Prediction, bool)> {
        let Prediction::Field(f) = first else {
            return Some((Prediction::Nothing, false));
        };
        // A `rec` module's record ahead of its declaration: its field types
        // are not settled yet, and the chain is left unpredicted.
        let ty = if *f == core_contents() {
            FieldTy::Param
        } else {
            self.field_types.get(f).cloned()?
        };
        // On a known type an intrinsic field wins, then an extension of
        // `obj` in scope, which every type has.
        let extended = || {
            if stack.iter().any(|f| f.extensions.contains(&label)) {
                Prediction::NotAField
            } else {
                Prediction::Nothing
            }
        };
        Some(match ty {
            FieldTy::Prim => (extended(), false),
            FieldTy::Param => (self.predict(stack, label).0, true),
            FieldTy::Record(file, name) => {
                let has = self.record_labels[&(file, name.clone())].contains(&label);
                let p = if has {
                    Prediction::Field(FieldId {
                        file,
                        record: name,
                        label,
                    })
                } else {
                    extended()
                };
                (p, false)
            }
        })
    }

    /// Settle the member probes of the group just entered: FCS reads the
    /// record's own labels there ahead of the table (a
    /// `[<RequireQualifiedAccess>]` record's too), which by then holds the
    /// whole group.
    fn settle_members(&mut self, stack: &[Frame]) {
        for (binder, at, label, own) in std::mem::take(&mut self.pending_members) {
            // FCS's member lookup (`obj`'s members, extensions) comes first
            // there too.
            let looked_up =
                label == OBJECT_MEMBER || stack.iter().any(|f| f.extensions.contains(&label));
            let (prediction, winner, passed_skipped) = if !looked_up && own.labels.contains(&label)
            {
                (
                    Prediction::Field(FieldId {
                        file: self.file,
                        record: own.name.clone(),
                        label,
                    }),
                    None,
                    false,
                )
            } else {
                self.predict(stack, label)
            };
            self.probes.push(Probe {
                file: self.file,
                binder,
                range: at,
                label,
                prediction,
                winner,
                must_commit: false,
                passed_skipped,
                chain: None,
                in_member: true,
            });
        }
    }

    fn predict(&self, stack: &[Frame], label: &'static str) -> (Prediction, Option<Event>, bool) {
        if label == OBJECT_MEMBER || stack.iter().any(|f| f.extensions.contains(&label)) {
            return (Prediction::NotAField, None, false);
        }
        for frame in stack.iter().rev() {
            if let Some(ev) = frame.events.iter().rev().find(|e| e.label == label) {
                let passed_skipped = stack
                    .iter()
                    .flat_map(|f| f.skipped.iter())
                    .any(|&(l, pos)| l == label && pos > ev.pos);
                return (
                    Prediction::Field(ev.field.clone()),
                    Some(ev.clone()),
                    passed_skipped,
                );
            }
        }
        (Prediction::Nothing, None, false)
    }

    fn emit_items(&mut self, indent: usize, items: &[Item], stack: &mut Vec<Frame>, lib: &Lib) {
        for item in items {
            match item {
                Item::Records(specs) => {
                    let pos = self.emit_records(indent, specs);
                    let frame = stack.last_mut().unwrap();
                    for r in specs.iter().filter(|r| r.rqa) {
                        for &l in &r.labels {
                            frame.skipped.push((l, pos));
                        }
                    }
                    if !frame.rec {
                        let events = record_events(self.file, specs, Origin::InFile, pos, false);
                        frame.events.extend(events);
                    }
                    self.settle_members(stack);
                    for r in specs.iter().filter(|r| !r.generic && r.access.nameable()) {
                        self.abbreviable.push((r.name.clone(), stack.len()));
                    }
                }
                Item::Module {
                    name,
                    auto_open,
                    rec,
                    private,
                    items,
                } => {
                    if *auto_open {
                        self.line(indent, "[<AutoOpen>]");
                    }
                    let start = self.src.len();
                    let rec_kw = if *rec { "rec " } else { "" };
                    let private_kw = if *private { "private " } else { "" };
                    self.line(indent, &format!("module {private_kw}{rec_kw}{name} ="));
                    let mut frame = Frame {
                        rec: *rec,
                        ..Frame::default()
                    };
                    if *rec {
                        for i in items {
                            if let Item::Records(specs) = i {
                                frame.events.extend(record_events(
                                    self.file,
                                    specs,
                                    Origin::RecUpfront,
                                    start,
                                    false,
                                ));
                            }
                        }
                    }
                    stack.push(frame);
                    let abbreviable = self.abbreviable.len();
                    let filler = self.names.next("filler");
                    self.line(indent + 1, &format!("let {filler} = 0"));
                    self.emit_items(indent + 1, items, stack, lib);
                    let inner = stack.pop().unwrap();
                    self.abbreviable.truncate(abbreviable);
                    // The module ends before its last line break, so an item after it is
                    // later.
                    let end = self.src.len() - 1;
                    let own: Vec<RecordSpec> = items
                        .iter()
                        .filter_map(|i| match i {
                            Item::Records(specs) => Some(specs.clone()),
                            _ => None,
                        })
                        .flatten()
                        .collect();
                    self.module_records.push((name.clone(), own));
                    if *auto_open {
                        let parent = stack.last_mut().unwrap();
                        // FCS adds the module's own records, then its
                        // `[<AutoOpen>]` submodules'.
                        let (own, submodules): (Vec<Event>, Vec<Event>) = inner
                            .events
                            .into_iter()
                            .filter(|e| {
                                matches!(
                                    e.origin,
                                    Origin::InFile | Origin::Copied | Origin::RecUpfront
                                ) && e.access != Access::PrivateType
                            })
                            .partition(|e| !e.copied);
                        parent
                            .events
                            .extend(own.into_iter().chain(submodules).map(|e| Event {
                                origin: if e.origin == Origin::RecUpfront || inner.rec {
                                    Origin::RecUpfront
                                } else {
                                    Origin::Copied
                                },
                                pos: end,
                                copied: true,
                                ..e
                            }));
                        parent
                            .skipped
                            .extend(inner.skipped.into_iter().map(|(l, _)| (l, end)));
                    }
                }
                Item::Open(target) => {
                    let pos = self.src.len();
                    let (path, events) = match target {
                        OpenTarget::Lib => (
                            format!("L{}.M", lib.scenario),
                            record_events(0, &lib.module_records, Origin::Opened, pos, true),
                        ),
                        OpenTarget::Core => (
                            "Microsoft.FSharp.Core".to_string(),
                            vec![core_event(Origin::Opened, pos)],
                        ),
                        OpenTarget::Collections => {
                            ("Microsoft.FSharp.Collections".to_string(), Vec::new())
                        }
                        OpenTarget::Sibling(m) => {
                            let specs = self
                                .module_records
                                .iter()
                                .find(|(n, _)| n == m)
                                .map(|(_, s)| s.clone())
                                .expect("a sibling module is emitted before its open");
                            // Relative: FCS does not resolve the block's own
                            // namespace by its full name inside it (FS0039).
                            (
                                m.clone(),
                                record_events(self.file, &specs, Origin::Opened, pos, true),
                            )
                        }
                    };
                    self.line(indent, &format!("open {path}"));
                    let frame = stack.last_mut().unwrap();
                    frame.opens.push(pos);
                    frame.events.extend(events);
                }
                Item::NonRecord(kind, label) => {
                    let pos = self.src.len();
                    match kind {
                        NonRecord::Class => {
                            let n = self.names.next("C");
                            self.line(indent, &format!("type {n}() ="));
                            self.line(indent + 1, &format!("member _.{label} = 1"));
                        }
                        NonRecord::UnionField => {
                            let n = self.names.next("U");
                            self.line(indent, &format!("type {n} = | {n}Case of {label}: int"));
                        }
                        NonRecord::Abbreviation => {
                            let Some((target, _)) = self.abbreviable.last().cloned() else {
                                continue;
                            };
                            let n = self.names.next("Ab");
                            self.line(indent, &format!("type {n} = {target}"));
                        }
                    }
                    stack.last_mut().unwrap().skipped.push((label, pos));
                }
                Item::Extension(label) => {
                    let n = self.names.next("Ext");
                    self.line(indent, "[<AutoOpen>]");
                    self.line(indent, &format!("module {n} ="));
                    self.line(indent + 1, "type System.Object with");
                    self.line(indent + 2, &format!("member _.{label} = 0"));
                    stack.last_mut().unwrap().extensions.push(label);
                    self.file_extensions.push(label);
                }
                Item::Probe {
                    label,
                    dot_get,
                    chain,
                } => {
                    // A namespace holds no `let`: a probe there sits in a
                    // module of its own, which adds nothing to the table.
                    let indent = if indent == 0 {
                        let q = self.names.next("Q");
                        self.line(0, &format!("module {q} ="));
                        1
                    } else {
                        indent
                    };
                    let f = self.names.next("f");
                    let head = if *dot_get {
                        format!("let {f} p = (id p).")
                    } else {
                        format!("let {f} p = p.")
                    };
                    // A chain starts, where it can, at a label whose winner
                    // has a record-typed field, so it reads through it.
                    let label: &'static str = chain
                        .and_then(|seed| {
                            let through: Vec<&'static str> = LABELS
                                .iter()
                                .copied()
                                .filter(|l| match self.predict(stack, l).0 {
                                    Prediction::Field(f) => {
                                        matches!(
                                            self.field_types.get(&f),
                                            Some(FieldTy::Record(..))
                                        )
                                    }
                                    _ => false,
                                })
                                .collect();
                            (!through.is_empty()).then(|| {
                                through[usize::try_from(
                                    (seed >> 32) % u64::try_from(through.len()).unwrap(),
                                )
                                .unwrap()]
                            })
                        })
                        .unwrap_or(label);
                    self.src.push_str(&" ".repeat(indent * 4));
                    self.src.push_str(&head);
                    let start = self.src.len();
                    self.src.push_str(label);
                    let end = self.src.len();
                    let (prediction, winner, passed_skipped) = self.predict(stack, label);
                    let chain_at = chain.map(|seed| {
                        let second = self.chain_label(&prediction, seed);
                        self.src.push('.');
                        let start = self.src.len();
                        self.src.push_str(second);
                        (range(start, self.src.len()), second)
                    });
                    self.src.push('\n');
                    let chain = chain_at.and_then(|(at, second)| {
                        let (p, unknown) = self.predict_chain(stack, &prediction, second)?;
                        Some((at, second, p, unknown))
                    });
                    let must_commit = winner.as_ref().is_some_and(|w| {
                        matches!(w.origin, Origin::InFile | Origin::Copied)
                            && !stack.iter().any(|f| f.rec)
                            && !stack
                                .iter()
                                .flat_map(|f| f.opens.iter())
                                .any(|&o| o > w.pos)
                    }) && matches!(self.kind, FileKind::Clean | FileKind::Ext);
                    self.probes.push(Probe {
                        file: self.file,
                        binder: f.clone(),
                        range: range(start, end),
                        label,
                        prediction,
                        winner,
                        must_commit,
                        passed_skipped,
                        chain,
                        in_member: false,
                    });
                }
            }
        }
    }
}

/// What the earlier file declares for one scenario.
struct Lib {
    scenario: usize,
    module_records: Vec<RecordSpec>,
    fragment: Vec<RecordSpec>,
}

struct Project {
    sources: Vec<String>,
    fields: Vec<(FieldId, Range<usize>)>,
    probes: Vec<Probe>,
}

fn build_project(seed: u64, blocks_per_file: usize) -> Project {
    let mut rng = Rng(seed);
    let mut names = Names::default();
    let probe_kinds = [FileKind::Clean, FileKind::Ext, FileKind::Opens];
    let scenarios = blocks_per_file * probe_kinds.len();

    // The earlier file.
    let mut libs = Vec::new();
    let mut lib = Emitter {
        file: 0,
        kind: FileKind::Lib,
        src: String::new(),
        fields: Vec::new(),
        probes: Vec::new(),
        names: Names::default(),
        file_extensions: Vec::new(),
        module_records: Vec::new(),
        abbreviable: Vec::new(),
        field_types: std::collections::HashMap::new(),
        record_labels: std::collections::HashMap::new(),
        pending_members: Vec::new(),
    };
    for scenario in 0..scenarios {
        let module_records: Vec<RecordSpec> = (0..1 + rng.below(3))
            .map(|_| gen_record(&mut rng, &mut names, true))
            .collect();
        lib.line(0, &format!("namespace L{scenario}"));
        lib.line(0, "module M =");
        lib.abbreviable.clear();
        for r in &module_records {
            lib.emit_records(1, std::slice::from_ref(r));
            if !r.generic && r.access.nameable() {
                lib.abbreviable.push((r.name.clone(), 0));
            }
        }
        let fragment: Vec<RecordSpec> = if rng.chance(2, 5) {
            (0..1 + rng.below(2))
                .map(|_| gen_record(&mut rng, &mut names, true))
                .collect()
        } else {
            Vec::new()
        };
        if !fragment.is_empty() {
            lib.line(0, &format!("namespace P{scenario}"));
            lib.abbreviable.clear();
            for r in &fragment {
                lib.emit_records(0, std::slice::from_ref(r));
                if !r.generic && r.access.nameable() {
                    lib.abbreviable.push((r.name.clone(), 0));
                }
            }
        }
        libs.push(Lib {
            scenario,
            module_records,
            fragment,
        });
    }

    // The earlier file's member probes are not graded: nothing types them.
    lib.pending_members.clear();
    let mut sources = vec![lib.src];
    let mut fields = lib.fields;
    let field_types = lib.field_types;
    let record_labels = lib.record_labels;
    let mut probes = Vec::new();
    for (k, &kind) in probe_kinds.iter().enumerate() {
        let file = k + 1;
        let mut e = Emitter {
            file,
            kind,
            src: String::new(),
            fields: Vec::new(),
            probes: Vec::new(),
            names: Names(1_000_000 * file),
            file_extensions: Vec::new(),
            module_records: Vec::new(),
            abbreviable: Vec::new(),
            field_types: field_types.clone(),
            record_labels: record_labels.clone(),
            pending_members: Vec::new(),
        };
        for b in 0..blocks_per_file {
            let l = &libs[k * blocks_per_file + b];
            let mut siblings = Vec::new();
            let mut items = gen_items(&mut rng, &mut names, kind, 0, false, &mut siblings);
            items.push(gen_probe(&mut rng, false));
            e.line(0, &format!("namespace P{}", l.scenario));
            e.module_records.clear();
            e.abbreviable.clear();
            // FCS adds the assemblies' labels (with their implicit opens),
            // then the earlier files', then, entering the namespace, its
            // fragments.
            let mut events = vec![core_event(Origin::Assembly, 0)];
            // A namespace-level `private` record is the namespace's, in every
            // file of it.
            events.extend(record_events(0, &l.fragment, Origin::Implicit, 0, false));
            let mut stack = vec![Frame {
                events,
                ..Frame::default()
            }];
            e.emit_items(0, &items, &mut stack, l);
        }
        // The extension gate reads every extension the file declares,
        // before the probe or after it.
        for p in &mut e.probes {
            p.must_commit &= !e.file_extensions.contains(&p.label);
        }
        sources.push(e.src);
        fields.extend(e.fields);
        probes.extend(e.probes);
    }
    Project {
        sources,
        fields,
        probes,
    }
}

/// What FCS reported at a probe.
fn fcs_report(
    uses: &[NormalisedProjectUse],
    range: TextRange,
    written: &[(PathBuf, String)],
    fields: &[(FieldId, Range<usize>)],
) -> Prediction {
    let (s, e) = (usize::from(range.start()), usize::from(range.end()));
    // FCS reports a field reached through a path at the whole path (`p.A`),
    // and one through an expression at the label: either way, the use ends
    // where the label does and covers it. Nothing else in a probe line does.
    let Some(u) = uses
        .iter()
        .find(|u| u.start <= s && u.end == e && !u.is_from_definition)
    else {
        return Prediction::Nothing;
    };
    if u.kind.as_deref() != Some("field") {
        return Prediction::NotAField;
    }
    let Some(decl) = u.decl.as_ref() else {
        assert_eq!(
            (u.assembly.as_deref(), u.full_name.as_deref()),
            (
                Some("FSharp.Core"),
                Some("Microsoft.FSharp.Core.Ref<_>.contents")
            ),
            "FCS named an assembly field the harness does not know: {u:?}"
        );
        return Prediction::Field(core_contents());
    };
    let file = written
        .iter()
        .position(|(p, _)| p.file_name() == decl.file.file_name())
        .expect("the declaring file is one of the project's");
    let field = fields
        .iter()
        .find(|(f, r)| f.file == file && r.start == decl.start && r.end == decl.end)
        .unwrap_or_else(|| panic!("FCS named an ungenerated field at {decl:?}"));
    Prediction::Field(field.0.clone())
}

#[derive(Default, Debug)]
struct Tally {
    probes: usize,
    fcs_fields: usize,
    must_commit: usize,
    committed: usize,
    declined_fields: usize,
    not_a_field: usize,
    nothing: usize,
    by_origin: [usize; 6],
    generic_winners: usize,
    and_second_winners: usize,
    passed_skipped: usize,
    dot_get_commits: usize,
    /// Chains whose second label FCS resolves through a known record.
    chain_known_fields: usize,
    /// Chains whose second label FCS resolves through its table again.
    chain_table_fields: usize,
    /// Member probes FCS resolves to their own record's field.
    member_own_fields: usize,
    /// Member probes FCS resolves through the table.
    member_table_fields: usize,
    /// Winners whose record is not plain public.
    restricted_winners: usize,
}

fn origin_index(o: Origin) -> usize {
    match o {
        Origin::InFile => 0,
        Origin::Copied => 1,
        Origin::RecUpfront => 2,
        Origin::Opened => 3,
        Origin::Implicit => 4,
        Origin::Assembly => 5,
    }
}

fn run(seed: u64, blocks_per_file: usize) -> Tally {
    let project = build_project(seed, blocks_per_file);
    let written: Vec<(PathBuf, String)> = project
        .sources
        .iter()
        .zip(FILES)
        .map(|(src, kind)| {
            (
                temp_fs_file(&format!("record_label_{kind:?}"), src),
                src.clone(),
            )
        })
        .collect();
    if let Ok(dir) = std::env::var("BORZOI_RECORD_LABEL_DUMP") {
        for ((_, src), kind) in written.iter().zip(FILES) {
            std::fs::write(format!("{dir}/{kind:?}.fs"), src).expect("dump a generated file");
        }
    }
    let paths: Vec<&std::path::Path> = written.iter().map(|(p, _)| p.as_path()).collect();
    let json = invoke_fcs_dump_project_with_refs(&paths, &[]);
    let fcs_files = parse_fcs_uses_project(&json, &written);

    let env = fsharp_core_env();
    // The table answers only on syntax that parsed cleanly, so the
    // resolver is told what the parse recovered from (nothing).
    let parsed: Vec<(SourceFile, SyntaxRecovery)> = written
        .iter()
        .map(|(_, src)| {
            let p = parse(src);
            assert!(
                p.errors.is_empty(),
                "parse errors in generated source:\n{src}"
            );
            let recovery = SyntaxRecovery::of(&p);
            let file = ImplFile::cast(p.root).expect("impl file");
            (SourceFile::Impl(file), recovery)
        })
        .collect();
    let srcs: Vec<SourceFile> = parsed.iter().map(|(f, _)| f.clone()).collect();
    let file_paths: Vec<PathBuf> = written.iter().map(|(p, _)| p.clone()).collect();
    let files: Vec<ProjectFile> = parsed
        .into_iter()
        .zip(qualified_names(&srcs, &file_paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect();
    let proj = resolve_project_files(&files, env);
    for (p, _) in &written {
        let _ = std::fs::remove_file(p);
    }

    let mut t = Tally::default();
    for probe in &project.probes {
        let (path, src) = &written[probe.file];
        let fu = fcs_files
            .iter()
            .find(|f| f.path.file_name() == path.file_name())
            .unwrap_or_else(|| panic!("FCS reported no uses for {path:?}"));
        let line = src[..usize::from(probe.range.start())]
            .matches('\n')
            .count()
            + 1;
        let ctx = format!(
            "seed {seed:#x}, {:?} line {line}: `{}` (label {})",
            FILES[probe.file],
            src.lines().nth(line - 1).unwrap_or_default().trim(),
            probe.label
        );
        let fcs = fcs_report(&fu.uses, probe.range, &written, &project.fields);
        if probe.prediction != fcs {
            let near: Vec<&NormalisedProjectUse> = fu
                .uses
                .iter()
                .filter(|u| u.start.abs_diff(usize::from(probe.range.start())) < 40)
                .collect();
            panic!(
                "{ctx}: the harness's model of the label table disagrees with FCS\n  \
                 model: {:?}\n  FCS: {fcs:?}\n  FCS uses near the probe: {near:#?}\n  \
                 FCS errors in the file: {:#?}",
                probe.prediction, fu.errors
            );
        }
        t.probes += 1;
        match &fcs {
            Prediction::Field(_) => t.fcs_fields += 1,
            Prediction::NotAField => t.not_a_field += 1,
            Prediction::Nothing => t.nothing += 1,
        }
        if let Some(w) = &probe.winner {
            t.by_origin[origin_index(w.origin)] += 1;
            t.generic_winners += usize::from(w.generic);
            t.and_second_winners += usize::from(w.and_second);
        }
        t.passed_skipped += usize::from(probe.passed_skipped);
        if let Some(w) = &probe.winner {
            t.restricted_winners += usize::from(w.access != Access::Public);
        }
        if probe.in_member && matches!(fcs, Prediction::Field(_)) {
            if probe.winner.is_none() {
                t.member_own_fields += 1;
            } else {
                t.member_table_fields += 1;
            }
        }
        if let Some((at, second, predicted, unknown)) = &probe.chain {
            let fcs2 = fcs_report(&fu.uses, *at, &written, &project.fields);
            assert_eq!(
                predicted, &fcs2,
                "{ctx}: the model disagrees with FCS at the chain's second label `{second}`"
            );
            if matches!(fcs2, Prediction::Field(_)) {
                if *unknown {
                    t.chain_table_fields += 1;
                } else {
                    t.chain_known_fields += 1;
                }
            }
            // On a receiver FCS knows nothing about, the table's answer is
            // FCS's; on one it knows, the answer makes no claim.
            if *unknown
                && let Some(label) = proj
                    .file(probe.file)
                    .field_label_on_unknown_receiver(*at, env)
            {
                let ours = project
                    .fields
                    .iter()
                    .find(|(f, r)| {
                        f.file == probe.file
                            && r.start == usize::from(label.field.start())
                            && r.end == usize::from(label.field.end())
                    })
                    .map(|(f, _)| f.clone());
                assert_eq!(
                    ours.map(Prediction::Field),
                    Some(fcs2),
                    "{ctx}: we resolved the chain's second label `{second}` to {label:?}"
                );
            }
        }

        let ours = proj
            .file(probe.file)
            .field_label_on_unknown_receiver(probe.range, env);
        match ours {
            Some(label) => {
                t.committed += 1;
                let ours = project
                    .fields
                    .iter()
                    .find(|(f, r)| {
                        f.file == probe.file
                            && r.start == usize::from(label.field.start())
                            && r.end == usize::from(label.field.end())
                    })
                    .map(|(f, _)| f.clone())
                    .unwrap_or_else(|| panic!("{ctx}: we named no generated field: {label:?}"));
                assert_eq!(
                    fcs,
                    Prediction::Field(ours.clone()),
                    "{ctx}: we resolved the label to {ours:?}"
                );
                if src[..usize::from(probe.range.start())].ends_with("(id p).") {
                    t.dot_get_commits += 1;
                }
            }
            None => {
                if matches!(fcs, Prediction::Field(_)) {
                    t.declined_fields += 1;
                }
                assert!(
                    !probe.must_commit,
                    "{ctx}: FCS resolves the label to {fcs:?}, a record the resolver models, \
                     and we declined"
                );
            }
        }
        t.must_commit += usize::from(probe.must_commit);
    }
    t
}

/// Floors on everything the generator mixes, so a change that stops a
/// dimension from being exercised fails rather than passes vacuously. Each
/// is about half what a sweep of 100 blocks per file produces or less,
/// scaled to `blocks`.
fn assert_floors(t: &Tally, blocks: usize) {
    eprintln!("record-label sweep: {t:?}");
    let [in_file, copied, rec, opened, implicit, assembly] = t.by_origin;
    for (what, n, floor) in [
        ("probes FCS resolves to a field", t.fcs_fields, 350),
        ("must-commit probes", t.must_commit, 70),
        ("probes FCS resolves and we decline", t.declined_fields, 250),
        ("probes no label answers (FS0072)", t.nothing, 200),
        ("probes a member answers", t.not_a_field, 40),
        ("winners declared in the file", in_file, 230),
        ("winners an AutoOpen module brought", copied, 18),
        ("winners in a rec module", rec, 40),
        ("winners an open brought", opened, 25),
        ("winners from an earlier file's fragment", implicit, 60),
        ("winners from FSharp.Core", assembly, 30),
        ("generic winners", t.generic_winners, 90),
        ("winners second in an and pair", t.and_second_winners, 100),
        ("scans past a skipped declaration", t.passed_skipped, 30),
        (
            "commits through a parenthesised receiver",
            t.dot_get_commits,
            7,
        ),
        (
            "chains read through a known record",
            t.chain_known_fields,
            20,
        ),
        (
            "chains read through the table again",
            t.chain_table_fields,
            15,
        ),
        ("member probes on their own record", t.member_own_fields, 15),
        ("member probes through the table", t.member_table_fields, 5),
        ("winners not plain public", t.restricted_winners, 60),
    ] {
        let floor = floor * blocks / 100;
        assert!(n >= floor, "only {n} {what} (floor {floor}): {t:?}");
    }
}

#[test]
fn record_labels_agree_with_fcs() {
    let t = run(0x5EED_0707, 100);
    assert_floors(&t, 100);
}

/// A larger sweep over fresh seeds: `BORZOI_RECORD_LABEL_SEEDS` seeds (default
/// 8) of `BORZOI_RECORD_LABEL_BLOCKS` blocks per file (default 100).
#[test]
#[ignore = "deep sweep; minutes of FCS time"]
fn deep_record_labels_agree_with_fcs() {
    let seeds: u64 = std::env::var("BORZOI_RECORD_LABEL_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8);
    let blocks: usize = std::env::var("BORZOI_RECORD_LABEL_BLOCKS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    for seed in 0..seeds {
        let t = run(0xDEE9_0000 + seed, blocks);
        assert_floors(&t, blocks);
    }
}

/// Inference reads the answer: over the same generated programs, every node
/// and binder it types in any file must be FCS's, nothing may commit on a
/// line FCS rejects, and each must-commit probe's function must be typed
/// (its receiver fixed to the record, its result to the field). Each probe
/// file is checked after the earlier file alone, which is all it reads.
#[test]
fn record_labels_type_receivers_as_fcs_does() {
    let project = build_project(0x5EED_0707, 100);
    if let Ok(dir) = std::env::var("BORZOI_RECORD_LABEL_DUMP") {
        for (src, kind) in project.sources.iter().zip(FILES) {
            std::fs::write(format!("{dir}/{kind:?}.fs"), src).expect("dump a generated file");
        }
    }
    let mut tally = GradeTally::default();
    let mut obligated = 0;
    for (file, kind) in FILES.iter().enumerate().skip(1) {
        let sources = vec![
            ("Lib.fs".to_string(), project.sources[0].clone()),
            (format!("{kind:?}.fs"), project.sources[file].clone()),
        ];
        let src = &project.sources[file];
        let cells: Vec<Cell> = project
            .probes
            .iter()
            .filter(|p| p.file == file)
            .map(|p| {
                let line = src[..usize::from(p.range.start())].matches('\n').count() + 1;
                // A member access on a receiver whose type has open
                // arguments publishes nothing yet, whatever typed the
                // receiver: so a generic record obligates nothing here.
                // Inference reads a field off a record only where it bridges
                // the field's type and may read the representation, which a
                // chain's first field and a `private` representation do not
                // always allow: those are graded for agreement alone.
                let must = p.must_commit
                    && p.chain.is_none()
                    && p.winner
                        .as_ref()
                        .is_some_and(|w| !w.generic && w.access != Access::PrivateRepr);
                obligated += usize::from(must);
                (
                    u32::try_from(line).unwrap(),
                    p.binder.clone(),
                    must,
                    format!("{kind:?} line {line}: {}", p.binder),
                )
            })
            .collect();
        check(&sources, &cells, &mut tally);
    }
    assert_eq!(
        tally.committed_erroring, 0,
        "cells committed on lines FCS rejects: {tally:?}"
    );
    assert_clean(&tally, obligated);
    assert!(obligated >= 30, "only {obligated} obligated probes");
}
