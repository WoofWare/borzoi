//! Generated producer projects for `source_existence_diff`: random
//! declaration trees over every production of the walk's domain, combined,
//! nested and repeated as no hand-written cell would, with one production
//! from outside the domain in some.
//!
//! Three properties, beside containment (`source_existence_diff::grade`):
//!
//! - a producer of in-domain productions alone is **read**: the walk does not
//!   decline its own domain;
//! - a producer holding an out-of-domain production **declines**, with that
//!   production's form as the reason;
//! - the **production census**: every production is drawn in the pinned run,
//!   each in-domain one in a case FCS and the walk both read, and the counts
//!   are pinned (`tests/manifests/source_existence_gen_productions.txt`).
//!
//! One case in `hostile::RATE` has a hostile source state mixed into one of
//! its files (hostile census `source_existence_gen`); such a case is held
//! to containment only, since the state may move it out of the domain.

use std::collections::{BTreeMap, BTreeSet};

use borzoi_oracle_harness::hostile::census::Census;
use borzoi_oracle_harness::hostile::{self, Dimension, Kind as HostileKind, coverage, source};
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_sema::{ExistenceUnread, Form, SourceExistence};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells, graded};

/// A small deterministic generator (xorshift64*), so a case is its seed.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

/// Every production the generator draws: the walk's domain, and, after
/// `Outside`, one form from outside it per production.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Production {
    Namespace,
    DottedNamespace,
    RecNamespace,
    GlobalNamespace,
    ModuleHeader,
    NestedModule,
    EmptyModule,
    ModuleBesideType,
    Record,
    Union,
    Class,
    Interface,
    Struct,
    Enum,
    Delegate,
    GenericType,
    AndGroup,
    CoreAbbreviation,
    StructuralAbbreviation,
    Augmentation,
    Exception,
    ExceptionAbbreviation,
    Let,
    AttributedLet,
    Open,
    ModuleAbbreviation,
    /// A keyword as a quoted name (`` ``global`` ``, `` ``type`` ``).
    QuotedKeywordName,
    // Outside the domain: each declines with its form.
    EntityAttribute,
    StandaloneAttribute,
    SuffixedModule,
    DottedType,
    SingleIdentTarget,
    NamedTarget,
    TupleAugmentation,
    ConstructorAugmentation,
    HashDirective,
    GlobalName,
    LineDirective,
}

impl Production {
    const ALL: &'static [Production] = &[
        Production::Namespace,
        Production::DottedNamespace,
        Production::RecNamespace,
        Production::GlobalNamespace,
        Production::ModuleHeader,
        Production::NestedModule,
        Production::EmptyModule,
        Production::ModuleBesideType,
        Production::Record,
        Production::Union,
        Production::Class,
        Production::Interface,
        Production::Struct,
        Production::Enum,
        Production::Delegate,
        Production::GenericType,
        Production::AndGroup,
        Production::CoreAbbreviation,
        Production::StructuralAbbreviation,
        Production::Augmentation,
        Production::Exception,
        Production::ExceptionAbbreviation,
        Production::Let,
        Production::AttributedLet,
        Production::Open,
        Production::ModuleAbbreviation,
        Production::EntityAttribute,
        Production::StandaloneAttribute,
        Production::SuffixedModule,
        Production::DottedType,
        Production::SingleIdentTarget,
        Production::NamedTarget,
        Production::TupleAugmentation,
        Production::ConstructorAugmentation,
        Production::HashDirective,
        Production::GlobalName,
        Production::LineDirective,
        Production::QuotedKeywordName,
    ];

    /// The form an out-of-domain production declines with, `None` for one
    /// in the domain.
    fn declines_with(self) -> Option<Form> {
        Some(match self {
            Production::EntityAttribute => Form::EntityAttribute,
            Production::StandaloneAttribute => Form::StandaloneAttribute,
            Production::SuffixedModule => Form::SuffixedModule,
            Production::DottedType => Form::DottedType,
            Production::SingleIdentTarget => Form::SingleIdentTarget,
            Production::NamedTarget => Form::NamedTarget,
            Production::TupleAugmentation => Form::TupleAugmentation,
            Production::ConstructorAugmentation => Form::ConstructorAugmentation,
            Production::HashDirective => Form::HashDirective,
            Production::GlobalName => Form::GlobalName,
            Production::LineDirective => Form::LineDirective,
            Production::Namespace
            | Production::DottedNamespace
            | Production::RecNamespace
            | Production::GlobalNamespace
            | Production::ModuleHeader
            | Production::NestedModule
            | Production::EmptyModule
            | Production::ModuleBesideType
            | Production::Record
            | Production::Union
            | Production::Class
            | Production::Interface
            | Production::Struct
            | Production::Enum
            | Production::Delegate
            | Production::GenericType
            | Production::AndGroup
            | Production::CoreAbbreviation
            | Production::StructuralAbbreviation
            | Production::Augmentation
            | Production::Exception
            | Production::ExceptionAbbreviation
            | Production::Let
            | Production::AttributedLet
            | Production::Open
            | Production::ModuleAbbreviation
            | Production::QuotedKeywordName => return None,
        })
    }

    const OUTSIDE: &'static [Production] = &[
        Production::EntityAttribute,
        Production::StandaloneAttribute,
        Production::SuffixedModule,
        Production::DottedType,
        Production::SingleIdentTarget,
        Production::NamedTarget,
        Production::TupleAugmentation,
        Production::ConstructorAugmentation,
        Production::HashDirective,
        Production::GlobalName,
        Production::LineDirective,
    ];
}

/// Names a type, module or exception may have: plain ones that recur (a
/// module beside a type of its name, an augmentation of a local type),
/// names FSharp.Core and the BCL also declare, backticked and Unicode names.
const ENTITY_NAMES: &[&str] = &[
    "A",
    "B",
    "Item",
    "List",
    "Option",
    "String",
    "Result",
    "Exception",
    "``My Type``",
    "``a-b``",
    "``type``",
    "Élan",
    "Мир",
    "Tуpe",
];

/// Namespace and module-header segments: no space or punctuation, which FCS
/// rejects there.
const NAMESPACE_NAMES: &[&str] = &["N", "Lib", "System", "Collections", "FSharp", "Ünï"];

const CORE_TARGETS: &[&str] = &["int", "string", "obj", "unit", "bool", "float", "exn"];

const STRUCTURAL_TARGETS: &[&str] = &[
    "int * string",
    "int -> string",
    "int[]",
    "{| X: int |}",
    "(int * int) -> unit",
];

struct Gen {
    rng: Rng,
    drawn: BTreeSet<Production>,
    /// Distinct names, so no two declarations of one scope collide unless
    /// the generator means them to.
    counter: usize,
}

impl Gen {
    fn fresh(&mut self) -> String {
        self.counter += 1;
        let base = self.rng.pick(ENTITY_NAMES);
        match base.strip_prefix("``").and_then(|b| b.strip_suffix("``")) {
            Some(inner) => format!("``{inner} {}``", self.counter),
            None => format!("{base}{}", self.counter),
        }
    }

    fn draw(&mut self, p: Production) -> Production {
        self.drawn.insert(p);
        p
    }

    /// A file: its header and its declarations, `outside` placed at its top
    /// level when given.
    fn file(&mut self, outside: Option<Production>) -> String {
        let segment = |g: &mut Gen| (*g.rng.pick(NAMESPACE_NAMES)).to_owned();
        let header = match self.rng.below(5) {
            0 => {
                self.draw(Production::Namespace);
                format!("namespace {}\n", segment(self))
            }
            1 => {
                self.draw(Production::DottedNamespace);
                format!(
                    "namespace {}.{}.{}\n",
                    segment(self),
                    segment(self),
                    segment(self)
                )
            }
            2 => {
                self.draw(Production::RecNamespace);
                format!("namespace rec {}\n", segment(self))
            }
            3 => {
                self.draw(Production::GlobalNamespace);
                "namespace global\n".to_owned()
            }
            _ => {
                self.draw(Production::ModuleHeader);
                format!("module {}.M{}\n", segment(self), self.rng.below(100))
            }
        };
        // A namespace holds no `let`, so its body is a module's.
        let module_header = header.starts_with("module ");
        let mut text = header;
        if !module_header {
            let name = format!("Body{}", self.rng.below(100));
            self.draw(Production::NestedModule);
            text.push_str(&format!("module {name} =\n"));
            text.push_str(&self.decls(1, 3));
            text.push_str(&self.types(0));
        } else {
            text.push_str(&self.decls(0, 3));
        }
        if let Some(p) = outside {
            text.push_str(&self.outside(p, 0));
        }
        text
    }

    /// Type and exception declarations only, which a namespace may hold.
    fn types(&mut self, depth: usize) -> String {
        let mut out = String::new();
        for _ in 0..1 + self.rng.below(2) {
            out.push_str(&self.type_decl(depth));
        }
        out
    }

    fn indent(depth: usize) -> String {
        "    ".repeat(depth)
    }

    /// Between one and four declarations at `depth`, nesting at most
    /// `budget` modules deeper.
    fn decls(&mut self, depth: usize, budget: usize) -> String {
        let pad = Self::indent(depth);
        let mut out = String::new();
        for _ in 0..1 + self.rng.below(4) {
            match self.rng.below(10) {
                0 | 1 if budget > 0 => {
                    let name = self.fresh();
                    self.draw(Production::NestedModule);
                    out.push_str(&format!("{pad}module {name} =\n"));
                    out.push_str(&self.decls(depth + 1, budget - 1));
                }
                2 => {
                    let name = self.fresh();
                    self.draw(Production::EmptyModule);
                    out.push_str(&format!("{pad}module {name} = begin end\n"));
                }
                3 => {
                    let name = self.fresh();
                    self.draw(Production::ModuleBesideType);
                    out.push_str(&format!(
                        "{pad}type {name} = {{ X: int }}\n{pad}module {name} =\n{pad}    let make () = {{ X = 1 }}\n"
                    ));
                }
                4 => {
                    self.draw(Production::Let);
                    out.push_str(&format!("{pad}let v{} = 1\n", self.rng.below(1000)));
                }
                5 => {
                    self.draw(Production::AttributedLet);
                    out.push_str(&format!(
                        "{pad}[<Literal>]\n{pad}let L{} = 1\n",
                        self.rng.below(1000)
                    ));
                }
                6 => {
                    self.draw(Production::Open);
                    out.push_str(&format!("{pad}open System\n"));
                }
                8 => {
                    self.draw(Production::QuotedKeywordName);
                    let name = self.rng.pick(&["``global``", "``type``", "``module``"]);
                    out.push_str(&format!("{pad}type {name} = {{ X: int }}\n"));
                }
                7 if budget > 0 => {
                    let real = self.fresh();
                    let alias = self.fresh();
                    self.draw(Production::ModuleAbbreviation);
                    out.push_str(&format!(
                        "{pad}module {real} =\n{pad}    let x = 1\n{pad}module {alias} = {real}\n"
                    ));
                }
                _ => out.push_str(&self.type_decl(depth)),
            }
        }
        out
    }

    /// One type or exception declaration at `depth`.
    fn type_decl(&mut self, depth: usize) -> String {
        let pad = Self::indent(depth);
        let name = self.fresh();
        let p = *self.rng.pick(&[
            Production::Record,
            Production::Union,
            Production::Class,
            Production::Interface,
            Production::Struct,
            Production::Enum,
            Production::Delegate,
            Production::GenericType,
            Production::AndGroup,
            Production::CoreAbbreviation,
            Production::StructuralAbbreviation,
            Production::Augmentation,
            Production::Exception,
            Production::ExceptionAbbreviation,
        ]);
        self.draw(p);
        match p {
            Production::Record => format!("{pad}type {name} = {{ X: int }}\n"),
            Production::Union => format!("{pad}type {name} = | C1 | C2 of int\n"),
            Production::Class => format!("{pad}type {name}(x: int) =\n{pad}    member _.X = x\n"),
            Production::Interface => {
                format!("{pad}type {name} =\n{pad}    abstract M: int -> int\n")
            }
            Production::Struct => format!("{pad}type {name} = struct val X: int end\n"),
            Production::Enum => format!("{pad}type {name} = | One = 1 | Two = 2\n"),
            Production::Delegate => format!("{pad}type {name} = delegate of int -> int\n"),
            Production::GenericType => format!("{pad}type {name}<'a> = {{ V: 'a }}\n"),
            Production::AndGroup => {
                let other = self.fresh();
                format!(
                    "{pad}type {name} = {{ O: {other} option }}\n{pad}and {other} = {{ N: int }}\n"
                )
            }
            Production::CoreAbbreviation => {
                format!("{pad}type {name} = {}\n", self.rng.pick(CORE_TARGETS))
            }
            Production::StructuralAbbreviation => {
                format!("{pad}type {name} = {}\n", self.rng.pick(STRUCTURAL_TARGETS))
            }
            Production::Augmentation => format!(
                "{pad}type {name} = {{ X: int }}\n{pad}type {name} with\n{pad}    member r.Y = r.X\n"
            ),
            Production::Exception => format!("{pad}exception {name} of string\n"),
            Production::ExceptionAbbreviation => {
                let other = self.fresh();
                format!("{pad}exception {name} of string\n{pad}exception {other} = {name}\n")
            }
            other => unreachable!("{other:?} is no type declaration"),
        }
    }

    /// The out-of-domain production `p`, at `depth`.
    fn outside(&mut self, p: Production, depth: usize) -> String {
        let pad = Self::indent(depth);
        let name = self.fresh();
        self.draw(p);
        match p {
            Production::EntityAttribute => {
                format!("{pad}[<System.Obsolete>]\n{pad}type {name} = {{ X: int }}\n")
            }
            Production::StandaloneAttribute => format!("{pad}[<System.Obsolete>]\n{pad}do ()\n"),
            // A plain stem: `Module` after a backticked name is no name.
            Production::SuffixedModule => format!(
                "{pad}module Stem{}Module =\n{pad}    let x = 1\n",
                self.counter
            ),
            Production::DottedType => {
                format!("{pad}type System.String with\n{pad}    member s.M = 1\n")
            }
            Production::SingleIdentTarget => format!("{pad}type {name} = Somewhere\n"),
            Production::NamedTarget => format!("{pad}type {name} = int list\n"),
            Production::TupleAugmentation => {
                format!("{pad}type (int * int) with\n{pad}    member x.M = 1\n")
            }
            Production::ConstructorAugmentation => {
                format!("{pad}type {name}() with\n{pad}    member x.M = 1\n")
            }
            Production::HashDirective => format!("{pad}#time \"on\"\n"),
            Production::GlobalName => format!("{pad}type global = {{ X: int }}\n"),
            Production::LineDirective => format!("{pad}# 7 \"Elsewhere.fs\"\n"),
            other => unreachable!("{other:?} is in the domain"),
        }
    }
}

/// The generated case of `seed`: its cell, the productions drawn, whether
/// a hostile state was mixed in, and the out-of-domain production placed.
pub struct Case {
    pub cell: Cell,
    pub drawn: BTreeSet<Production>,
    pub outside: Option<Production>,
    /// The hostile dimension mixed into one of its files, if any.
    pub hostile: BTreeSet<Dimension>,
}

pub fn case(seed: u64) -> Case {
    let mut g = Gen {
        rng: Rng::new(seed),
        drawn: BTreeSet::new(),
        counter: 0,
    };
    // One case in three has one production from outside the domain, in turn
    // so a short run reaches each.
    let outside = (seed % 3 == 2)
        .then(|| Production::OUTSIDE[(seed / 3) as usize % Production::OUTSIDE.len()]);
    let n = 1 + g.rng.below(2);
    let mut files: Vec<(String, String)> = Vec::new();
    for i in 0..n {
        let text = g.file(if i + 1 == n { outside } else { None });
        files.push((format!("F{i}.fs"), text));
    }
    let mut cell = Cell::new(format!("gen_{seed}"), &[]);
    let mut hostile = BTreeSet::new();
    if hostile::mixes(seed) {
        let dimensions: Vec<Dimension> = HostileKind::SourceText
            .dimensions()
            .filter(|d| *d != Dimension::NotText)
            .collect();
        let turn = seed / hostile::RATE;
        let dimension = dimensions[turn as usize % dimensions.len()];
        let entries: Vec<_> = source::alphabet().of(dimension).collect();
        let entry = entries[(turn as usize / dimensions.len()) % entries.len()];
        let at = (turn as usize) % files.len();
        let text = &files[at].1;
        if entry.value.varies(text) {
            files[at].1 = String::from_utf8(entry.value.apply(text))
                .expect("a mutation of a text dimension keeps the file UTF-8");
            hostile.insert(entry.dimension);
        }
    }
    cell.graph.files = files
        .into_iter()
        .map(|(name, text)| borzoi_oracle_harness::project_graph::FixtureFile { name, text })
        .collect();
    Case {
        cell,
        drawn: g.drawn,
        outside,
        hostile,
    }
}

/// Whether the walk keeps its domain on `c`, a case with no hostile state:
/// a case of in-domain productions alone is read, and one holding an
/// out-of-domain production declines with that production's form. Judged
/// on the walk's own verdict, whatever FCS made of the case.
fn domain_failures(c: &Case) -> Option<String> {
    if !c.hostile.is_empty() {
        return None;
    }
    let ours = crate::source_existence_diff::ours(&c.cell);
    match (c.outside, &ours) {
        (None, SourceExistence::Read(_)) => None,
        (None, SourceExistence::Unread(why)) => Some(format!(
            "{}: in the domain, and the walk declines: {why:?}",
            c.cell.name
        )),
        (Some(p), ours) => {
            let form = p.declines_with().expect("an out-of-domain production");
            (!matches!(
                ours,
                SourceExistence::Unread(ExistenceUnread::Declined(_, f)) if *f == form
            ))
            .then(|| {
                format!(
                    "{}: holds {p:?}, which declines with {form:?}, and the walk gave {ours:?}",
                    c.cell.name
                )
            })
        }
    }
}

/// The census of the source mutations the generator mixes in.
fn open_census() -> Census {
    coverage::open(
        file!(),
        "source_existence_gen",
        &[(
            Dimension::NotText,
            "a cell's files are text: a Compile item that is not UTF-8 is one the caller \
             cannot read, `CompileItem::Unreadable`, which the walk's unit tests witness",
        )],
    )
}

const REGENERATE: &str = "source_existence_gen::source_rows_hold_fcs_facts_over_generated_projects";

/// The pinned default run of the generator: seeds `0..90`.
#[test]
fn source_rows_hold_fcs_facts_over_generated_projects() {
    let census = open_census();
    let cases: Vec<Case> = (0..90).map(case).collect();
    let cells: Vec<Cell> = cases.iter().map(|c| c.cell.clone()).collect();
    let (entries, mut failures) = grade_cells(&cells);
    let verdicts: BTreeMap<&str, &str> = entries
        .iter()
        .map(|(n, v)| (n.as_str(), v.as_str()))
        .collect();
    let mut productions: BTreeMap<Production, (usize, usize)> = BTreeMap::new();
    for c in &cases {
        let verdict = verdicts
            .get(c.cell.name.as_str())
            .copied()
            .unwrap_or("failed");
        census.reached(
            &c.hostile,
            verdict.split([' ', ',']).next().unwrap_or("failed"),
        );
        for p in &c.drawn {
            let slot = productions.entry(*p).or_default();
            slot.0 += 1;
            if graded(verdict) {
                slot.1 += 1;
            }
        }
        failures.extend(domain_failures(c));
    }
    if !failures.is_empty() {
        for c in &cases {
            if failures
                .iter()
                .any(|f| f.starts_with(&format!("{}:", c.cell.name)))
            {
                for f in &c.cell.graph.files {
                    eprintln!("--- {} {}\n{}", c.cell.name, f.name, f.text);
                }
            }
        }
    }
    for p in Production::ALL {
        let (drawn, graded) = productions.get(p).copied().unwrap_or_default();
        if drawn == 0 {
            failures.push(format!("{p:?} is never drawn"));
        } else if p.declines_with().is_none() && graded == 0 {
            failures.push(format!(
                "{p:?} is drawn in no case FCS and the walk both read"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
    check_manifest(
        "source_existence_gen",
        &Manifest::from_keyed(entries).expect("well-formed entries"),
        &regenerate(REGENERATE),
    );
    check_manifest(
        "source_existence_gen_productions",
        &Manifest::from_keyed(
            productions
                .iter()
                .map(|(p, (d, g))| (format!("{p:?}"), format!("drawn {d}, graded {g}")))
                .collect::<Vec<(String, String)>>(),
        )
        .expect("well-formed entries"),
        &regenerate(REGENERATE),
    );
    census.finish(&regenerate(REGENERATE));
}

/// The generator over more seeds: `BORZOI_SOURCE_EXISTENCE_SEED` (default
/// 1000) and `BORZOI_SOURCE_EXISTENCE_CASES` (default 400). Pins nothing:
/// every property but the census must hold.
#[test]
#[ignore = "hundreds of FCS checks; the default run is the gate"]
fn deep_source_rows_hold_fcs_facts_over_generated_projects() {
    let var = |name: &str, default: u64| {
        std::env::var(name)
            .ok()
            .map(|v| v.parse().expect("a count"))
            .unwrap_or(default)
    };
    let first = var("BORZOI_SOURCE_EXISTENCE_SEED", 1000);
    let count = var("BORZOI_SOURCE_EXISTENCE_CASES", 400);
    let cases: Vec<Case> = (first..first + count).map(case).collect();
    let cells: Vec<Cell> = cases.iter().map(|c| c.cell.clone()).collect();
    let (_, mut failures) = grade_cells(&cells);
    failures.extend(cases.iter().filter_map(domain_failures));
    show_failing(&cases, &failures);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

/// Print each failing case's files.
fn show_failing(cases: &[Case], failures: &[String]) {
    for c in cases {
        if failures
            .iter()
            .any(|f| f.starts_with(&format!("{}:", c.cell.name)))
        {
            for f in &c.cell.graph.files {
                eprintln!("--- {} {}\n{}", c.cell.name, f.name, f.text);
            }
        }
    }
}
