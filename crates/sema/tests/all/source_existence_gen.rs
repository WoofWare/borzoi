//! Generated producer projects for `source_existence_diff`: random
//! declaration trees over every declaration form, accessibility, attribute
//! spelling and name shape the grid has, combined, nested and repeated as
//! no hand-written cell would.
//!
//! Names are drawn from a hostile pool: names FSharp.Core and the BCL also
//! declare, backticked names with spaces and punctuation, keywords, Unicode
//! letters and confusables, and a long name; and from a small plain pool, so
//! the same name recurs (a module beside a type of its name, duplicates
//! across files, an augmentation of a local type).

use borzoi_oracle_harness::hostile::census::Census;
use borzoi_oracle_harness::hostile::{self, Dimension, Kind as HostileKind, coverage, source};
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::Target;

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells};

/// The hostile dimensions mixed into a cell's source, which the cell
/// carries to where the walk reads it.
pub type Hostile = std::collections::BTreeSet<Dimension>;

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

    pub fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

/// Names a type, module or exception may have.
const ENTITY_NAMES: &[&str] = &[
    "A",
    "B",
    "Item",
    "Value",
    "List",
    "Option",
    "String",
    "Map",
    "Seq",
    "Result",
    "Exception",
    "Attribute",
    "``My Type``",
    "``a-b``",
    "``1st``",
    "``type``",
    "``member``",
    "Élan",
    "Ωmega",
    "Мир",
    "Tуpe",
    "ℕat",
    "VeryLongNameThatGoesOnAndOnForQuiteSomeTimeIndeed",
];

/// Namespace segments: no space or punctuation, which FCS rejects there.
const NAMESPACE_NAMES: &[&str] = &[
    "N",
    "Lib",
    "System",
    "Collections",
    "Microsoft",
    "FSharp",
    "Core",
    "Ünï",
    "Deep",
];

/// Member names an augmentation or a type declares.
const MEMBER_NAMES: &[&str] = &["M", "Length", "Item", "ToString", "``odd member``", "Ωp"];

/// Names a type's `let`s, constructor arguments, self identifier, fields and
/// `[<CompiledName>]`s share, so that one takes another's (and FCS mangles
/// it, `f@7`).
const LET_NAMES: &[&str] = &[
    "f",
    "g",
    "arg",
    "self",
    "fld",
    "Q",
    "patternInput",
    "``f@4``",
];

/// What an augmentation may extend.
const EXTENDED: &[&str] = &[
    "System.String",
    "System.Int32",
    "List<'T>",
    "System.Collections.Generic.Dictionary<'K, 'V>",
];

struct Gen {
    rng: Rng,
    /// Types declared so far in this file: name, and whether generic. For
    /// augmentations and abbreviations.
    declared: Vec<(String, bool, Kind)>,
}

/// A type definition's kind, which decides the attributes FCS accepts on it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Record,
    Union,
    Class,
    Interface,
    Enum,
    Delegate,
    Abbreviation,
    StaticHolder,
    CSharpHolder,
    Measure,
}

impl Gen {
    fn entity_name(&mut self) -> String {
        // The name of a marker attribute A may declare, rarely: the
        // certificate then cannot vouch for that marker's spelling.
        if self.rng.chance(2) {
            return "AutoOpenAttribute".to_owned();
        }
        (*self.rng.pick(ENTITY_NAMES)).to_owned()
    }

    /// A name that may label an exception: upper case first.
    fn upper_name(&mut self) -> String {
        loop {
            let n = self.entity_name();
            let first = n.trim_start_matches('`').chars().next();
            if first.is_some_and(char::is_uppercase) {
                return n;
            }
        }
    }

    fn access(&mut self) -> &'static str {
        self.rng
            .pick(&["", "", "", "private ", "internal ", "public "])
    }

    /// Attributes FCS accepts on a type of `kind`, or none.
    fn type_attributes(&mut self, indent: &str, kind: Kind) -> String {
        let choices: &[&str] = match kind {
            Kind::Record => &[
                "[<Struct>]",
                "[<CompiledName(\"Renamed\")>]",
                "[<RequireQualifiedAccess>]",
                "[<AutoOpen>]",
            ],
            Kind::Union => &[
                "[<Struct>]",
                "[<CompiledName(\"Renamed\")>]",
                "[<RequireQualifiedAccess>]",
            ],
            Kind::Class => &[
                "[<AutoOpen>]",
                "[<CompiledName(\"Renamed\")>]",
                "[<AbstractClass>]",
            ],
            Kind::Enum => &["[<RequireQualifiedAccess>]"],
            Kind::Abbreviation => &[
                "[<AutoOpen>]",
                "[<System.Runtime.CompilerServices.Extension>]",
            ],
            Kind::StaticHolder => &["[<AutoOpen>]", "[<AbstractClass; Sealed>]"],
            Kind::CSharpHolder => &[
                "[<System.Runtime.CompilerServices.Extension>]",
                "[<Sealed>]",
            ],
            Kind::Interface | Kind::Delegate | Kind::Measure => &[],
        };
        // Any attribute at any target, now and then: the placement grid's
        // product, combined with everything else here.
        if self.rng.chance(15) {
            let attr = crate::source_existence_placement::random_attribute(&mut self.rng);
            return format!("{indent}{attr}\n");
        }
        if choices.is_empty() || self.rng.chance(50) {
            return String::new();
        }
        let attr = *self.rng.pick(choices);
        // An explicit `type:` target, which FCS reads as no target.
        if self.rng.chance(20) {
            format!("{indent}[<type: {}\n", &attr[2..])
        } else {
            format!("{indent}{attr}\n")
        }
    }

    fn module_attributes(&mut self, indent: &str) -> String {
        if self.rng.chance(15) {
            let attr = crate::source_existence_placement::random_attribute(&mut self.rng);
            return format!("{indent}{attr}\n");
        }
        match self.rng.below(8) {
            0 => format!("{indent}[<AutoOpen>]\n"),
            1 => format!("{indent}[<Microsoft.FSharp.Core.AutoOpenAttribute>]\n"),
            2 => format!(
                "{indent}[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]\n"
            ),
            3 => format!("{indent}[<RequireQualifiedAccess>]\n"),
            4 => format!("{indent}[<AutoOpen; RequireQualifiedAccess>]\n"),
            _ => String::new(),
        }
    }

    /// One type definition.
    fn type_defn(&mut self, indent: &str, in_module: bool) -> String {
        let name = self.entity_name();
        let access = self.access();
        let kind = *self.rng.pick(&[
            Kind::Record,
            Kind::Record,
            Kind::Union,
            Kind::Class,
            Kind::Interface,
            Kind::Enum,
            Kind::Delegate,
            Kind::Abbreviation,
            Kind::Abbreviation,
            Kind::StaticHolder,
            Kind::CSharpHolder,
            Kind::Measure,
        ]);
        let kind = if kind == Kind::CSharpHolder && !in_module {
            Kind::StaticHolder
        } else {
            kind
        };
        let attrs = self.type_attributes(indent, kind);
        let may_be_generic = matches!(
            kind,
            Kind::Record | Kind::Union | Kind::Class | Kind::Interface
        );
        let generic = may_be_generic && self.rng.chance(25);
        let typars = if generic { "<'a>" } else { "" };
        let body = match kind {
            Kind::Record => " = { X: int }".to_owned(),
            Kind::Union => format!(" =\n{indent}    | Case1\n{indent}    | Case2 of int"),
            Kind::Class => format!("() =\n{indent}    member _.P = 1"),
            Kind::Interface => format!(" =\n{indent}    abstract M: int -> int"),
            Kind::Enum => format!(" =\n{indent}    | One = 1\n{indent}    | Two = 2"),
            Kind::Delegate => " = delegate of int -> int".to_owned(),
            Kind::Abbreviation => {
                let earlier: Vec<String> = self
                    .declared
                    .iter()
                    .filter(|(_, g, k)| !g && *k != Kind::Measure)
                    .map(|(n, _, _)| n.clone())
                    .collect();
                match self.rng.below(3) {
                    0 if !earlier.is_empty() => format!(" = {}", self.rng.pick(&earlier)),
                    1 => " = string list".to_owned(),
                    _ => " = int".to_owned(),
                }
            }
            Kind::StaticHolder => format!(" =\n{indent}    static member S = 1"),
            Kind::CSharpHolder => {
                // Every member shape a type declares, `[<Extension>]` on it
                // or on one of its parts.
                let ext = "[<System.Runtime.CompilerServices.Extension>]";
                let type_name = name.clone();
                let name = *self.rng.pick(MEMBER_NAMES);
                let n = self.rng.below(1000);
                // The primary constructor's arguments and self identifier,
                // which take their names before any `let`.
                let arg = *self.rng.pick(LET_NAMES);
                let (ctor, call) = match self.rng.below(3) {
                    0 => ("()".to_owned(), "()"),
                    1 => (format!("({arg}: int)"), "(1)"),
                    _ => (format!("({arg}: int, q: int)"), "(1, 2)"),
                };
                let self_id = if self.rng.below(4) == 0 {
                    format!(" as {}", self.rng.pick(LET_NAMES))
                } else {
                    String::new()
                };
                let mut body = format!(
                    "{ctor}{self_id} =\n{indent}    static let helper{n} (s: string) = s\n"
                );
                // The `let`s, before every member: functions (methods),
                // values, lambdas, a `mutable` (a field), patterns, under
                // names that collide.
                for _ in 0..self.rng.below(4) {
                    let let_name = *self.rng.pick(LET_NAMES);
                    let other = *self.rng.pick(LET_NAMES);
                    let binding = match self.rng.below(7) {
                        0 => format!("{ext}\n{indent}    static let {let_name} (s: string) = s"),
                        1 => format!("{ext}\n{indent}    static let {let_name} = 1"),
                        2 => format!(
                            "{ext}\n{indent}    static let {let_name} = fun (s: string) -> s"
                        ),
                        3 => format!(
                            "{ext}\n{indent}    static let mutable {let_name} = fun (s: string) -> s"
                        ),
                        4 => format!("static let {let_name} (s: string) = s"),
                        5 => format!("static let {let_name}, {other} = 1, 2"),
                        _ => format!("{ext}\n{indent}    let {let_name} (s: string) = s"),
                    };
                    body.push_str(&format!("{indent}    {binding}\n"));
                }
                for _ in 0..1 + self.rng.below(3) {
                    let member = match self.rng.below(10) {
                        0 => format!("{ext}\n{indent}    static member {name}(s: string) = s"),
                        1 => format!("{ext}\n{indent}    static member {name} = 1"),
                        2 => format!(
                            "static member {name} with {ext} get () = 1 and set (v: int) = ()"
                        ),
                        3 => format!("{ext}\n{indent}    new(s: string) = {type_name}{call}"),
                        4 => format!(
                            "[<DefaultValue>]\n{indent}    static val mutable private {}: int",
                            self.rng.pick(LET_NAMES)
                        ),
                        9 => format!(
                            "[<CompiledName(\"{}\")>]\n{indent}    static member R{n}(s: string) = s",
                            self.rng.pick(LET_NAMES)
                        ),
                        5 => format!(
                            "{ext}\n{indent}    [<CompiledName(\"Renamed{n}\")>]\n{indent}    static member {name}X(s: string) = s"
                        ),
                        6 => format!(
                            "[<CLIEvent>]\n{indent}    member _.Ev{n} = Event<int>().Publish"
                        ),
                        7 => format!("{ext}\n{indent}    member _.{name}Y(s: string) = s"),
                        _ => format!(
                            "{ext}\n{indent}    static member {name}Z (s: string) (t: string) = s + t"
                        ),
                    };
                    body.push_str(&format!("{indent}    {member}\n"));
                }
                body.push_str(&format!("{indent}    member _.Use{n} = helper{n} \"x\""));
                body
            }
            Kind::Measure => {
                return format!("{indent}[<Measure>]\n{indent}type {access}{name}\n");
            }
        };
        self.declared.push((name.clone(), generic, kind));
        format!("{attrs}{indent}type {access}{name}{typars}{body}\n")
    }

    fn augmentation(&mut self, indent: &str) -> String {
        let local: Vec<String> = self
            .declared
            .iter()
            // A class-like type: augmenting it in its own list is intrinsic.
            .filter(|(_, g, k)| {
                !g && matches!(
                    k,
                    Kind::Record | Kind::Union | Kind::Class | Kind::StaticHolder
                )
            })
            .map(|(n, _, _)| n.clone())
            .collect();
        let target = if !local.is_empty() && self.rng.chance(40) {
            self.rng.pick(&local).clone()
        } else {
            (*self.rng.pick(EXTENDED)).to_owned()
        };
        let mut out = format!("{indent}type {target} with\n");
        let members = 1 + self.rng.below(3);
        for _ in 0..members {
            let name = *self.rng.pick(MEMBER_NAMES);
            let line = match self.rng.below(8) {
                7 => format!(
                    "[<CLIEvent>]\n{indent}    member x.Ev{} = Event<int>().Publish",
                    self.rng.below(1000)
                ),
                0 => format!("member x.{name}() = 1"),
                1 => format!("member x.{name} = 1"),
                2 => format!("static member {name}() = 1"),
                3 => format!("member x.{name} with get () = 1 and set (v: int) = ()"),
                4 => "static member (+++) (a: int, b: int) = a".to_owned(),
                5 => format!("static member {name} = 2"),
                _ => format!("member x.{name}(y: int) = y"),
            };
            // A member attribute with a target: `method:` is the member's,
            // `return:` its return value's.
            match self.rng.below(10) {
                0 => out.push_str(&format!("{indent}    [<return: CompiledName(\"Q\")>]\n")),
                1 => out.push_str(&format!(
                    "{indent}    [<method: CompiledName(\"P{}\")>]\n",
                    self.rng.below(100)
                )),
                _ => {}
            }
            out.push_str(&format!("{indent}    {line}\n"));
        }
        out
    }

    /// The declarations of one list, `depth` levels down.
    fn decls(&mut self, indent: &str, depth: usize, in_module: bool) -> String {
        let mut out = String::new();
        let n = 1 + self.rng.below(4);
        for _ in 0..n {
            match self.rng.below(10) {
                0 | 1 if depth < 3 => {
                    let name = self.entity_name();
                    let attrs = self.module_attributes(indent);
                    let access = self.access();
                    let rec = if self.rng.chance(15) { "rec " } else { "" };
                    let inner = format!("{indent}    ");
                    let body = self.decls(&inner, depth + 1, true);
                    out.push_str(&format!(
                        "{attrs}{indent}module {access}{rec}{name} =\n{body}"
                    ));
                }
                2..=4 => out.push_str(&self.type_defn(indent, in_module)),
                5 => {
                    let name = self.upper_name();
                    let access = self.access();
                    out.push_str(&format!("{indent}exception {access}{name} of string\n"));
                }
                6 if in_module => out.push_str(&self.augmentation(indent)),
                7 if in_module => {
                    let attr = if self.rng.chance(60) {
                        format!("{indent}[<System.Runtime.CompilerServices.Extension>]\n")
                    } else {
                        String::new()
                    };
                    let rec = if self.rng.chance(20) { "rec " } else { "" };
                    let name = self.rng.below(1000);
                    out.push_str(&format!("{attr}{indent}let {rec}f{name} (s: string) = s\n"));
                }
                8 if in_module => {
                    out.push_str(&format!("{indent}let v{} = 1\n", self.rng.below(1000)))
                }
                _ => out.push_str(&self.type_defn(indent, in_module)),
            }
        }
        out
    }

    fn namespace_path(&mut self) -> String {
        let n = 1 + self.rng.below(3);
        (0..n)
            .map(|_| *self.rng.pick(NAMESPACE_NAMES))
            .collect::<Vec<_>>()
            .join(".")
    }

    /// One file.
    fn file(&mut self, last: bool) -> (String, bool) {
        self.declared.clear();
        let mut out = String::new();
        let mut headerless = false;
        match self.rng.below(if last { 5 } else { 4 }) {
            0 | 1 => {
                let fragments = 1 + self.rng.below(2);
                for _ in 0..fragments {
                    let rec = if self.rng.chance(10) { "rec " } else { "" };
                    out.push_str(&format!("namespace {rec}{}\n", self.namespace_path()));
                    out.push_str(&self.decls("", 0, false));
                }
            }
            2 => {
                out.push_str(&self.module_attributes(""));
                out.push_str(&format!(
                    "module {}.{}\n",
                    self.namespace_path(),
                    self.entity_name()
                ));
                out.push_str(&self.decls("", 0, true));
            }
            3 => {
                out.push_str("namespace global\n");
                out.push_str(&self.decls("", 0, false));
            }
            _ => {
                // Headerless: the last file of an executable.
                headerless = true;
                out.push_str(&self.decls("", 0, true));
            }
        }
        if self.rng.chance(15) {
            out.push_str(&format!(
                "[<assembly: AutoOpen(\"{}\")>]\ndo ()\n",
                self.namespace_path()
            ));
        }
        (out, headerless)
    }
}

/// The generated cell of `seed`.
pub fn cell(seed: u64) -> Cell {
    let mut g = Gen {
        rng: Rng::new(seed),
        declared: Vec::new(),
    };
    let n = 1 + g.rng.below(3);
    let mut files = Vec::new();
    let mut headerless = false;
    for i in 0..n {
        let (text, h) = g.file(i + 1 == n);
        headerless |= h;
        files.push((format!("F{i}.fs"), text));
    }
    let mut cell = Cell::new(format!("gen_{seed}"), &[]);
    // One case in `hostile::RATE` has a hostile source state mixed into one
    // of its files, by dimension in turn so a short run reaches each.
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
            let mutated = String::from_utf8(entry.value.apply(text))
                .expect("a mutation of a text dimension keeps the file UTF-8");
            files[at].1 = mutated;
            cell.hostile.insert(entry.dimension);
        }
    }
    cell.files = files;
    if headerless {
        cell.target = Target::Exe;
    }
    cell
}

/// The census of the source mutations the generator mixes in.
fn open_census() -> Census {
    coverage::open(
        file!(),
        "source_existence_gen",
        &[(
            Dimension::NotText,
            "a cell's files are text: a Compile item that is not UTF-8 is one the \
             caller cannot read, the `UnreadableItem` channel, which the walk's \
             inventory witnesses",
        )],
    )
}

/// Record each graded cell's mutation, with the certified verdict's first
/// word as the outcome, once both readings have run.
fn record(census: &Census, cells: &[Cell], entries: &[(String, String)]) {
    for cell in cells {
        let outcome = entries
            .iter()
            .find(|(name, _)| *name == cell.name)
            .and_then(|(_, verdict)| verdict.strip_prefix("certified: "))
            .and_then(|v| v.split([' ', ',']).next())
            .unwrap_or("failed");
        census.reached(&cell.hostile, outcome);
    }
}

/// The cells the generator makes from seeds `first..first + count`.
fn generated(first: u64, count: u64) -> Vec<Cell> {
    (first..first + count).map(cell).collect()
}

/// The pinned default run of the generator: its seeds are fixed, so each
/// case's verdict is pinned in `source_existence_gen.txt`.
#[test]
fn source_rows_are_fcs_rows_over_generated_projects() {
    let census = open_census();
    let cells = generated(0, 60);
    let (entries, failures) = grade_cells(&cells);
    record(&census, &cells, &entries);
    if !failures.is_empty() {
        for c in &cells {
            if failures.iter().any(|f| f.contains(&format!("{}:", c.name))) {
                for (name, text) in &c.files {
                    eprintln!("--- {} {name}\n{text}", c.name);
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "source_existence_gen",
        &manifest,
        &regenerate("source_existence_gen::source_rows_are_fcs_rows_over_generated_projects"),
    );
    census.finish(&regenerate(
        "source_existence_gen::source_rows_are_fcs_rows_over_generated_projects",
    ));
}

/// The generator over more seeds: `BORZOI_SOURCE_EXISTENCE_SEED` (default
/// 1000) and `BORZOI_SOURCE_EXISTENCE_CASES` (default 400). Pins nothing:
/// every property must hold.
#[test]
#[ignore = "hundreds of FCS checks; the default run is the gate"]
fn deep_source_rows_are_fcs_rows_over_generated_projects() {
    let var = |name: &str, default: u64| {
        std::env::var(name)
            .ok()
            .map(|v| v.parse().expect("a count"))
            .unwrap_or(default)
    };
    let first = var("BORZOI_SOURCE_EXISTENCE_SEED", 1000);
    let count = var("BORZOI_SOURCE_EXISTENCE_CASES", 400);
    eprintln!("seeds {first}..{}", first + count);
    let census = open_census();
    let cells = generated(first, count);
    let (entries, failures) = grade_cells(&cells);
    record(&census, &cells, &entries);
    let exact = entries
        .iter()
        .filter(|(_, v)| v.starts_with("certified: exact"))
        .count();
    eprintln!(
        "{} cases, {exact} exact under the certificate",
        entries.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    census.finish(&regenerate(
        "source_existence_gen::deep_source_rows_are_fcs_rows_over_generated_projects",
    ));
}

/// Print the generated cell `BORZOI_SOURCE_EXISTENCE_SEED`, our reading of
/// it, and FCS's diagnostics: the tool for reading a generated failure.
#[test]
#[ignore = "a debugging aid, run by hand"]
fn show_generated_cell() {
    let seed: u64 = std::env::var("BORZOI_SOURCE_EXISTENCE_SEED")
        .expect("BORZOI_SOURCE_EXISTENCE_SEED")
        .parse()
        .expect("a seed");
    let cell = cell(seed);
    for (name, text) in &cell.files {
        eprintln!("--- {name}\n{text}");
    }
    let (ours, _) = crate::source_existence_diff::ours(&cell, None);
    match &ours {
        borzoi_sema::SourceExistence::Unread(why) => eprintln!("ours: unread {why:?}"),
        borzoi_sema::SourceExistence::Read(s) => eprintln!("ours: read, {:?}", s.approximations),
    }
    let fcs = crate::source_existence_diff::fcs(&cell);
    eprintln!("FCS errors: {:?}", fcs.errors);
}
