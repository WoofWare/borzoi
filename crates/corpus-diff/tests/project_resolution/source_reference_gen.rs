//! Generated two-project fixtures: a library A that exports a random tree of
//! the declaration kinds an F# assembly can export, and a consumer B that
//! uses each of them qualified, bare, and through `open`s.
//!
//! Built so A always compiles, which is what the fresh-DLL side of the
//! differential needs: names are unique per scope (with collisions *across*
//! scopes and with FSharp.Core and the BCL on purpose), a `.fsi` is printed
//! from the same tree as its implementation, and no visible signature
//! mentions a hidden item. B need not compile: FCS's diagnostics are part of
//! the compared answer.
//!
//! The randomness is a seeded SplitMix64, so a case is reproduced from its
//! seed alone.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// SplitMix64: small, seedable, and good enough to spread choices.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..n`.
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(n).expect("n fits u64")).expect("fits usize")
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    Public,
    Internal,
    Private,
}

impl Access {
    fn keyword(self) -> &'static str {
        match self {
            Access::Public => "",
            Access::Internal => "internal ",
            Access::Private => "private ",
        }
    }
}

/// The declaration kinds A exports. Each is printed in both its implementation
/// and its signature form, and used from B.
#[derive(Clone, Debug)]
pub enum Item {
    Module {
        name: String,
        access: Access,
        auto_open: bool,
        rqa: bool,
        items: Vec<Decl>,
    },
    Value {
        name: String,
        access: Access,
    },
    Literal {
        name: String,
    },
    Function {
        name: String,
        access: Access,
        compiled_name: Option<String>,
    },
    ActivePattern {
        case: String,
    },
    Record {
        name: String,
        access: Access,
        field: String,
    },
    Union {
        name: String,
        access: Access,
        cases: Vec<String>,
    },
    Class {
        name: String,
        access: Access,
    },
    Interface {
        name: String,
        access: Access,
    },
    Abbrev {
        name: String,
        access: Access,
        target: &'static str,
    },
    Exception {
        name: String,
        access: Access,
    },
    Measure {
        name: String,
    },
    /// An optional extension (`type System.String with …`); module-only.
    OptExtension {
        target: &'static str,
        member: String,
    },
    /// A C#-style extension method on `string`.
    CsExtension {
        holder: String,
        access: Access,
        member: String,
    },
}

/// An item with whether a `.fsi` hides it. Hiding is decided at generation, so
/// printing is a pure function of the tree.
#[derive(Clone, Debug)]
pub struct Decl {
    pub item: Item,
    pub hidden: bool,
}

#[derive(Clone, Debug)]
pub enum Block {
    /// `namespace <path>` followed by type-level declarations.
    Namespace { path: String, decls: Vec<Decl> },
    /// A whole-file `module <path>`.
    TopModule {
        path: String,
        auto_open: bool,
        decls: Vec<Decl>,
    },
}

#[derive(Clone, Debug)]
pub struct AFile {
    pub stem: String,
    pub blocks: Vec<Block>,
    pub fsi: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ivt {
    None,
    /// `InternalsVisibleTo` naming B.
    Consumer,
    /// `InternalsVisibleTo` naming some other assembly.
    Other,
}

#[derive(Clone, Debug)]
pub struct Case {
    pub library: String,
    pub consumer: String,
    pub files: Vec<AFile>,
    pub ivt: Ivt,
    pub assembly_auto_open: Option<String>,
    /// Paths B opens, in order.
    pub opens: Vec<String>,
    /// Lines of B's body.
    pub uses: Vec<String>,
}

const NAMESPACES: &[&str] = &[
    "N",
    "N.Sub",
    "Other",
    "System",
    "Microsoft.FSharp.Collections",
];
const MODULES: &[&str] = &["M", "List", "Option", "Helpers", "String"];
const TYPES: &[&str] = &["T", "Result", "Option", "String", "Point", "Shape"];
const VALUES: &[&str] = &["x", "id", "map", "length", "value", "max"];
const LITERALS: &[&str] = &["Lit", "Max", "Zero"];
const CASES: &[&str] = &["Some", "None", "Ok", "Error", "A", "B", "Red"];
const FIELDS: &[&str] = &["X", "Value", "Length", "Name"];
const EXT_MEMBERS: &[&str] = &["Ext", "Length2", "Trim", "Chars2"];
const MEASURES: &[&str] = &["m", "kg", "s"];
const EXCEPTIONS: &[&str] = &["Failure", "E", "Oops"];
const PATTERNS: &[&str] = &["Even", "Some", "Positive"];
const HOLDERS: &[&str] = &["Ext", "Extensions", "StringExt"];
const ABBREV_TARGETS: &[&str] = &["int", "string list", "System.String", "int * string"];
const EXT_TARGETS: &[&str] = &["System.String", "System.Int32"];

/// The two name spaces of one scope: entities (types, exceptions, modules,
/// measures, extension holders) and values. Each must be unique for A to
/// compile.
#[derive(Default)]
struct Scope {
    entities: BTreeSet<String>,
    values: BTreeSet<String>,
}

struct Gen<'a> {
    rng: &'a mut Rng,
    /// Entity scopes by namespace path: shared across every block and file
    /// that declares into the namespace.
    namespaces: BTreeMap<String, Scope>,
}

impl Gen<'_> {
    /// A name from `pool` not yet in `taken`, or that name with a digit.
    fn fresh(rng: &mut Rng, pool: &[&str], taken: &mut BTreeSet<String>, ns: &str) -> String {
        let base = loop {
            let candidate = *rng.pick(pool);
            // A user type or module named `String` in namespace `System`
            // would make A's own `type System.String with` an intrinsic
            // augmentation of it.
            if !(ns == "System" && candidate == "String") {
                break candidate;
            }
        };
        let mut name = base.to_owned();
        let mut n = 1;
        while taken.contains(&name) {
            name = format!("{base}{n}");
            n += 1;
        }
        taken.insert(name.clone());
        name
    }

    fn access(&mut self, allow_private: bool) -> Access {
        match self.rng.below(if allow_private { 5 } else { 4 }) {
            0 => Access::Internal,
            4 => Access::Private,
            _ => Access::Public,
        }
    }

    fn hide(&mut self, fsi: bool, access: Access) -> bool {
        // A private item is omitted from a signature rather than printed as
        // `val private`, which is what a hand-written `.fsi` does.
        fsi && (access == Access::Private || self.rng.chance(20))
    }

    /// One namespace-level declaration.
    fn ns_decl(&mut self, ns: &str, fsi: bool, depth: usize) -> Decl {
        let scope = self.namespaces.entry(ns.to_owned()).or_default();
        let mut taken = std::mem::take(&mut scope.entities);
        let decl = self.entity_decl(ns, &mut taken, fsi, depth, false);
        self.namespaces.get_mut(ns).expect("inserted").entities = taken;
        decl
    }

    /// An entity-level declaration into `taken`. In a module, `in_module`
    /// also admits the module-only forms.
    fn entity_decl(
        &mut self,
        ns: &str,
        taken: &mut BTreeSet<String>,
        fsi: bool,
        depth: usize,
        in_module: bool,
    ) -> Decl {
        let access = self.access(in_module);
        // Index 8 is a nested module, below the nesting bound only.
        let pick = match self.rng.below(9) {
            8 if depth >= 2 => 0,
            k => k,
        };
        let item = match pick {
            0 => Item::Record {
                name: Self::fresh(self.rng, TYPES, taken, ns),
                access,
                field: self.rng.pick(FIELDS).to_string(),
            },
            1 => {
                let n = 1 + self.rng.below(3);
                let mut cases = BTreeSet::new();
                while cases.len() < n {
                    cases.insert(self.rng.pick(CASES).to_string());
                }
                Item::Union {
                    name: Self::fresh(self.rng, TYPES, taken, ns),
                    access,
                    cases: cases.into_iter().collect(),
                }
            }
            2 => Item::Class {
                name: Self::fresh(self.rng, TYPES, taken, ns),
                access,
            },
            3 => Item::Interface {
                name: Self::fresh(self.rng, TYPES, taken, ns),
                access,
            },
            4 => Item::Abbrev {
                name: Self::fresh(self.rng, TYPES, taken, ns),
                access,
                target: self.rng.pick(ABBREV_TARGETS),
            },
            5 => Item::Exception {
                name: Self::fresh(self.rng, EXCEPTIONS, taken, ns),
                access,
            },
            6 => Item::Measure {
                name: Self::fresh(self.rng, MEASURES, taken, ns),
            },
            7 => Item::CsExtension {
                holder: Self::fresh(self.rng, HOLDERS, taken, ns),
                access,
                member: self.rng.pick(EXT_MEMBERS).to_string(),
            },
            _ => {
                let name = Self::fresh(self.rng, MODULES, taken, ns);
                let auto_open = self.rng.chance(35);
                let rqa = !auto_open && self.rng.chance(25);
                // A whole module hidden by a `.fsi` hides its contents too,
                // so the contents' own hiding is decided as if no `.fsi`
                // were there.
                let hidden = self.hide(fsi, access);
                let items = self.module_body(ns, fsi && !hidden, depth + 1);
                return Decl {
                    item: Item::Module {
                        name,
                        access,
                        auto_open,
                        rqa,
                        items,
                    },
                    hidden,
                };
            }
        };
        let access = item_access(&item);
        Decl {
            hidden: self.hide(fsi, access),
            item,
        }
    }

    /// One to four declarations for a module body.
    fn module_body(&mut self, ns: &str, fsi: bool, depth: usize) -> Vec<Decl> {
        let mut scope = Scope::default();
        let n = 1 + self.rng.below(4);
        (0..n)
            .map(|_| {
                if self.rng.chance(45) {
                    self.value_decl(ns, &mut scope.values, fsi)
                } else {
                    self.entity_decl(ns, &mut scope.entities, fsi, depth, true)
                }
            })
            .collect()
    }

    fn value_decl(&mut self, ns: &str, taken: &mut BTreeSet<String>, fsi: bool) -> Decl {
        let access = self.access(true);
        let item = match self.rng.below(5) {
            0 => Item::Value {
                name: Self::fresh(self.rng, VALUES, taken, ns),
                access,
            },
            1 => Item::Literal {
                name: Self::fresh(self.rng, LITERALS, taken, ns),
            },
            2 => {
                let name = Self::fresh(self.rng, VALUES, taken, ns);
                let compiled_name = self.rng.chance(30).then(|| format!("Compiled{name}"));
                Item::Function {
                    name,
                    access,
                    compiled_name,
                }
            }
            3 => Item::ActivePattern {
                case: Self::fresh(self.rng, PATTERNS, taken, ns),
            },
            _ => Item::OptExtension {
                target: self.rng.pick(EXT_TARGETS),
                member: Self::fresh(self.rng, EXT_MEMBERS, taken, ns),
            },
        };
        let access = item_access(&item);
        Decl {
            hidden: self.hide(fsi, access),
            item,
        }
    }
}

fn item_access(item: &Item) -> Access {
    match item {
        Item::Module { access, .. }
        | Item::Value { access, .. }
        | Item::Function { access, .. }
        | Item::Record { access, .. }
        | Item::Union { access, .. }
        | Item::Class { access, .. }
        | Item::Interface { access, .. }
        | Item::Abbrev { access, .. }
        | Item::Exception { access, .. }
        | Item::CsExtension { access, .. } => *access,
        Item::Literal { .. }
        | Item::ActivePattern { .. }
        | Item::Measure { .. }
        | Item::OptExtension { .. } => Access::Public,
    }
}

/// Generate case `index` of a run seeded with `seed`.
pub fn generate(seed: u64, index: usize) -> Case {
    let mut rng = Rng::new(seed ^ (u64::try_from(index).expect("fits") << 32));
    let mut g = Gen {
        rng: &mut rng,
        namespaces: BTreeMap::new(),
    };
    let n_files = 1 + g.rng.below(3);
    let mut files = Vec::new();
    for f in 0..n_files {
        let fsi = g.rng.chance(50);
        let blocks = if g.rng.chance(25) {
            // `module <ns>.<name>`: the module's name is an entity of `ns`.
            let ns = g.rng.pick(NAMESPACES).to_string();
            let scope = g.namespaces.entry(ns.clone()).or_default();
            let mut taken = std::mem::take(&mut scope.entities);
            let name = Gen::fresh(g.rng, MODULES, &mut taken, &ns);
            g.namespaces.get_mut(&ns).expect("inserted").entities = taken;
            let auto_open = g.rng.chance(30);
            let decls = g.module_body(&ns, fsi, 1);
            vec![Block::TopModule {
                path: format!("{ns}.{name}"),
                auto_open,
                decls,
            }]
        } else {
            (0..1 + g.rng.below(2))
                .map(|_| {
                    let ns = g.rng.pick(NAMESPACES).to_string();
                    let decls = (0..1 + g.rng.below(4))
                        .map(|_| g.ns_decl(&ns, fsi, 0))
                        .collect();
                    Block::Namespace { path: ns, decls }
                })
                .collect()
        };
        // The last file is never named after the assembly, so an unpinned
        // `-o:` would name the assembly differently.
        files.push(AFile {
            stem: format!("File{f}"),
            blocks,
            fsi,
        });
    }
    let ivt = match g.rng.below(3) {
        0 => Ivt::None,
        1 => Ivt::Consumer,
        _ => Ivt::Other,
    };
    let mut case = Case {
        library: format!("Ay{index}"),
        consumer: "Bee".to_owned(),
        files,
        ivt,
        assembly_auto_open: None,
        opens: Vec::new(),
        uses: Vec::new(),
    };
    let targets = open_targets(&case);
    if rng.chance(30) && !targets.is_empty() {
        case.assembly_auto_open = Some(rng.pick(&targets).clone());
    }
    let mut opens: Vec<String> = targets.iter().filter(|_| rng.chance(60)).cloned().collect();
    // Order decides which open shadows which.
    for i in (1..opens.len()).rev() {
        opens.swap(i, rng.below(i + 1));
    }
    case.opens = opens;
    case.uses = consumer_uses(&case, &mut rng);
    case
}

/// Every namespace and module path B could open (an `RequireQualifiedAccess`
/// module excepted), in declaration order, without repeats.
fn open_targets(case: &Case) -> Vec<String> {
    fn walk(prefix: &str, decls: &[Decl], out: &mut Vec<String>) {
        for d in decls {
            if let Item::Module {
                name, rqa, items, ..
            } = &d.item
            {
                let path = format!("{prefix}.{name}");
                if !rqa {
                    out.push(path.clone());
                }
                walk(&path, items, out);
            }
        }
    }
    let mut out = Vec::new();
    for f in &case.files {
        for b in &f.blocks {
            match b {
                Block::Namespace { path, decls } => {
                    out.push(path.clone());
                    walk(path, decls, &mut out);
                }
                Block::TopModule { path, decls, .. } => {
                    out.push(path.clone());
                    walk(path, decls, &mut out);
                }
            }
        }
    }
    let mut seen = BTreeSet::new();
    out.retain(|p| seen.insert(p.clone()));
    out
}

/// B's body: for every item of A, its uses, qualified and bare.
fn consumer_uses(case: &Case, rng: &mut Rng) -> Vec<String> {
    let mut out = Vec::new();
    let mut k = 0usize;
    let mut next = || {
        k += 1;
        format!("u{k}")
    };
    fn walk(
        prefix: &str,
        decls: &[Decl],
        rng: &mut Rng,
        out: &mut Vec<String>,
        next: &mut dyn FnMut() -> String,
    ) {
        for d in decls {
            uses_of(prefix, &d.item, rng, out, next);
            if let Item::Module { name, items, .. } = &d.item {
                walk(&format!("{prefix}.{name}"), items, rng, out, next);
            }
        }
    }
    for f in &case.files {
        for b in &f.blocks {
            match b {
                Block::Namespace { path, decls } | Block::TopModule { path, decls, .. } => {
                    walk(path, decls, rng, &mut out, &mut next)
                }
            }
        }
    }
    out
}

fn uses_of(
    p: &str,
    item: &Item,
    rng: &mut Rng,
    out: &mut Vec<String>,
    next: &mut dyn FnMut() -> String,
) {
    let bare = rng.chance(60);
    let mut push = |text: String| out.push(text);
    match item {
        Item::Module { .. } => {}
        Item::Value { name, .. } => {
            push(format!("let {} = {p}.{name}", next()));
            if bare {
                push(format!("let {} = {name}", next()));
            }
        }
        Item::Literal { name } => {
            push(format!(
                "let {} = match 0 with {p}.{name} -> 1 | _ -> 2",
                next()
            ));
            push(format!("let {} = {p}.{name} + 1", next()));
        }
        Item::Function { name, .. } => {
            push(format!("let {} = {p}.{name} 1", next()));
            if bare {
                push(format!("let {} = {name} 1", next()));
            }
        }
        Item::ActivePattern { case } => {
            push(format!("let {} = match 2 with {p}.{case} n -> n", next()));
            if bare {
                push(format!("let {} = match 2 with {case} n -> n", next()));
            }
        }
        Item::Record { name, field, .. } => {
            push(format!(
                "let {} : {p}.{name} = {{ {p}.{name}.{field} = 1 }}",
                next()
            ));
            push(format!("let {} (r: {p}.{name}) = r.{field}", next()));
            if bare {
                push(format!("let {} = {{ {field} = 2 }}", next()));
            }
        }
        Item::Union { name, cases, .. } => {
            let case = &cases[0];
            push(format!("let {} = {p}.{name}.{case}", next()));
            push(format!(
                "let {} (u: {p}.{name}) = match u with {p}.{name}.{case} -> 0 | _ -> 1",
                next()
            ));
            if bare {
                push(format!("let {} = {case}", next()));
            }
        }
        Item::Class { name, .. } => {
            push(format!(
                "let {} = {p}.{name}().Inst + {p}.{name}.Stat",
                next()
            ));
            if bare {
                push(format!("let {} = {name}()", next()));
            }
        }
        Item::Interface { name, .. } => {
            push(format!("let {} (i: {p}.{name}) = i.Get ()", next()));
        }
        Item::Abbrev { name, .. } => {
            push(format!(
                "let {} : {p}.{name} = Unchecked.defaultof<_>",
                next()
            ));
            if bare {
                push(format!("let {} : {name} = Unchecked.defaultof<_>", next()));
            }
        }
        Item::Exception { name, .. } => {
            push(format!("let {} = {p}.{name} \"x\"", next()));
            push(format!(
                "let {} (e: exn) = match e with {p}.{name} s -> s | _ -> \"\"",
                next()
            ));
            if bare {
                push(format!("let {} = {name} \"y\"", next()));
            }
        }
        Item::Measure { name } => {
            push(format!("let {} = 1<{p}.{name}>", next()));
            if bare {
                push(format!("let {} = 2<{name}>", next()));
            }
        }
        Item::OptExtension { target, member } => {
            let receiver = if *target == "System.String" {
                "\"s\""
            } else {
                "(1)"
            };
            push(format!("let {} = {receiver}.{member}", next()));
            push(format!("let {} = {target}.{member}S", next()));
        }
        Item::CsExtension { holder, member, .. } => {
            push(format!("let {} = \"s\".{member} ()", next()));
            push(format!("let {} = {p}.{holder}.{member} \"t\"", next()));
        }
    }
}

/// The implementation form of `decls`, at `indent`.
fn print_impl(decls: &[Decl], indent: usize, out: &mut String) {
    let pad = " ".repeat(indent);
    for d in decls {
        print_impl_item(&d.item, &pad, indent, out);
    }
}

fn print_impl_item(item: &Item, pad: &str, indent: usize, out: &mut String) {
    let w = |out: &mut String, line: &str| {
        writeln!(out, "{pad}{line}").expect("write to a String");
    };
    match item {
        Item::Module {
            name,
            access,
            auto_open,
            rqa,
            items,
        } => {
            module_attrs(pad, *auto_open, *rqa, out);
            w(out, &format!("module {}{name} =", access.keyword()));
            print_impl(items, indent + 4, out);
        }
        Item::Value { name, access } => {
            w(out, &format!("let {}{name} : int = 1", access.keyword()))
        }
        Item::Literal { name } => {
            w(out, "[<Literal>]");
            w(out, &format!("let {name} = 1"));
        }
        Item::Function {
            name,
            access,
            compiled_name,
        } => {
            if let Some(c) = compiled_name {
                w(out, &format!("[<CompiledName(\"{c}\")>]"));
            }
            w(
                out,
                &format!("let {}{name} (a: int) : int = a", access.keyword()),
            );
        }
        // Total, so its body names no `Some`, which a generated union case
        // in scope could shadow.
        Item::ActivePattern { case } => w(out, &format!("let (|{case}|) (x: int) : int = x % 2")),
        Item::Record {
            name,
            access,
            field,
        } => w(
            out,
            &format!("type {}{name} = {{ {field}: int }}", access.keyword()),
        ),
        Item::Union {
            name,
            access,
            cases,
        } => w(
            out,
            &format!("type {}{name} = {}", access.keyword(), union_cases(cases)),
        ),
        Item::Class { name, access } => {
            w(out, &format!("type {}{name}() =", access.keyword()));
            w(out, "    member _.Inst = 1");
            w(out, "    static member Stat = 2");
        }
        Item::Interface { name, access } => {
            w(out, &format!("type {}{name} =", access.keyword()));
            w(out, "    abstract Get: unit -> int");
        }
        Item::Abbrev {
            name,
            access,
            target,
        } => w(out, &format!("type {}{name} = {target}", access.keyword())),
        Item::Exception { name, access } => w(
            out,
            &format!("exception {}{name} of string", access.keyword()),
        ),
        Item::Measure { name } => w(out, &format!("[<Measure>] type {name}")),
        Item::OptExtension { target, member } => {
            w(out, &format!("type {target} with"));
            w(out, &format!("    member _.{member} = 1"));
            w(out, &format!("    static member {member}S = 2"));
        }
        Item::CsExtension {
            holder,
            access,
            member,
        } => {
            w(
                out,
                "[<System.Runtime.CompilerServices.Extension; Sealed; AbstractClass>]",
            );
            w(out, &format!("type {}{holder} =", access.keyword()));
            w(out, "    [<System.Runtime.CompilerServices.Extension>]");
            w(
                out,
                &format!("    static member {member}(s: string) = s.Length"),
            );
        }
    }
}

/// The signature form of the visible part of `decls`, at `indent`. `None`
/// when nothing is visible.
fn print_sig(decls: &[Decl], indent: usize, out: &mut String) {
    let pad = " ".repeat(indent);
    let w = |out: &mut String, line: &str| {
        writeln!(out, "{pad}{line}").expect("write to a String");
    };
    for d in decls.iter().filter(|d| !d.hidden) {
        match &d.item {
            Item::Module {
                name,
                access,
                auto_open,
                rqa,
                items,
            } => {
                module_attrs(&pad, *auto_open, *rqa, out);
                if items.iter().all(|d| d.hidden) {
                    w(
                        out,
                        &format!("module {}{name} = begin end", access.keyword()),
                    );
                } else {
                    w(out, &format!("module {}{name} =", access.keyword()));
                    print_sig(items, indent + 4, out);
                }
            }
            Item::Value { name, access } => w(out, &format!("val {}{name}: int", access.keyword())),
            Item::Literal { name } => {
                w(out, "[<Literal>]");
                w(out, &format!("val {name}: int = 1"));
            }
            Item::Function {
                name,
                access,
                compiled_name,
            } => {
                if let Some(c) = compiled_name {
                    w(out, &format!("[<CompiledName(\"{c}\")>]"));
                }
                w(
                    out,
                    &format!("val {}{name}: a: int -> int", access.keyword()),
                );
            }
            Item::ActivePattern { case } => w(out, &format!("val (|{case}|): x: int -> int")),
            Item::Class { name, access } => {
                w(out, &format!("type {}{name} =", access.keyword()));
                w(out, &format!("    new: unit -> {name}"));
                w(out, "    member Inst: int");
                w(out, "    static member Stat: int");
            }
            Item::OptExtension { target, member } => {
                w(out, &format!("type {target} with"));
                w(out, &format!("    member {member}: int"));
                w(out, &format!("    static member {member}S: int"));
            }
            Item::CsExtension {
                holder,
                access,
                member,
            } => {
                w(
                    out,
                    "[<System.Runtime.CompilerServices.Extension; Sealed; AbstractClass>]",
                );
                w(out, &format!("type {}{holder} =", access.keyword()));
                w(out, "    [<System.Runtime.CompilerServices.Extension>]");
                w(
                    out,
                    &format!("    static member {member}: s: string -> int"),
                );
            }
            // A type definition's signature is its definition.
            other @ (Item::Record { .. }
            | Item::Union { .. }
            | Item::Interface { .. }
            | Item::Abbrev { .. }
            | Item::Exception { .. }
            | Item::Measure { .. }) => print_impl_item(other, &pad, indent, out),
        }
    }
}

fn module_attrs(pad: &str, auto_open: bool, rqa: bool, out: &mut String) {
    if auto_open {
        writeln!(out, "{pad}[<AutoOpen>]").expect("write to a String");
    }
    if rqa {
        writeln!(out, "{pad}[<RequireQualifiedAccess>]").expect("write to a String");
    }
}

fn union_cases(cases: &[String]) -> String {
    cases
        .iter()
        .map(|c| format!("| {c}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// A's source files, in Compile order, as `(file name, text)`: each `.fsi`
/// before its implementation, and the assembly attributes in a file of their
/// own ahead of them.
pub fn library_files(case: &Case) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut attrs = String::new();
    match case.ivt {
        Ivt::None => {}
        Ivt::Consumer => writeln!(
            attrs,
            "[<assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"{}\")>]",
            case.consumer
        )
        .expect("write to a String"),
        Ivt::Other => writeln!(
            attrs,
            "[<assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"SomeoneElse\")>]"
        )
        .expect("write to a String"),
    }
    if let Some(target) = &case.assembly_auto_open {
        writeln!(attrs, "[<assembly: AutoOpen(\"{target}\")>]").expect("write to a String");
    }
    if !attrs.is_empty() {
        out.push((
            "AssemblyInfo.fs".to_owned(),
            format!("module AssemblyAttributes\n\n{attrs}do ()\n"),
        ));
    }
    out.push((
        "Anchor.fs".to_owned(),
        format!("module {}\n\nlet anchor = 1\n", anchor_module(case)),
    ));
    for f in &case.files {
        let mut implementation = String::new();
        let mut signature = String::new();
        for b in &f.blocks {
            match b {
                Block::Namespace { path, decls } => {
                    writeln!(implementation, "namespace {path}\n").expect("write to a String");
                    print_impl(decls, 0, &mut implementation);
                    writeln!(implementation).expect("write to a String");
                    writeln!(signature, "namespace {path}\n").expect("write to a String");
                    print_sig(decls, 0, &mut signature);
                    writeln!(signature).expect("write to a String");
                }
                Block::TopModule {
                    path,
                    auto_open,
                    decls,
                } => {
                    for text in [&mut implementation, &mut signature] {
                        module_attrs("", *auto_open, false, text);
                        writeln!(text, "module {path}\n").expect("write to a String");
                    }
                    print_impl(decls, 0, &mut implementation);
                    print_sig(decls, 0, &mut signature);
                }
            }
        }
        if f.fsi {
            out.push((format!("{}.fsi", f.stem), signature));
        }
        out.push((format!("{}.fs", f.stem), implementation));
    }
    out
}

/// The module every case's A declares one public value in, whatever else it
/// declares: B's use of it is the case's must-commit point.
pub fn anchor_module(case: &Case) -> String {
    format!("{}Anchor", case.library)
}

/// The first line of B's body: the use of the anchor.
pub const ANCHOR_USE: &str = "let anchorUse = ";

/// B's source files, in Compile order. The last is never named after B.
pub fn consumer_files(case: &Case) -> Vec<(String, String)> {
    let mut text = String::from("module Use\n\n");
    for o in &case.opens {
        writeln!(text, "open {o}").expect("write to a String");
    }
    writeln!(text).expect("write to a String");
    writeln!(text, "{ANCHOR_USE}{}.anchor", anchor_module(case)).expect("write to a String");
    for u in &case.uses {
        writeln!(text, "{u}").expect("write to a String");
    }
    vec![
        ("Use.fs".to_owned(), text),
        (
            "Program.fs".to_owned(),
            "module Program\n\nlet z = 0\n".to_owned(),
        ),
    ]
}

/// The declaration kinds of `case`'s A, by name: what a coverage census
/// reports against.
pub fn kinds(case: &Case) -> BTreeSet<&'static str> {
    fn kind(item: &Item) -> &'static str {
        match item {
            Item::Module {
                auto_open: true, ..
            } => "auto-open module",
            Item::Module { rqa: true, .. } => "rqa module",
            Item::Module { .. } => "module",
            Item::Value { .. } => "value",
            Item::Literal { .. } => "literal",
            Item::Function {
                compiled_name: Some(_),
                ..
            } => "compiled-name function",
            Item::Function { .. } => "function",
            Item::ActivePattern { .. } => "active pattern",
            Item::Record { .. } => "record",
            Item::Union { .. } => "union",
            Item::Class { .. } => "class",
            Item::Interface { .. } => "interface",
            Item::Abbrev { .. } => "abbreviation",
            Item::Exception { .. } => "exception",
            Item::Measure { .. } => "measure",
            Item::OptExtension { .. } => "optional extension",
            Item::CsExtension { .. } => "C#-style extension",
        }
    }
    fn walk(decls: &[Decl], out: &mut BTreeSet<&'static str>) {
        for d in decls {
            out.insert(kind(&d.item));
            if d.hidden {
                out.insert("fsi-hidden item");
            }
            if item_access(&d.item) == Access::Internal {
                out.insert("internal item");
            }
            if let Item::Module { items, .. } = &d.item {
                walk(items, out);
            }
        }
    }
    let mut out = BTreeSet::new();
    for f in &case.files {
        for b in &f.blocks {
            match b {
                Block::Namespace { decls, .. } => {
                    out.insert("namespace");
                    walk(decls, &mut out);
                }
                Block::TopModule {
                    decls, auto_open, ..
                } => {
                    out.insert(if *auto_open {
                        "auto-open top-level module"
                    } else {
                        "top-level module"
                    });
                    walk(decls, &mut out);
                }
            }
        }
    }
    if case.assembly_auto_open.is_some() {
        out.insert("assembly-level auto-open");
    }
    match case.ivt {
        Ivt::None => {}
        Ivt::Consumer => {
            out.insert("IVT to the consumer");
        }
        Ivt::Other => {
            out.insert("IVT to another assembly");
        }
    }
    out
}
