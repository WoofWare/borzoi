//! A generated, FCS-graded grid of **what a union case or exception head
//! resolves to and whether the patterns under it bind**, as one project.
//!
//! Four families of cells. The first two are probed by the same four uses
//! — a type-qualified head in a pattern and in an expression, and the bare
//! head in each — with an outer `x` that a use reaches when the pattern
//! under its head binds nothing:
//!
//! - [`NamesakeCell`]: a union `T<'a>` owning `C`, and another type named
//!   `T` ([`Namesake`]) of lower, the same or higher generic arity
//!   ([`Arity`]), entering the name environment before or after the union
//!   ([`Order`]), from an earlier file or a module of the use's file, or
//!   from an earlier file's namespace the use does not open
//!   ([`NamesakeAt`]), with the union itself in an earlier file or the
//!   use's module ([`UnionAt`]). In pattern position FCS tries every type of the
//!   head's name latest first and takes the first that finds `C`
//!   (`ResolvePatternLongIdentPrim`'s `tyconSearch`); in an expression it
//!   sorts them by arity first (`CheckForTypeLegitimacyAndMultipleGenericTypeAmbiguities`).
//!   A namesake that finds `C` as a record field abandons the pattern under
//!   the head; one that finds a case of its own takes the head.
//! - [`AttributeCell`]: a union or exception carrying an attribute
//!   ([`Attr`]) on the case, on the union, or on another case
//!   ([`AttrOn`]). FCS checks a case's attributes and its union's before the
//!   arguments of a pattern it heads (`CheckUnionCaseAttributes`, or
//!   `CheckEntityAttributes` for an exception), and an error-level one
//!   (`[<Obsolete(…, true)>]`, `[<CompilerMessage(…, IsError = true)>]`)
//!   abandons the pattern under the head. The union or exception sits in
//!   an earlier file, the use's module, or the referenced fixture assembly
//!   ([`DeclAt`]), where a case's and an exception's attributes live in
//!   its F# signature data alone.
//!
//! The other two probe qualified paths:
//!
//! - [`PathCell`]: an attribute on a module, on a module nested in it, or
//!   on the types the nested module declares ([`PathAttrOn`]), wherever
//!   [`DeclAt`] puts them, probed by every kind of path through them — a
//!   value, a static member, a case qualified by its type or its module, a
//!   pattern head, an annotation, a record label, a module abbreviation —
//!   and by the names an `open` of the nested module brings into scope.
//!   FCS checks every module and type a path names on its way to the item
//!   (`SendEntityPathToSink`) and the module an `open` or an abbreviation
//!   names, and an error-level attribute leaves the path unresolved or
//!   abandons the declaration.
//! - [`HeaderCell`]: the same on a file's top-level `module` header, in an
//!   implementation or its signature ([`HeaderSig`]); a later file sees
//!   the signature's attributes, not the implementation's.
//!
//! Every use is held to certain-implies-exact against FCS's record at the
//! site ([`wrong`]), but an argument FCS never checked
//! ([`unchecked_argument`]); every pattern binder the walk interns must be
//! one FCS binds, and every one FCS abandons must be declined; binder
//! completeness holds over the project. Each site's pair of verdicts, the
//! walk's declines and FCS's unchecked arguments among them, is pinned in
//! `tests/manifests/case_head_grid.txt`, so a decline that starts to commit,
//! or a commit that starts to decline, shows as manifest movement.

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::common::use_grade::{
    FileBuilder, Graded, GradedProject, OurVerdict, Site, grade_project_with_refs,
};
use crate::common::{
    ensure_case_attr_fixture_built, ensure_fsharp_core_dll, ensure_system_runtime_dll,
};
use crate::unmodelled_contributor_grid::{agrees, env_of};
use borzoi_cst::syntax::TextRange;
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_sema::{AssemblyEnv, Resolution};
use std::collections::HashMap;

/// The site of the `nth` whole-word occurrence of `word` in `line`, once
/// `line` is the next line `f` appends.
fn word_site(f: &FileBuilder, line: &str, word: &str, nth: usize, label: String) -> Site {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    let at = line
        .match_indices(word)
        .filter(|&(i, _)| {
            !line[..i].chars().next_back().is_some_and(is_ident)
                && !line[i + word.len()..].chars().next().is_some_and(is_ident)
        })
        .nth(nth)
        .unwrap_or_else(|| panic!("{word:?} occurs {} times in {line:?}", nth + 1))
        .0;
    let start = f.text.len() + at;
    Site {
        file: f.index,
        range: TextRange::new(
            u32::try_from(start).unwrap().into(),
            u32::try_from(start + word.len()).unwrap().into(),
        ),
        label,
    }
}

/// The probes every cell writes, at indentation `ind`: `qualified` is the
/// type- (or module-) qualified head, `bare` the head alone; `scrutinee`
/// annotates the matched value when it needs one (an exception).
struct Probes<'a> {
    qualified: &'a str,
    bare: &'a str,
    scrutinee: &'a str,
}

/// Sites and binders collected while writing the cells.
#[derive(Default)]
struct Collected {
    sites: Vec<Site>,
    binders: Vec<Site>,
    /// The site of each dotted path's last segment, to the site of the whole
    /// path: FCS records a referenced assembly's type over the path ending at
    /// it, where the walk records it at its own segment.
    whole_of: HashMap<String, String>,
}

impl Collected {
    /// The pattern probe `head x -> ignore x`: the head, the binder and the
    /// use, labelled `{label}/{form}…`.
    fn pattern(
        &mut self,
        f: &mut FileBuilder,
        ind: &str,
        head: &str,
        scrutinee: &str,
        label: &str,
        form: &str,
    ) {
        let line = format!(
            "{ind}let p{form} (b{scrutinee}) = match b with {head} x -> ignore x | _ -> ()"
        );
        self.sites.push(word_site(
            f,
            &line,
            head,
            0,
            format!("{label}/{form}PatHead"),
        ));
        self.binders.push(word_site(
            f,
            &line,
            "x",
            0,
            format!("{label}/{form}PatBinder"),
        ));
        self.sites
            .push(word_site(f, &line, "x", 1, format!("{label}/{form}PatUse")));
        f.line(&line);
    }

    /// The expression probe `head x`: the head and the argument's use.
    fn expression(&mut self, f: &mut FileBuilder, ind: &str, head: &str, label: &str, form: &str) {
        let line = format!("{ind}let e{form} = {head} x");
        self.sites.push(word_site(
            f,
            &line,
            head,
            0,
            format!("{label}/{form}ExprHead"),
        ));
        self.sites.push(word_site(
            f,
            &line,
            "x",
            0,
            format!("{label}/{form}ExprArg"),
        ));
        f.line(&line);
    }

    /// The qualified probes, then `between` (an `open`, for an exception
    /// whose bare name needs one), then the bare probes.
    fn probes(
        &mut self,
        f: &mut FileBuilder,
        ind: &str,
        p: &Probes<'_>,
        between: Option<&str>,
        label: &str,
    ) {
        f.line(&format!("{ind}let x = 1"));
        self.pattern(f, ind, p.qualified, p.scrutinee, label, "q");
        self.expression(f, ind, p.qualified, label, "q");
        if let Some(line) = between {
            f.line(&format!("{ind}{line}"));
        }
        self.pattern(f, ind, p.bare, p.scrutinee, label, "u");
        self.expression(f, ind, p.bare, label, "u");
    }
}

/// `decl`'s lines at indentation `ind`.
fn lines(f: &mut FileBuilder, ind: &str, decl: &str) {
    for l in decl.lines() {
        f.line(&format!("{ind}{l}"));
    }
}

/// The other declaration of the union's name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Namesake {
    /// A record with a field of the case's name: FCS's lookup finds it.
    Record,
    /// A union with a case of the case's name.
    UnionWithCase,
    /// A union without one: the lookup finds nothing and goes on.
    UnionWithoutCase,
}

impl Namesake {
    const ALL: [Namesake; 3] = [
        Namesake::Record,
        Namesake::UnionWithCase,
        Namesake::UnionWithoutCase,
    ];

    fn tag(self) -> &'static str {
        match self {
            Namesake::Record => "record",
            Namesake::UnionWithCase => "unionWithCase",
            Namesake::UnionWithoutCase => "unionWithoutCase",
        }
    }

    fn decl(self, i: usize, arity: Arity) -> String {
        let generics = arity.generics();
        match self {
            Namesake::Record => format!("type T{i}{generics} = {{ C{i}: int }}"),
            Namesake::UnionWithCase => {
                format!("type T{i}{generics} =\n    | C{i} of int\n    | E{i}")
            }
            Namesake::UnionWithoutCase => {
                format!("type T{i}{generics} =\n    | E{i} of int\n    | F{i}")
            }
        }
    }
}

/// The namesake's generic arity, against the union's one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arity {
    Lower,
    Same,
    Higher,
}

impl Arity {
    const ALL: [Arity; 3] = [Arity::Lower, Arity::Same, Arity::Higher];

    fn tag(self) -> &'static str {
        match self {
            Arity::Lower => "lower",
            Arity::Same => "same",
            Arity::Higher => "higher",
        }
    }

    fn generics(self) -> &'static str {
        match self {
            Arity::Lower => "",
            Arity::Same => "<'a>",
            Arity::Higher => "<'a, 'b>",
        }
    }
}

/// When the namesake enters the use's name environment, against the union.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Order {
    Before,
    After,
}

impl Order {
    const ALL: [Order; 2] = [Order::Before, Order::After];

    fn tag(self) -> &'static str {
        match self {
            Order::Before => "before",
            Order::After => "after",
        }
    }
}

/// Where the union sits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UnionAt {
    /// An earlier file's `namespace U{i}`, which the use's module opens.
    EarlierFile,
    /// The use's module.
    UseModule,
}

impl UnionAt {
    const ALL: [UnionAt; 2] = [UnionAt::EarlierFile, UnionAt::UseModule];

    fn tag(self) -> &'static str {
        match self {
            UnionAt::EarlierFile => "unionEarlier",
            UnionAt::UseModule => "unionLocal",
        }
    }
}

/// Where the namesake sits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NamesakeAt {
    /// An earlier file's `namespace S{i}`, which the use's module opens.
    EarlierFile,
    /// A module `L{i}` the use's module declares and opens.
    LocalModule,
    /// An earlier file's `namespace S{i}`, which the use does not open: FCS
    /// never tries it, whatever the order.
    EarlierUnopened,
}

impl NamesakeAt {
    const ALL: [NamesakeAt; 3] = [
        NamesakeAt::EarlierFile,
        NamesakeAt::LocalModule,
        NamesakeAt::EarlierUnopened,
    ];

    fn tag(self) -> &'static str {
        match self {
            NamesakeAt::EarlierFile => "namesakeEarlier",
            NamesakeAt::LocalModule => "namesakeLocal",
            NamesakeAt::EarlierUnopened => "namesakeUnopened",
        }
    }
}

/// One [`NamesakeCell`]: `None` for the control without a namesake.
struct NamesakeCell {
    union_at: UnionAt,
    namesake: Option<(Namesake, Arity, Order, NamesakeAt)>,
}

impl NamesakeCell {
    fn label(&self) -> String {
        match self.namesake {
            None => format!("{}/none", self.union_at.tag()),
            Some((kind, arity, order, at)) => format!(
                "{}/{}/{}/{}/{}",
                self.union_at.tag(),
                kind.tag(),
                arity.tag(),
                order.tag(),
                at.tag()
            ),
        }
    }

    fn all() -> Vec<NamesakeCell> {
        let mut out = Vec::new();
        for union_at in UnionAt::ALL {
            out.push(NamesakeCell {
                union_at,
                namesake: None,
            });
            for kind in Namesake::ALL {
                for arity in Arity::ALL {
                    for order in Order::ALL {
                        for at in NamesakeAt::ALL {
                            if at == NamesakeAt::EarlierUnopened && order == Order::After {
                                continue;
                            }
                            out.push(NamesakeCell {
                                union_at,
                                namesake: Some((kind, arity, order, at)),
                            });
                        }
                    }
                }
            }
        }
        out
    }

    fn write(
        &self,
        i: usize,
        earlier: &mut FileBuilder,
        main: &mut FileBuilder,
        c: &mut Collected,
    ) {
        let union = format!("type T{i}<'a> =\n    | C{i} of 'a\n    | D{i}");
        let ind = "    ";
        if self.union_at == UnionAt::EarlierFile {
            earlier.line(&format!("namespace U{i}"));
            lines(earlier, "", &union);
        }
        main.line(&format!("module P{i} ="));
        // The union entering the environment: its `open`, or its declaration.
        let union_enters = |main: &mut FileBuilder| match self.union_at {
            UnionAt::EarlierFile => main.line(&format!("{ind}open U{i}")),
            UnionAt::UseModule => lines(main, ind, &union),
        };
        match self.namesake {
            None => union_enters(main),
            Some((kind, arity, order, at)) => {
                let decl = kind.decl(i, arity);
                let namesake_enters = |main: &mut FileBuilder| match at {
                    NamesakeAt::EarlierFile => main.line(&format!("{ind}open S{i}")),
                    NamesakeAt::LocalModule => {
                        main.line(&format!("{ind}module L{i} ="));
                        lines(main, &format!("{ind}    "), &decl);
                        main.line(&format!("{ind}open L{i}"));
                    }
                    NamesakeAt::EarlierUnopened => {}
                };
                if matches!(at, NamesakeAt::EarlierFile | NamesakeAt::EarlierUnopened) {
                    earlier.line(&format!("namespace S{i}"));
                    lines(earlier, "", &decl);
                }
                match order {
                    Order::Before => {
                        namesake_enters(main);
                        union_enters(main);
                    }
                    Order::After => {
                        union_enters(main);
                        namesake_enters(main);
                    }
                }
            }
        }
        let qualified = format!("T{i}.C{i}");
        let bare = format!("C{i}");
        c.probes(
            main,
            ind,
            &Probes {
                qualified: &qualified,
                bare: &bare,
                scrutinee: "",
            },
            None,
            &self.label(),
        );
    }
}

/// An attribute a case, a union or an exception carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attr {
    None,
    ObsoleteWarning,
    /// Warning-level, but written with two arguments.
    ObsoleteWarningExplicit,
    ObsoleteError,
    CompilerMessageWarning,
    CompilerMessageError,
    Experimental,
}

impl Attr {
    const ALL: [Attr; 7] = [
        Attr::None,
        Attr::ObsoleteWarning,
        Attr::ObsoleteWarningExplicit,
        Attr::ObsoleteError,
        Attr::CompilerMessageWarning,
        Attr::CompilerMessageError,
        Attr::Experimental,
    ];

    fn tag(self) -> &'static str {
        match self {
            Attr::None => "none",
            Attr::ObsoleteWarning => "obsoleteWarning",
            Attr::ObsoleteWarningExplicit => "obsoleteWarningExplicit",
            Attr::ObsoleteError => "obsoleteError",
            Attr::CompilerMessageWarning => "compilerMessageWarning",
            Attr::CompilerMessageError => "compilerMessageError",
            Attr::Experimental => "experimental",
        }
    }

    fn text(self) -> &'static str {
        match self {
            Attr::None => "",
            Attr::ObsoleteWarning => "[<System.Obsolete(\"w\")>] ",
            Attr::ObsoleteWarningExplicit => "[<System.Obsolete(\"w\", false)>] ",
            Attr::ObsoleteError => "[<System.Obsolete(\"e\", true)>] ",
            Attr::CompilerMessageWarning => "[<CompilerMessage(\"m\", 9001)>] ",
            Attr::CompilerMessageError => "[<CompilerMessage(\"m\", 9001, IsError = true)>] ",
            Attr::Experimental => "[<Experimental(\"x\")>] ",
        }
    }
}

/// What carries the [`Attr`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AttrOn {
    /// The probed case.
    Case,
    /// Another case of its union.
    OtherCase,
    /// The union type.
    Union,
    /// An exception, the probed head.
    Exception,
}

impl AttrOn {
    fn tag(self) -> &'static str {
        match self {
            AttrOn::Case => "onCase",
            AttrOn::OtherCase => "onOtherCase",
            AttrOn::Union => "onUnion",
            AttrOn::Exception => "onException",
        }
    }
}

/// Where an [`AttributeCell`]'s or a [`PathCell`]'s declarations sit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclAt {
    /// An earlier file's namespace.
    EarlierFile,
    /// The use's module.
    UseModule,
    /// A namespace of the referenced fixture assembly
    /// (`tests/fixtures/case_attr_env`), read from its metadata.
    Referenced,
}

impl DeclAt {
    const ALL: [DeclAt; 3] = [DeclAt::EarlierFile, DeclAt::UseModule, DeclAt::Referenced];

    fn tag(self) -> &'static str {
        match self {
            DeclAt::EarlierFile => "Earlier",
            DeclAt::UseModule => "Local",
            DeclAt::Referenced => "Referenced",
        }
    }
}

/// The files the cells write: the earlier project file, the use's file,
/// and the referenced fixture assembly's source.
struct Files {
    earlier: FileBuilder,
    main: FileBuilder,
    fixture: FileBuilder,
}

/// The fixture assembly's root namespace.
const FIXTURE_NAMESPACE: &str = "CaFix";

struct AttributeCell {
    at: DeclAt,
    attr: Attr,
    on: AttrOn,
}

impl AttributeCell {
    fn label(&self) -> String {
        format!(
            "decl{}/{}/{}",
            self.at.tag(),
            self.on.tag(),
            self.attr.tag()
        )
    }

    fn all() -> Vec<AttributeCell> {
        let mut out = Vec::new();
        for at in DeclAt::ALL {
            for attr in Attr::ALL {
                let ons: &[AttrOn] = match attr {
                    Attr::None => &[AttrOn::Case, AttrOn::Exception],
                    Attr::ObsoleteError => &[
                        AttrOn::Case,
                        AttrOn::OtherCase,
                        AttrOn::Union,
                        AttrOn::Exception,
                    ],
                    _ => &[AttrOn::Case, AttrOn::Union, AttrOn::Exception],
                };
                for &on in ons {
                    out.push(AttributeCell { at, attr, on });
                }
            }
        }
        out
    }

    fn write(&self, j: usize, files: &mut Files, c: &mut Collected) {
        let a = self.attr.text();
        let on = |o: AttrOn| if self.on == o { a } else { "" };
        let ind = "    ";
        let decl = if self.on == AttrOn::Exception {
            format!("{}exception E{j} of int", a.replace("] ", "]\n"))
        } else {
            format!(
                "{}type V{j}<'a> =\n    | {}K{j} of 'a\n    | {}L{j}",
                on(AttrOn::Union).replace("] ", "]\n"),
                on(AttrOn::Case),
                on(AttrOn::OtherCase)
            )
        };
        let main = &mut files.main;
        main.line(&format!("module Q{j} ="));
        let (qualified, bare, scrutinee, between) = match (self.on, self.at) {
            (AttrOn::Exception, DeclAt::EarlierFile) => {
                files.earlier.line(&format!("namespace X{j}"));
                lines(&mut files.earlier, "", &decl);
                (
                    format!("X{j}.E{j}"),
                    format!("E{j}"),
                    ": exn",
                    Some(format!("open X{j}")),
                )
            }
            (AttrOn::Exception, DeclAt::UseModule) => {
                main.line(&format!("{ind}module Ex{j} ="));
                lines(main, &format!("{ind}    "), &decl);
                (
                    format!("Ex{j}.E{j}"),
                    format!("E{j}"),
                    ": exn",
                    Some(format!("open Ex{j}")),
                )
            }
            (AttrOn::Exception, DeclAt::Referenced) => {
                files
                    .fixture
                    .line(&format!("namespace {FIXTURE_NAMESPACE}.X{j}"));
                lines(&mut files.fixture, "", &decl);
                main.line(&format!("{ind}open {FIXTURE_NAMESPACE}"));
                (
                    format!("X{j}.E{j}"),
                    format!("E{j}"),
                    ": exn",
                    Some(format!("open X{j}")),
                )
            }
            (_, DeclAt::EarlierFile) => {
                files.earlier.line(&format!("namespace X{j}"));
                lines(&mut files.earlier, "", &decl);
                main.line(&format!("{ind}open X{j}"));
                (format!("V{j}.K{j}"), format!("K{j}"), "", None)
            }
            (_, DeclAt::UseModule) => {
                lines(main, ind, &decl);
                (format!("V{j}.K{j}"), format!("K{j}"), "", None)
            }
            (_, DeclAt::Referenced) => {
                files
                    .fixture
                    .line(&format!("namespace {FIXTURE_NAMESPACE}.X{j}"));
                lines(&mut files.fixture, "", &decl);
                main.line(&format!("{ind}open {FIXTURE_NAMESPACE}.X{j}"));
                (format!("V{j}.K{j}"), format!("K{j}"), "", None)
            }
        };
        c.probes(
            main,
            ind,
            &Probes {
                qualified: &qualified,
                bare: &bare,
                scrutinee,
            },
            between.as_deref(),
            &self.label(),
        );
    }
}

/// Which entity on a qualified path carries a [`PathCell`]'s attribute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PathAttrOn {
    /// The outer module `O`.
    Outer,
    /// The module `I` nested in `O`.
    Inner,
    /// The types `I` declares: a type with a static member, a union, a
    /// record and an exception.
    Types,
}

impl PathAttrOn {
    const ALL: [PathAttrOn; 3] = [PathAttrOn::Outer, PathAttrOn::Inner, PathAttrOn::Types];

    fn tag(self) -> &'static str {
        match self {
            PathAttrOn::Outer => "onOuter",
            PathAttrOn::Inner => "onInner",
            PathAttrOn::Types => "onTypes",
        }
    }
}

/// The attributes a [`PathCell`] tries: none, a warning written without a
/// tuple, a warning written with one (which the walk cannot tell from an
/// error without resolving its name), and the two error-level ones.
const PATH_ATTRS: [Attr; 5] = [
    Attr::None,
    Attr::ObsoleteWarning,
    Attr::ObsoleteWarningExplicit,
    Attr::ObsoleteError,
    Attr::CompilerMessageError,
];

/// An attribute ([`Attr`]) on an entity along qualified paths
/// ([`PathAttrOn`]): a module `O` declaring a value and a module `I`, which
/// declares a value, a type with a static member, a union, a record and an
/// exception. FCS checks every module and type a qualified path names on
/// its way to the item (`SendEntityPathToSink`), and an error-level
/// attribute on one leaves the path unresolved; an `open` (or a module
/// abbreviation) checks the module it names, and an error-level attribute
/// there abandons the declaration, so nothing it would bring into scope is.
struct PathCell {
    at: DeclAt,
    attr: Attr,
    on: PathAttrOn,
}

impl PathCell {
    fn label(&self) -> String {
        format!(
            "path{}/{}/{}",
            self.at.tag(),
            self.on.tag(),
            self.attr.tag()
        )
    }

    fn all() -> Vec<PathCell> {
        let mut out = Vec::new();
        for at in DeclAt::ALL {
            for attr in PATH_ATTRS {
                for on in PathAttrOn::ALL {
                    if attr == Attr::None && on != PathAttrOn::Outer {
                        continue;
                    }
                    out.push(PathCell { at, attr, on });
                }
            }
        }
        out
    }

    fn write(&self, k: usize, files: &mut Files, c: &mut Collected) {
        let a = self.attr.text();
        let on = |o: PathAttrOn| if self.on == o { a } else { "" };
        // Names no other family spells.
        let n = |stem: &str| format!("{stem}{k}");
        let (o, i, s, t, r) = (n("Po"), n("Pi"), n("Ps"), n("Pt"), n("Pr"));
        let (case, nullary, field, exn) = (n("Pc"), n("Pd"), n("Pf"), n("Pe"));
        let (v, w, p, abbrev) = (n("pv"), n("pw"), n("Pp"), n("Pa"));
        let decl = format!(
            "{outer}module {o} =\n    \
             let {v} = 1\n    \
             {inner}module {i} =\n        \
             let {w} = 2\n        \
             {ty}type {s} =\n            static member {p} = 3\n        \
             {ty}type {t} =\n            | {case} of int\n            | {nullary}\n        \
             {ty}type {r} = {{ {field}: int }}\n        \
             {ty}exception {exn} of int",
            outer = on(PathAttrOn::Outer).replace("] ", "]\n"),
            inner = on(PathAttrOn::Inner).replace("] ", "]\n    "),
            ty = on(PathAttrOn::Types).replace("] ", "]\n        "),
        );
        let ind = "    ";
        let main = &mut files.main;
        main.line(&format!("module {} =", n("Pz")));
        match self.at {
            DeclAt::EarlierFile => {
                files.earlier.line(&format!("namespace {}", n("Py")));
                lines(&mut files.earlier, "", &decl);
                main.line(&format!("{ind}open {}", n("Py")));
            }
            DeclAt::UseModule => lines(main, ind, &decl),
            DeclAt::Referenced => {
                files
                    .fixture
                    .line(&format!("namespace {FIXTURE_NAMESPACE}.{}", n("Py")));
                lines(&mut files.fixture, "", &decl);
                main.line(&format!("{ind}open {FIXTURE_NAMESPACE}.{}", n("Py")));
            }
        }
        let label = self.label();
        main.line(&format!("{ind}let x = 1"));
        // Expressions.
        c.path_expr(main, ind, &format!("{o}.{v}"), &label, "value");
        c.path_expr(main, ind, &format!("{o}.{i}.{w}"), &label, "nestedValue");
        c.path_expr(
            main,
            ind,
            &format!("{o}.{i}.{s}.{p}"),
            &label,
            "staticMember",
        );
        c.path_expr(
            main,
            ind,
            &format!("{o}.{i}.{t}.{nullary}"),
            &label,
            "typeCase",
        );
        c.path_expr(
            main,
            ind,
            &format!("{o}.{i}.{nullary}"),
            &label,
            "moduleCase",
        );
        // Patterns.
        c.path_pattern(
            main,
            ind,
            &format!("{o}.{i}.{case}"),
            "",
            &label,
            "modulePat",
        );
        c.path_pattern(
            main,
            ind,
            &format!("{o}.{i}.{t}.{case}"),
            "",
            &label,
            "typePat",
        );
        c.path_pattern(
            main,
            ind,
            &format!("{o}.{i}.{exn}"),
            ": exn",
            &label,
            "exnPat",
        );
        // A type annotation, and a type-qualified record label.
        let annotated = format!("{o}.{i}.{t}");
        let line = format!("{ind}let ann (b: {annotated}) = b");
        c.path_line(main, &line, &annotated, &label, "annotation");
        let labelled = format!("{o}.{i}.{r}.{field}");
        let line = format!("{ind}let lbl = {{ {labelled} = 1 }}");
        c.path_line(main, &line, &labelled, &label, "label");
        // A module abbreviation, then a path through it.
        let target = format!("{o}.{i}");
        let line = format!("{ind}module {abbrev} = {target}");
        c.path_line(main, &line, &target, &label, "abbrevTarget");
        c.path_expr(main, ind, &format!("{abbrev}.{w}"), &label, "viaAbbrev");
        // An `open` of the inner module, then its names bare.
        let line = format!("{ind}open {target}");
        c.path_line(main, &line, &target, &label, "openTarget");
        c.path_expr(main, ind, &w, &label, "openedValue");
        c.path_expr(main, ind, &format!("{s}.{p}"), &label, "openedStatic");
        c.path_pattern(main, ind, &case, "", &label, "openedPat");
        c.path_pattern(main, ind, &exn, ": exn", &label, "openedExnPat");
        // A nullary head, a variable to FCS where no case of its name is in
        // scope; binder completeness grades what it declares there.
        let line = format!("{ind}let nul b = match b with {nullary} -> 0 | _ -> 1");
        c.path_line(main, &line, &nullary, &label, "openedNullary");
        let line = format!("{ind}let ann2 (b: {t}) = b");
        c.path_line(main, &line, &t, &label, "openedAnnotation");
        let line = format!("{ind}let lbl2 = {{ {field} = 1 }}");
        c.path_line(main, &line, &field, &label, "openedLabel");
    }
}

/// Which half of a [`HeaderCell`]'s module carries its attribute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HeaderSig {
    /// No signature: the implementation's header.
    NoSignature,
    /// A signature's header, its implementation's bare: what a later file
    /// sees of the module.
    OnSignature,
    /// The implementation's header, its signature's bare, which a later
    /// file never sees.
    OnImplementation,
}

impl HeaderSig {
    const ALL: [HeaderSig; 3] = [
        HeaderSig::NoSignature,
        HeaderSig::OnSignature,
        HeaderSig::OnImplementation,
    ];

    fn tag(self) -> &'static str {
        match self {
            HeaderSig::NoSignature => "noSig",
            HeaderSig::OnSignature => "onSig",
            HeaderSig::OnImplementation => "onImpl",
        }
    }
}

/// An attribute ([`Attr`]) on a file's top-level `module` header, in an
/// implementation or its signature ([`HeaderSig`]), probed from a later
/// file through paths and an `open` of the module.
struct HeaderCell {
    attr: Attr,
    sig: HeaderSig,
}

impl HeaderCell {
    fn label(&self) -> String {
        format!("header/{}/{}", self.sig.tag(), self.attr.tag())
    }

    fn all() -> Vec<HeaderCell> {
        let mut out = Vec::new();
        for attr in [
            Attr::None,
            Attr::ObsoleteWarningExplicit,
            Attr::ObsoleteError,
            Attr::CompilerMessageError,
        ] {
            for sig in HeaderSig::ALL {
                if attr == Attr::None && sig != HeaderSig::NoSignature {
                    continue;
                }
                out.push(HeaderCell { attr, sig });
            }
        }
        out
    }

    /// The cell's files, in Compile order: `(name, source)`.
    fn files(&self, n: usize) -> Vec<(String, String)> {
        let a = self.attr.text().replace("] ", "]\n");
        let on = |half: HeaderSig| {
            if self.sig == half { a.as_str() } else { "" }
        };
        let union = format!("type Ht{n} =\n    | Hc{n} of int\n    | Hd{n}\n");
        let implementation = |attr: &str| format!("{attr}module Ph{n}\nlet hv{n} = 1\n{union}");
        match self.sig {
            HeaderSig::NoSignature => vec![(format!("h{n}.fs"), implementation(&a))],
            HeaderSig::OnSignature | HeaderSig::OnImplementation => vec![
                (
                    format!("h{n}.fsi"),
                    format!(
                        "{}module Ph{n}\nval hv{n} : int\n{union}",
                        on(HeaderSig::OnSignature)
                    ),
                ),
                (
                    format!("h{n}.fs"),
                    implementation(on(HeaderSig::OnImplementation)),
                ),
            ],
        }
    }

    fn write(&self, n: usize, main: &mut FileBuilder, c: &mut Collected) {
        let ind = "    ";
        let label = self.label();
        let module = format!("Ph{n}");
        main.line(&format!("module Hz{n} ="));
        main.line(&format!("{ind}let x = 1"));
        c.path_expr(main, ind, &format!("{module}.hv{n}"), &label, "value");
        c.path_expr(
            main,
            ind,
            &format!("{module}.Ht{n}.Hd{n}"),
            &label,
            "typeCase",
        );
        c.path_pattern(
            main,
            ind,
            &format!("{module}.Hc{n}"),
            "",
            &label,
            "modulePat",
        );
        let line = format!("{ind}open {module}");
        c.path_line(main, &line, &module, &label, "openTarget");
        c.path_expr(main, ind, &format!("hv{n}"), &label, "openedValue");
        c.path_pattern(main, ind, &format!("Hc{n}"), "", &label, "openedPat");
        let line = format!("{ind}let nul b = match b with Hd{n} -> 0 | _ -> 1");
        c.path_line(main, &line, &format!("Hd{n}"), &label, "openedNullary");
    }
}

impl Collected {
    /// A site for each segment of the dotted `path`, at its first
    /// occurrence in `line` (the next line `f` appends), and, for a path of
    /// more than one segment, one for the whole path: `{label}/{form}/{n}`
    /// for the `n`th segment, `{label}/{form}/whole`.
    fn path_sites(&mut self, f: &FileBuilder, line: &str, path: &str, label: &str, form: &str) {
        let start = line.find(path).expect("path occurs in its line");
        let base = f.text.len() + start;
        let site = |from: usize, len: usize, label: String| Site {
            file: f.index,
            range: TextRange::new(
                u32::try_from(from).unwrap().into(),
                u32::try_from(from + len).unwrap().into(),
            ),
            label,
        };
        let segments: Vec<&str> = path.split('.').collect();
        let mut offset = 0;
        for (n, seg) in segments.iter().enumerate() {
            self.sites.push(site(
                base + offset,
                seg.len(),
                format!("{label}/{form}/{n}"),
            ));
            offset += seg.len() + 1;
        }
        if segments.len() > 1 {
            let whole = format!("{label}/{form}/whole");
            self.whole_of.insert(
                format!("{label}/{form}/{}", segments.len() - 1),
                whole.clone(),
            );
            self.sites.push(site(base, path.len(), whole));
        }
    }

    /// Append `line`, with a site for each segment of `path` in it
    /// ([`Self::path_sites`]).
    fn path_line(&mut self, f: &mut FileBuilder, line: &str, path: &str, label: &str, form: &str) {
        self.path_sites(f, line, path, label, form);
        f.line(line);
    }

    /// The expression probe `let {form} = {path}`.
    fn path_expr(&mut self, f: &mut FileBuilder, ind: &str, path: &str, label: &str, form: &str) {
        self.path_line(f, &format!("{ind}let {form} = {path}"), path, label, form);
    }

    /// The pattern probe `match b with {path} x -> ignore x | _ -> ()`:
    /// the head's segments ([`Self::path_sites`]), the binder and the use.
    fn path_pattern(
        &mut self,
        f: &mut FileBuilder,
        ind: &str,
        path: &str,
        scrutinee: &str,
        label: &str,
        form: &str,
    ) {
        let line =
            format!("{ind}let {form} (b{scrutinee}) = match b with {path} x -> ignore x | _ -> ()");
        self.path_sites(f, &line, path, label, form);
        self.binders.push(word_site(
            f,
            &line,
            "x",
            0,
            format!("{label}/{form}/binder"),
        ));
        self.sites
            .push(word_site(f, &line, "x", 1, format!("{label}/{form}/use")));
        f.line(&line);
    }
}

/// FCS's diagnostics that judge a use rather than resolve it: an
/// error-level `[<Obsolete>]` (FS0101) or `[<CompilerMessage>]` (its own
/// number), a type mismatch (FS0001) or wrong argument count (FS0727) under
/// a head FCS resolved, and an expression qualifier whose namesakes all
/// take type arguments (FS1124), which FCS reports and resolves anyway.
/// With these alone at a site, FCS's record there is its resolution.
fn judges_the_use(number: i64) -> bool {
    matches!(number, 1 | 101 | 727 | 1124 | 9001)
}

/// Whether FCS's record at a site is its resolution: no error at the site
/// is about something other than the use.
fn record_is_resolution(g: &Graded) -> bool {
    g.errors.iter().all(|&n| judges_the_use(n))
}

/// FCS's resolution at a site to a project declaration, when it has one.
fn fcs_resolution(g: &Graded) -> Option<(usize, TextRange)> {
    record_is_resolution(g).then_some(g.record).flatten()
}

/// Whether FCS resolves the site to anything, a project declaration or a
/// referenced assembly's.
fn fcs_resolves(g: &Graded) -> bool {
    record_is_resolution(g)
        && g.record_use
            .as_ref()
            .is_some_and(|u| u.decl.is_some() || u.assembly.is_some())
}

/// Whether the walk's answer at a site names a referenced assembly's
/// entity, member or union case.
fn assembly_answer(g: &Graded) -> Option<Resolution> {
    g.resolution.filter(|r| {
        matches!(
            r,
            Resolution::Entity(_) | Resolution::Member { .. } | Resolution::UnionCase { .. }
        )
    })
}

/// Whether FCS never checked an expression's argument: it recorded nothing
/// there, and reported an error at the head of the same application, which
/// raised before the argument was checked (an error-level attribute, or a
/// head it resolved to something it cannot apply). FCS makes no claim about
/// such a site, so it is not graded; how many there are is pinned.
fn unchecked_argument(g: &Graded, by_label: &HashMap<&str, &Graded>) -> bool {
    let Some(cell) = g.label.strip_suffix("ExprArg") else {
        return false;
    };
    g.record_use.is_none()
        && by_label
            .get(format!("{cell}ExprHead").as_str())
            .is_some_and(|head| !head.errors.is_empty())
}

/// We commit a site to anything but FCS's resolution there. An answer in a
/// referenced assembly at a path's last segment, where FCS records nothing,
/// is graded against FCS's record over the whole path (`whole`, the site
/// [`Collected::whole_of`] names).
fn wrong(g: &Graded, whole: Option<&Graded>, env: &AssemblyEnv, graded: &GradedProject) -> bool {
    if let Some(res) = assembly_answer(g) {
        let reading = match (&g.record_use, whole) {
            (None, Some(whole)) => whole,
            _ => g,
        };
        return !(record_is_resolution(reading)
            && reading
                .record_use
                .as_ref()
                .is_some_and(|u| agrees(env, &graded.proj, &graded.paths, 0, res, u)));
    }
    match &g.ours {
        OurVerdict::Declined => false,
        OurVerdict::Committed(f, r) => fcs_resolution(g) != Some((*f, *r)),
    }
}

/// Whether the walk commits the site.
fn commits(g: &Graded) -> bool {
    matches!(g.ours, OurVerdict::Committed(..)) || assembly_answer(g).is_some()
}

#[test]
fn case_heads_and_their_binders_agree_with_fcs() {
    let header_cells = HeaderCell::all();
    let header_files: Vec<(String, String)> = header_cells
        .iter()
        .enumerate()
        .flat_map(|(n, cell)| cell.files(n))
        .collect();
    let mut files = Files {
        earlier: FileBuilder::new(0),
        main: FileBuilder::new(1 + header_files.len()),
        fixture: FileBuilder::new(usize::MAX),
    };
    files.main.line("module Use");
    files.main.line("");
    let mut c = Collected::default();
    let namesake_cells = NamesakeCell::all();
    for (i, cell) in namesake_cells.iter().enumerate() {
        cell.write(i, &mut files.earlier, &mut files.main, &mut c);
    }
    let attribute_cells = AttributeCell::all();
    for (j, cell) in attribute_cells.iter().enumerate() {
        cell.write(j, &mut files, &mut c);
    }
    let path_cells = PathCell::all();
    for (k, cell) in path_cells.iter().enumerate() {
        cell.write(k, &mut files, &mut c);
    }
    for (n, cell) in header_cells.iter().enumerate() {
        cell.write(n, &mut files.main, &mut c);
    }
    let fixture = ensure_case_attr_fixture_built(&files.fixture.text);
    let runtime = ensure_system_runtime_dll();
    let netstandard = runtime.parent().expect("ref dir").join("netstandard.dll");
    let fsharp_core = ensure_fsharp_core_dll();
    let env = env_of(&[&fsharp_core, &runtime, &netstandard, fixture]);
    let mut sources = vec![("earlier.fs", files.earlier.text)];
    sources.extend(
        header_files
            .iter()
            .map(|(name, src)| (name.as_str(), src.clone())),
    );
    sources.push(("main.fs", files.main.text));
    let graded = grade_project_with_refs("chg", &sources, &c.sites, &c.binders, &env, &[fixture]);
    eprintln!(
        "case head grid: {} namesake cells, {} attribute cells, {} path cells, {} header cells, \
         {} uses, {} binders",
        namesake_cells.len(),
        attribute_cells.len(),
        path_cells.len(),
        header_cells.len(),
        graded.sites.len(),
        graded.binders.len()
    );
    let report = std::env::var_os("BORZOI_GRID_REPORT").is_some();
    let by_label: HashMap<&str, &Graded> =
        graded.sites.iter().map(|g| (g.label.as_str(), g)).collect();
    let mut failures: Vec<String> = Vec::new();
    let mut entries: Vec<String> = Vec::new();
    for g in &graded.sites {
        if report {
            eprintln!(
                "  {:<70} fcs {:?} {:?} errors {:?} | ours {:?} {:?}",
                g.label,
                g.record,
                g.record_use.as_ref().and_then(|u| u.full_name.as_deref()),
                g.errors,
                g.ours,
                assembly_answer(g)
            );
        }
        let unchecked = unchecked_argument(g, &by_label);
        let whole = c
            .whole_of
            .get(&g.label)
            .and_then(|w| by_label.get(w.as_str()).copied());
        if wrong(g, whole, &env, &graded) && !unchecked {
            failures.push(format!(
                "[{}] FCS {:?} {:?} (errors {:?}) | we gave {:?} {:?}",
                g.label,
                g.record,
                g.record_use.as_ref().and_then(|u| u.full_name.as_deref()),
                g.errors,
                g.ours,
                assembly_answer(g)
            ));
        }
        let fcs = match (fcs_resolves(g), g.errors.is_empty()) {
            _ if unchecked => "unchecked",
            (true, true) => "resolved",
            (true, false) => "resolved with error",
            (false, _) => "unresolved",
        };
        let ours = if commits(g) { "commit" } else { "decline" };
        entries.push(format!("{}\tfcs {fcs} | ours {ours}", g.label));
    }
    for b in &graded.binders {
        if report {
            eprintln!(
                "  {:<70} fcs binds {} | interns {} opaque {}",
                b.label, b.fcs_binds, b.walk_interns, b.walk_opaque
            );
        }
        match (b.fcs_binds, b.walk_interns, b.walk_opaque) {
            (false, true, _) => failures.push(format!(
                "[{}] FCS abandons it; the walk interns it",
                b.label
            )),
            (false, false, false) => failures.push(format!(
                "[{}] FCS abandons it; the walk does not decline it",
                b.label
            )),
            _ => {}
        }
        let fcs = if b.fcs_binds { "binds" } else { "abandons" };
        let ours = if b.walk_interns {
            "interns"
        } else {
            "declines"
        };
        entries.push(format!("{}\tfcs {fcs} | ours {ours}", b.label));
    }
    failures.extend(graded.completeness_failures.iter().cloned());
    assert!(
        failures.is_empty(),
        "{} failure(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    // Liveness: every family commits heads and interns binders somewhere,
    // so certain-implies-exact is not passing by declining.
    for family in [
        "union",
        "declEarlier",
        "declLocal",
        "declReferenced",
        "pathEarlier",
        "pathLocal",
        "pathReferenced",
        "header",
    ] {
        let pattern_head = |label: &str| {
            label.ends_with("PatHead") || (label.contains("Pat/") && !label.ends_with("/use"))
        };
        assert!(
            graded
                .sites
                .iter()
                .any(|g| g.label.starts_with(family) && pattern_head(&g.label) && commits(g)),
            "no {family} cell commits a pattern head"
        );
        assert!(
            graded
                .binders
                .iter()
                .any(|b| b.label.starts_with(family) && b.walk_interns),
            "no {family} cell interns a binder"
        );
    }
    let manifest = Manifest::from_entries(entries).expect("manifest entries");
    check_manifest(
        "case_head_grid",
        &manifest,
        &regenerate("case_head_grid::case_heads_and_their_binders_agree_with_fcs"),
    );
}
