//! A generated, FCS-graded grid of **what a union case or exception head
//! resolves to and whether the patterns under it bind**, as one project.
//!
//! Two families of cells, each probed by the same four uses — a
//! type-qualified head in a pattern and in an expression, and the bare head
//! in each — with an outer `x` that a use reaches when the pattern under its
//! head binds nothing:
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
//!   abandons the pattern under the head.
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
use crate::common::full_bcl_env;
use crate::common::use_grade::{FileBuilder, Graded, OurVerdict, Site, grade_project};
use borzoi_cst::syntax::TextRange;
use borzoi_oracle_harness::manifest::Manifest;
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

struct AttributeCell {
    at: UnionAt,
    attr: Attr,
    on: AttrOn,
}

impl AttributeCell {
    fn label(&self) -> String {
        let at = match self.at {
            UnionAt::EarlierFile => "declEarlier",
            UnionAt::UseModule => "declLocal",
        };
        format!("{at}/{}/{}", self.on.tag(), self.attr.tag())
    }

    fn all() -> Vec<AttributeCell> {
        let mut out = Vec::new();
        for at in UnionAt::ALL {
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

    fn write(
        &self,
        j: usize,
        earlier: &mut FileBuilder,
        main: &mut FileBuilder,
        c: &mut Collected,
    ) {
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
        main.line(&format!("module Q{j} ="));
        let (qualified, bare, scrutinee, between) = match (self.on, self.at) {
            (AttrOn::Exception, UnionAt::EarlierFile) => {
                earlier.line(&format!("namespace X{j}"));
                lines(earlier, "", &decl);
                (
                    format!("X{j}.E{j}"),
                    format!("E{j}"),
                    ": exn",
                    Some(format!("open X{j}")),
                )
            }
            (AttrOn::Exception, UnionAt::UseModule) => {
                main.line(&format!("{ind}module Ex{j} ="));
                lines(main, &format!("{ind}    "), &decl);
                (
                    format!("Ex{j}.E{j}"),
                    format!("E{j}"),
                    ": exn",
                    Some(format!("open Ex{j}")),
                )
            }
            (_, UnionAt::EarlierFile) => {
                earlier.line(&format!("namespace X{j}"));
                lines(earlier, "", &decl);
                main.line(&format!("{ind}open X{j}"));
                (format!("V{j}.K{j}"), format!("K{j}"), "", None)
            }
            (_, UnionAt::UseModule) => {
                lines(main, ind, &decl);
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

/// FCS's diagnostics that judge a use rather than resolve it: an
/// error-level `[<Obsolete>]` (FS0101) or `[<CompilerMessage>]` (its own
/// number), a type mismatch (FS0001) or wrong argument count (FS0727) under
/// a head FCS resolved, and an expression qualifier whose namesakes all
/// take type arguments (FS1124), which FCS reports and resolves anyway.
/// With these alone at a site, FCS's record there is its resolution.
fn judges_the_use(number: i64) -> bool {
    matches!(number, 1 | 101 | 727 | 1124 | 9001)
}

/// FCS's resolution at a site, when it has one: its record, unless an error
/// at the site is about something other than the use.
fn fcs_resolution(g: &Graded) -> Option<(usize, TextRange)> {
    g.errors
        .iter()
        .all(|&n| judges_the_use(n))
        .then_some(g.record)
        .flatten()
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
    g.record.is_none()
        && by_label
            .get(format!("{cell}ExprHead").as_str())
            .is_some_and(|head| !head.errors.is_empty())
}

/// We commit a site to anything but FCS's resolution there.
fn wrong(g: &Graded) -> bool {
    match &g.ours {
        OurVerdict::Declined => false,
        OurVerdict::Committed(f, r) => fcs_resolution(g) != Some((*f, *r)),
    }
}

#[test]
fn case_heads_and_their_binders_agree_with_fcs() {
    let mut earlier = FileBuilder::new(0);
    let mut main = FileBuilder::new(1);
    main.line("module Use");
    main.line("");
    let mut c = Collected::default();
    let namesake_cells = NamesakeCell::all();
    for (i, cell) in namesake_cells.iter().enumerate() {
        cell.write(i, &mut earlier, &mut main, &mut c);
    }
    let attribute_cells = AttributeCell::all();
    for (j, cell) in attribute_cells.iter().enumerate() {
        cell.write(j, &mut earlier, &mut main, &mut c);
    }
    let files = vec![("earlier.fs", earlier.text), ("main.fs", main.text)];
    let graded = grade_project("chg", &files, &c.sites, &c.binders, full_bcl_env());
    eprintln!(
        "case head grid: {} namesake cells, {} attribute cells, {} uses, {} binders",
        namesake_cells.len(),
        attribute_cells.len(),
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
                "  {:<70} fcs {:?} errors {:?} | ours {:?}",
                g.label, g.record, g.errors, g.ours
            );
        }
        let unchecked = unchecked_argument(g, &by_label);
        if wrong(g) && !unchecked {
            failures.push(format!(
                "[{}] FCS {:?} (errors {:?}) | we gave {:?}",
                g.label, g.record, g.errors, g.ours
            ));
        }
        let fcs = match (fcs_resolution(g), g.errors.is_empty()) {
            _ if unchecked => "unchecked",
            (Some(_), true) => "resolved",
            (Some(_), false) => "resolved with error",
            (None, _) => "unresolved",
        };
        let ours = match g.ours {
            OurVerdict::Committed(..) => "commit",
            OurVerdict::Declined => "decline",
        };
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
    failures.extend(graded.completeness_failures);
    assert!(
        failures.is_empty(),
        "{} failure(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    // Liveness: both families commit heads and intern binders somewhere, so
    // certain-implies-exact is not passing by declining.
    for family in ["union", "decl"] {
        assert!(
            graded.sites.iter().any(|g| g.label.starts_with(family)
                && g.label.ends_with("PatHead")
                && matches!(g.ours, OurVerdict::Committed(..))),
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
