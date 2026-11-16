//! A generated, FCS-graded grid of **what an enclosing namespace's ancestors
//! make visible**.
//!
//! A namespace block opens its own namespace and nothing else
//! (`ImplicitlyOpenOwnNamespace`): inside `namespace A.B`, the contents of
//! `A` are not in scope unless an `open` brings them, while the root's are,
//! and so are those of the modules enclosing the use. A lookup that walks
//! every prefix of the enclosing container path reaches `A` too, and would
//! commit where FCS reports FS0039. A module abbreviation is narrower still:
//! it is no member of its namespace, so only its own block sees it, unless
//! it sits at the root.
//!
//! The axes:
//!
//! - where the declarations sit, relative to the use's namespace `A{i}.B`
//!   ([`Decl`]): the root (`namespace global`), `A{i}.B` itself, its
//!   ancestor `A{i}` (unopened, opened, or beside a namesake at the root), a
//!   sibling `A{i}.Sib`, an unrelated namespace the use opens, or a module
//!   enclosing the use;
//! - which file holds them ([`Placement`]): an earlier file, or an earlier
//!   block of the use's file;
//! - where the use sits ([`UseSite`]): a module of a `namespace A{i}.B`
//!   block, a module nested in one, or a module nested in a top-level
//!   `module A{i}.B.Top`;
//! - the use: a type-qualified union case in an expression and in a
//!   pattern, the bare case, the type in an annotation, a module-qualified
//!   value, an exception constructor, a value through a module
//!   abbreviation declared beside the module and through one the use's
//!   module declares, and a value an `open` of the module brings.
//!
//! The oracle is [`crate::common::use_grade`]'s: certain-implies-exact, and
//! every use FCS resolves must commit but the [`DECLINED`] gaps, so the grid
//! cannot pass by declining.

use crate::common::use_grade::{
    FcsVerdict, FileBuilder, Graded, Site, agrees, assert_sound_and_live, grade,
};

/// Where the cell's declarations sit, relative to the use's namespace
/// `A{i}.B`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Decl {
    /// `namespace global`.
    Root,
    /// `namespace A{i}.B`, the use's own namespace.
    Same,
    /// `namespace A{i}`, which the use does not open.
    Ancestor,
    /// `namespace A{i}`, which the use opens.
    AncestorOpened,
    /// `namespace A{i}` and `namespace global` both: FCS sees the root's.
    AncestorAndRoot,
    /// `namespace A{i}.Sib`, which the use does not open.
    Sibling,
    /// `namespace O{i}`, which the use opens.
    Opened,
    /// A module enclosing the use, in the use's file and block.
    EnclosingModule,
}

impl Decl {
    const ALL: [Decl; 8] = [
        Decl::Root,
        Decl::Same,
        Decl::Ancestor,
        Decl::AncestorOpened,
        Decl::AncestorAndRoot,
        Decl::Sibling,
        Decl::Opened,
        Decl::EnclosingModule,
    ];

    fn tag(self) -> &'static str {
        match self {
            Decl::Root => "root",
            Decl::Same => "sameNs",
            Decl::Ancestor => "ancestorNs",
            Decl::AncestorOpened => "ancestorNsOpened",
            Decl::AncestorAndRoot => "ancestorNsAndRoot",
            Decl::Sibling => "siblingNs",
            Decl::Opened => "opened",
            Decl::EnclosingModule => "enclosingModule",
        }
    }

    /// The namespaces declaring the cell's names, outside the use's block.
    fn namespaces(self, i: usize) -> Vec<String> {
        match self {
            Decl::Root => vec!["global".to_string()],
            Decl::Same => vec![format!("A{i}.B")],
            Decl::Ancestor | Decl::AncestorOpened => vec![format!("A{i}")],
            Decl::AncestorAndRoot => vec![format!("A{i}"), "global".to_string()],
            Decl::Sibling => vec![format!("A{i}.Sib")],
            Decl::Opened => vec![format!("O{i}")],
            Decl::EnclosingModule => vec![],
        }
    }

    /// The `open` the use's module writes first, if any.
    fn open(self, i: usize) -> Option<String> {
        match self {
            Decl::AncestorOpened => Some(format!("open A{i}")),
            Decl::Opened => Some(format!("open O{i}")),
            _ => None,
        }
    }
}

/// Which file holds the declarations outside the use's block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Placement {
    /// The earlier file.
    EarlierFile,
    /// A block of the use's file before the use's block.
    EarlierBlock,
}

impl Placement {
    fn tag(self) -> &'static str {
        match self {
            Placement::EarlierFile => "earlierFile",
            Placement::EarlierBlock => "earlierBlock",
        }
    }
}

/// Where the use sits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UseSite {
    /// `namespace A{i}.B`, then `module P`.
    InNamespace,
    /// `namespace A{i}.B`, then `module Outer = module P`.
    Nested,
    /// `module A{i}.B.Top` in a file of its own, then `module P`.
    UnderTop,
}

impl UseSite {
    const ALL: [UseSite; 3] = [UseSite::InNamespace, UseSite::Nested, UseSite::UnderTop];

    fn tag(self) -> &'static str {
        match self {
            UseSite::InNamespace => "nsModule",
            UseSite::Nested => "nestedModule",
            UseSite::UnderTop => "topModule",
        }
    }

    /// The placements available: a top-level module's file holds no other
    /// block.
    fn placements(self) -> &'static [Placement] {
        match self {
            UseSite::UnderTop => &[Placement::EarlierFile],
            _ => &[Placement::EarlierFile, Placement::EarlierBlock],
        }
    }
}

/// The cell's declarations, at indentation `ind`.
fn decls(f: &mut FileBuilder, i: usize, ind: &str) {
    for l in [
        format!("type U{i} ="),
        format!("    | K{i}"),
        format!("    | Other{i}"),
        format!("module M{i} ="),
        format!("    let v{i} = 1"),
        format!("module Al{i} = M{i}"),
        format!("exception E{i} of int"),
    ] {
        f.line(&format!("{ind}{l}"));
    }
}

/// The cell's declarations in a block of each of `namespaces`.
fn blocks(f: &mut FileBuilder, i: usize, namespaces: &[String]) {
    for ns in namespaces {
        f.line(&format!("namespace {ns}"));
        f.line("");
        decls(f, i, "");
    }
}

/// The uses, at indentation `ind`, after `open`.
fn probes(
    f: &mut FileBuilder,
    sites: &mut Vec<Site>,
    i: usize,
    ind: &str,
    open: Option<String>,
    label: &str,
) {
    if let Some(open) = open {
        f.line(&format!("{ind}{open}"));
    }
    let case = format!("U{i}.K{i}");
    f.probe(
        &format!("{ind}let e = {case}"),
        &case,
        format!("{label}/caseExpr"),
        sites,
    );
    f.probe(
        &format!("{ind}let p = match Unchecked.defaultof<_> with {case} -> 0 | _ -> 1"),
        &case,
        format!("{label}/casePattern"),
        sites,
    );
    f.probe(
        &format!("{ind}let b = K{i}"),
        &format!("K{i}"),
        format!("{label}/bareCase"),
        sites,
    );
    f.probe(
        &format!("{ind}let a (q: U{i}) = q"),
        &format!("U{i}"),
        format!("{label}/typeName"),
        sites,
    );
    let value = format!("M{i}.v{i}");
    f.probe(
        &format!("{ind}let m = {value}"),
        &value,
        format!("{label}/moduleValue"),
        sites,
    );
    f.probe(
        &format!("{ind}let ex = E{i} 1"),
        &format!("E{i}"),
        format!("{label}/exception"),
        sites,
    );
    let alias = format!("Al{i}.v{i}");
    f.probe(
        &format!("{ind}let al = {alias}"),
        &alias,
        format!("{label}/declaredAlias"),
        sites,
    );
    f.line(&format!("{ind}module X{i} = M{i}"));
    let local = format!("X{i}.v{i}");
    f.probe(
        &format!("{ind}let x = {local}"),
        &local,
        format!("{label}/localAlias"),
        sites,
    );
    f.line(&format!("{ind}open M{i}"));
    f.probe(
        &format!("{ind}let o = v{i}"),
        &format!("v{i}"),
        format!("{label}/openedModule"),
        sites,
    );
}

/// One cell: `earlier` takes declarations an earlier file holds, `main`
/// the use's block (and declarations an earlier block holds), and a
/// top-level module's use gets a file of its own, pushed onto `tops`.
#[allow(clippy::too_many_arguments)]
fn cell(
    i: usize,
    decl: Decl,
    placement: Placement,
    site: UseSite,
    earlier: &mut FileBuilder,
    main: &mut FileBuilder,
    tops: &mut Vec<FileBuilder>,
    sites: &mut Vec<Site>,
    next_index: &mut usize,
) {
    let label = if decl == Decl::EnclosingModule {
        format!("{}/{}", site.tag(), decl.tag())
    } else {
        format!("{}/{}/{}", site.tag(), decl.tag(), placement.tag())
    };
    let namespaces = decl.namespaces(i);
    match placement {
        Placement::EarlierFile => blocks(earlier, i, &namespaces),
        Placement::EarlierBlock => blocks(main, i, &namespaces),
    }
    let enclosing = decl == Decl::EnclosingModule;
    match site {
        UseSite::InNamespace => {
            main.line(&format!("namespace A{i}.B"));
            main.line("");
            main.line("module P =");
            if enclosing {
                decls(main, i, "    ");
            }
            probes(main, sites, i, "    ", decl.open(i), &label);
        }
        UseSite::Nested => {
            main.line(&format!("namespace A{i}.B"));
            main.line("");
            main.line("module Outer =");
            if enclosing {
                decls(main, i, "    ");
            }
            main.line("    module P =");
            probes(main, sites, i, "        ", decl.open(i), &label);
        }
        UseSite::UnderTop => {
            let mut f = FileBuilder::new(*next_index);
            *next_index += 1;
            f.line(&format!("module A{i}.B.Top"));
            f.line("");
            if enclosing {
                decls(&mut f, i, "");
            }
            f.line("module P =");
            probes(&mut f, sites, i, "    ", decl.open(i), &label);
            tops.push(f);
        }
    }
}

/// The uses FCS resolves that the walk declines, at every use site, as
/// `{decl}/{placement}/{use}`: an earlier block's root or opened declarations
/// (which only the lexical walk of the current block reaches), a type name
/// or bare case brought by an `open` or the root, and the root's namesake of
/// an ancestor's declaration. Every other use FCS resolves must commit, so
/// the grid cannot pass by declining; a gap that starts to commit FCS's
/// answer must leave the list.
const DECLINED: &[&str] = &[
    "root/earlierFile/bareCase",
    "root/earlierFile/typeName",
    "root/earlierBlock/caseExpr",
    "root/earlierBlock/casePattern",
    "root/earlierBlock/bareCase",
    "root/earlierBlock/typeName",
    "root/earlierBlock/exception",
    "ancestorNsOpened/earlierFile/typeName",
    "ancestorNsOpened/earlierBlock/caseExpr",
    "ancestorNsOpened/earlierBlock/casePattern",
    "ancestorNsOpened/earlierBlock/typeName",
    "ancestorNsAndRoot/earlierFile/bareCase",
    "ancestorNsAndRoot/earlierFile/typeName",
    "ancestorNsAndRoot/earlierBlock/caseExpr",
    "ancestorNsAndRoot/earlierBlock/casePattern",
    "ancestorNsAndRoot/earlierBlock/bareCase",
    "ancestorNsAndRoot/earlierBlock/typeName",
    "ancestorNsAndRoot/earlierBlock/exception",
    "ancestorNsAndRoot/earlierBlock/declaredAlias",
    "opened/earlierFile/typeName",
    "opened/earlierBlock/caseExpr",
    "opened/earlierBlock/casePattern",
    "opened/earlierBlock/typeName",
];

/// Whether `label` is one of [`DECLINED`], at whichever use site.
fn pinned_decline(label: &str) -> bool {
    label
        .split_once('/')
        .is_some_and(|(_, rest)| DECLINED.contains(&rest))
}

#[test]
fn ancestor_namespace_visibility_agrees_with_fcs() {
    let mut earlier = FileBuilder::new(0);
    let mut main = FileBuilder::new(1);
    let mut tops = Vec::new();
    let mut sites = Vec::new();
    let mut next_index = 2;
    let mut i = 0;
    for site in UseSite::ALL {
        for decl in Decl::ALL {
            let placements: &[Placement] = if decl == Decl::EnclosingModule {
                &[Placement::EarlierFile]
            } else {
                site.placements()
            };
            for &placement in placements {
                cell(
                    i,
                    decl,
                    placement,
                    site,
                    &mut earlier,
                    &mut main,
                    &mut tops,
                    &mut sites,
                    &mut next_index,
                );
                i += 1;
            }
        }
    }
    let mut files = vec![("earlier.fs", earlier.text), ("main.fs", main.text)];
    let names: Vec<String> = (0..tops.len()).map(|k| format!("top{k}.fs")).collect();
    files.extend(
        names
            .iter()
            .map(String::as_str)
            .zip(tops.into_iter().map(|f| f.text)),
    );
    let graded = grade("ang", &files, &sites);
    let count = |p: &dyn Fn(&Graded) -> bool| graded.iter().filter(|g| p(g)).count();
    assert!(count(&|g| matches!(g.fcs, FcsVerdict::Resolved(..))) > 0);
    assert!(count(&|g| matches!(g.fcs, FcsVerdict::Rejected)) > 0);
    let must: Vec<&str> = graded
        .iter()
        .filter(|g| matches!(g.fcs, FcsVerdict::Resolved(..)) && !pinned_decline(&g.label))
        .map(|g| g.label.as_str())
        .collect();
    assert_sound_and_live("ancestor namespace", &graded, &[], &must);
    let committed: Vec<&str> = graded
        .iter()
        .filter(|g| pinned_decline(&g.label) && agrees(g))
        .map(|g| g.label.as_str())
        .collect();
    assert!(
        committed.is_empty(),
        "uses pinned as declined now commit FCS's answer; remove them from DECLINED:\n{committed:#?}"
    );
    let unused: Vec<&&str> = DECLINED
        .iter()
        .filter(|d| {
            !graded
                .iter()
                .any(|g| g.label.split_once('/').is_some_and(|(_, r)| r == **d))
        })
        .collect();
    assert!(
        unused.is_empty(),
        "DECLINED names no use of the grid: {unused:#?}"
    );
}
