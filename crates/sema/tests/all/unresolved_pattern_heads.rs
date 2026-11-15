//! Binders under an applied pattern whose head FCS cannot resolve, graded
//! against FCS.
//!
//! FCS treats the two spellings of such a head differently
//! (`CheckPatterns.fs`, `TcPatLongIdent`):
//!
//! - a **single-segment** head it cannot resolve is a new definition
//!   (`TcPatLongIdentNewDef`): it reports FS0039 and still binds the
//!   arguments, so `| Foo x -> x` binds `x`;
//! - a **qualified** head it cannot resolve is an error that abandons the
//!   sub-pattern, so nothing under it binds: `| Q.R(x) as y -> …` binds `y`
//!   alone, and a use of `x` reaches whatever encloses the clause.
//!
//! The walk cannot tell a qualified head it declines from one that does not
//! exist, so the binders under it are opaque: never interned, and every use of
//! their names declines. These cells are type-check errors by construction, so
//! they cannot be rows of `binder_site_grid`, which requires FCS to accept a
//! cell; its `*_abbreviation_qualified_case_field` rows are the accepted
//! counterpart, a qualified head FCS resolves and the walk declines.
//!
//! A module value a deconstruction exports (`let (Q.R x) = …`) is the one
//! exception, interned as before ([`Expect::ExportedGap`]).
//!
//! A qualified head the walk declines only because it cannot tell which of
//! several same-named types FCS binds it to still binds its arguments when
//! every other type of that name in scope finds nothing of the case's name:
//! FCS then resolves it to the union case, whichever order it tries them
//! in. [`NAMESAKE_CELLS`] grade that against FCS, with namesakes that do
//! find something.

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange};
use borzoi_sema::test_support::binder_completeness::{BinderVerdict, binder_verdict};
use std::path::Path;

use borzoi_sema::{
    AssemblyEnv, ProjectItems, Resolution, SyntaxRecovery, resolve_file, resolve_project_files,
};

use crate::common::{
    census_oracle_binders, census_oracle_uses, full_bcl_env, invoke_fcs_dump_census,
    invoke_fcs_dump_project_with_refs, parse_census_jsonl, parse_fcs_uses_project,
    project_oracle_binders, temp_fs_file, temp_fs_tree, unmodelled_project_binder_failures,
};
use crate::resolve_signatures::project;

/// What FCS and the walk do at a marked binder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expect {
    /// FCS binds the name here; the walk interns it.
    Interned,
    /// FCS binds the name here; the walk declines it.
    Opaque,
    /// FCS binds nothing here; the walk declines it.
    Abandoned,
    /// FCS binds nothing here, but the walk interns it: a module value the
    /// deconstruction exports, which the walk cannot decline through every
    /// `open` of its module (see `prepare_binding`). FCS binds it whenever the
    /// head resolves, so the gap is confined to code that does not compile.
    ExportedGap,
}

/// A program with its binders marked `«n»` and its uses marked `‹n›`. Each
/// binder's [`Expect`] is listed in source order.
struct Cell {
    id: &'static str,
    template: &'static str,
    binders: &'static [Expect],
    /// Every planted use must commit to what FCS declares, rather than only
    /// not commit to anything else.
    uses_commit: bool,
}

/// The decoy every cell starts with: a module-level `x` and `e`, which a use
/// reaches when the clause binds no name of its own.
const PRELUDE: &str = "module M\nlet x = \"outer\"\nlet e = \"outer\"\n";

const CELLS: &[Cell] = &[
    Cell {
        id: "single_segment_head",
        template: "let f v =\n    match v with\n    | Foo «x» -> ignore ‹x›\n    | _ -> ()\n",
        binders: &[Expect::Interned],
        uses_commit: false,
    },
    Cell {
        id: "single_segment_param_head",
        template: "let f (Foo(«x», _)) = ignore ‹x›\n",
        binders: &[Expect::Interned],
        uses_commit: false,
    },
    Cell {
        id: "qualified_head",
        template: "let f v =\n    match v with\n    | Q.R(«x») as «y» -> ignore ‹y›; ignore ‹x›\n    | _ -> ()\n",
        binders: &[Expect::Abandoned, Expect::Interned],
        uses_commit: false,
    },
    Cell {
        id: "qualified_head_under_a_case",
        template: "let f v =\n    match v with\n    | Some (Q.Inner «x») -> ignore ‹x›\n    | _ -> ()\n",
        binders: &[Expect::Abandoned],
        uses_commit: false,
    },
    Cell {
        // The outer head marks the whole subtree; the inner one leans on it.
        id: "qualified_head_under_a_qualified_head",
        template: "let f v =\n    match v with\n    | Q.R (Q.S «x», «e») -> ignore ‹x›; ignore ‹e›\n    | _ -> ()\n",
        binders: &[Expect::Abandoned, Expect::Abandoned],
        uses_commit: false,
    },
    Cell {
        // A nullary case name under the head binds nothing whichever way the
        // head goes, so it hides nothing: the clause's own use of the case
        // still resolves.
        id: "case_name_under_a_qualified_head",
        template: "type U = A | B\nlet f v =\n    match v with\n    | Q.R(A) -> ignore ‹A›\n    | _ -> ()\n",
        binders: &[],
        uses_commit: true,
    },
    Cell {
        id: "qualified_head_named_fields",
        template: "let f v =\n    match v with\n    | Q.R(field = «x») -> ignore ‹x›\n    | _ -> ()\n",
        binders: &[Expect::Abandoned],
        uses_commit: false,
    },
    Cell {
        id: "qualified_param_head",
        template: "let f (Q.R «x») = ignore ‹x›\n",
        binders: &[Expect::Abandoned],
        uses_commit: false,
    },
    Cell {
        id: "qualified_local_let_head",
        template: "let f v =\n    let (Q.R «x») = v\n    ignore ‹x›\n",
        binders: &[Expect::Abandoned],
        uses_commit: false,
    },
    Cell {
        // FCS binds nothing, so its use of `x` is the decoy's; the walk
        // commits the exported value (and its use) instead.
        id: "qualified_module_let_head",
        template: "module Inner =\n    let (Q.R «x») = 1\n    do ignore x\n",
        binders: &[Expect::ExportedGap],
        uses_commit: false,
    },
    Cell {
        // `Tests.Watson.fs`: the first alternative's `e` sits under a head FCS
        // cannot resolve, so FCS binds the name at the second alternative.
        id: "or_pattern_first_alternative_abandoned",
        template: "let f v =\n    match v with\n    | Q.Wrap (Some (Q.Inner (m, r) as «e»))\n    | (Q.Inner (m, r) as «e») -> ignore ‹e›\n    | _ -> ()\n",
        binders: &[Expect::Abandoned, Expect::Opaque],
        uses_commit: false,
    },
];

/// `template` after [`PRELUDE`], with its markers removed, the marked binder
/// ranges and the marked use ranges.
fn materialise(template: &str) -> (String, Vec<TextRange>, Vec<TextRange>) {
    let mut src = PRELUDE.to_string();
    let (mut binders, mut uses) = (Vec::new(), Vec::new());
    let mut open: Option<(char, usize)> = None;
    for c in template.chars() {
        match c {
            '«' | '‹' => open = Some((c, src.len())),
            '»' | '›' => {
                let (kind, start) = open.take().expect("balanced markers");
                let range = TextRange::new((start as u32).into(), (src.len() as u32).into());
                if kind == '«' {
                    binders.push(range);
                } else {
                    uses.push(range);
                }
            }
            c => src.push(c),
        }
    }
    (src, binders, uses)
}

#[test]
fn binders_under_an_unresolved_head_follow_fcs() {
    let cells: Vec<_> = CELLS.iter().map(|c| (c, materialise(c.template))).collect();
    let paths: Vec<_> = cells
        .iter()
        .map(|(c, (src, ..))| temp_fs_file(&format!("unresolved_head_{}", c.id), src))
        .collect();
    let census = parse_census_jsonl(&invoke_fcs_dump_census(&paths));
    for p in &paths {
        let _ = std::fs::remove_file(p);
    }
    assert_eq!(census.len(), cells.len(), "one census line per cell");
    let env = AssemblyEnv::default();

    let mut failures = Vec::new();
    for ((cell, (src, binders, uses)), file) in cells.iter().zip(&census) {
        assert_eq!(
            binders.len(),
            cell.binders.len(),
            "{}: one Expect per binder",
            cell.id
        );
        assert!(file.ok, "{}: FCS failed on the cell", cell.id);
        let oracle_binders = census_oracle_binders(file, src);
        let oracle_uses = census_oracle_uses(file, src);

        let parsed = parse(src);
        assert!(parsed.errors.is_empty(), "{}: {:?}", cell.id, parsed.errors);
        let recovery = SyntaxRecovery::of(&parsed);
        let impl_file = ImplFile::cast(parsed.root).expect("impl file");
        let rf = resolve_file(&impl_file, &ProjectItems::default(), &env, &recovery);

        for (&range, &expect) in binders.iter().zip(cell.binders) {
            let oracle = oracle_binders
                .iter()
                .find(|b| b.range == range && b.introduces_a_name());
            match (expect, oracle) {
                (Expect::ExportedGap, Some(_)) => failures.push(format!(
                    "{}: FCS binds {range:?}, which the cell says it abandons",
                    cell.id
                )),
                (Expect::ExportedGap, None) => {
                    if !rf.defs().any(|d| d.range == range) {
                        failures.push(format!(
                            "{}: the exported value {range:?} is no longer interned",
                            cell.id
                        ));
                    }
                }
                (Expect::Abandoned, Some(_)) => failures.push(format!(
                    "{}: FCS binds {range:?}, which the cell says it abandons",
                    cell.id
                )),
                (Expect::Abandoned, None) => {
                    let interned = rf.defs().any(|d| d.range == range);
                    if interned || !rf.opaque_binders().contains(&range) {
                        failures.push(format!(
                            "{}: {range:?} is under an unresolved qualified head, but the walk {}",
                            cell.id,
                            if interned {
                                "interns it"
                            } else {
                                "does not record it as opaque"
                            }
                        ));
                    }
                }
                (_, None) => failures.push(format!(
                    "{}: FCS does not bind {range:?}, which the cell says it does",
                    cell.id
                )),
                (Expect::Interned | Expect::Opaque, Some(oracle)) => {
                    let want = if expect == Expect::Interned {
                        BinderVerdict::Interned
                    } else {
                        BinderVerdict::Opaque
                    };
                    let got = binder_verdict(&rf, oracle);
                    if got != want {
                        failures.push(format!(
                            "{}: {range:?} pinned {want:?}, observed {got:?}",
                            cell.id
                        ));
                    }
                }
            }
        }
        // No commit at a planted use but to what FCS declares.
        for &u in uses {
            let oracle_decl = oracle_uses
                .iter()
                .find(|o| o.range == u)
                .and_then(|o| o.decl);
            match rf.resolution_at(u) {
                None | Some(Resolution::Deferred(_)) if !cell.uses_commit => {}
                None | Some(Resolution::Deferred(_)) => failures.push(format!(
                    "{}: the use at {u:?} declines; FCS declares it at {oracle_decl:?}",
                    cell.id
                )),
                Some(res) if rf.resolved_def(res).map(|d| d.range) == oracle_decl => {}
                Some(res) => failures.push(format!(
                    "{}: the use at {u:?} commits to {res:?}; FCS declares it at {oracle_decl:?}",
                    cell.id
                )),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// An earlier file's unions whose names a referenced assembly's type also
/// bears, at a lower arity, in a namespace the cells open: the walk's
/// namesake guard declines each case head (`QualifierArityNamesake`), since
/// which type FCS binds is undecided.
const NAMESAKE_UNIONS: &str = "namespace N\n\
type MethodBody<'a> =\n    | Il of body: 'a\n    | Jit of 'a\n    | Abstract\n\
type String<'a> =\n    | Empty of 'a\n    | Length of 'a\n\
type Int32<'a> =\n    | MaxValue of 'a\n    | NotMax\n\
type Environment<'a> =\n    | SpecialFolder of 'a\n    | NotFolder\n";

/// The start of a use file over [`NAMESAKE_UNIONS`]: the namesakes'
/// namespaces opened, and a module-level `x` a use reaches when its clause
/// binds none.
const NAMESAKE_PRELUDE: &str =
    "namespace N\nopen System\nopen System.Reflection\nmodule M =\n    let x = \"outer\"\n";

/// The project types of [`project_namesake_cell`]: a union, and a record of
/// its name with a field of its case's name.
const PROJECT_NAMESAKES: &[(&str, &str)] = &[
    (
        "NamesakeA.fs",
        "namespace N2\ntype T<'a> =\n    | C of 'a\n    | D\n",
    ),
    ("NamesakeB.fs", "namespace N1\ntype T = { C: int }\n"),
];

/// A multi-file cell: the earlier files, then the use file — its prelude,
/// and its program marked as in [`Cell`] with one binder — and that
/// binder's [`Expect`].
struct ProjectCell {
    id: &'static str,
    earlier: &'static [(&'static str, &'static str)],
    prelude: &'static str,
    template: &'static str,
    binder: Expect,
}

/// A [`ProjectCell`] over [`NAMESAKE_UNIONS`].
const fn namesake_union_cell(
    id: &'static str,
    template: &'static str,
    binder: Expect,
) -> ProjectCell {
    ProjectCell {
        id,
        earlier: &[("NamesakeUnions.fs", NAMESAKE_UNIONS)],
        prelude: NAMESAKE_PRELUDE,
        template,
        binder,
    }
}

/// Qualified case heads the namesake guard declines. Whether FCS binds the
/// arguments turns on what the *first* type of the head's name it tries
/// finds in itself, not on which case it is: any union case binds them,
/// whatever its field count, and anything else the lookup finds abandons
/// the sub-pattern. So the walk commits the binders when no type of the name
/// but the found union could find anything of the case's name, and declines
/// them otherwise. The `Abandoned` cells are namesakes that do find
/// something; each would fail under a rule that committed the binders
/// whenever the guard had found a case reading.
const NAMESAKE_CELLS: &[ProjectCell] = &[
    namesake_union_cell(
        "assembly_namesake_lacks_the_case_name",
        "    let f (b: MethodBody<int>) =\n        match b with\n        | MethodBody.Il «x» -> ‹x›\n        | _ -> 0\n",
        Expect::Interned,
    ),
    namesake_union_cell(
        // FS0725, and the argument binds regardless.
        "nullary_case",
        "    let f (b: MethodBody<int>) =\n        match b with\n        | MethodBody.Abstract «x» -> ‹x›\n        | _ -> 0\n",
        Expect::Interned,
    ),
    namesake_union_cell(
        "named_field",
        "    let f (b: MethodBody<int>) =\n        match b with\n        | MethodBody.Il (body = «x») -> ‹x›\n        | _ -> 0\n",
        Expect::Interned,
    ),
    namesake_union_cell(
        "parameter",
        "    let f (MethodBody.Il «x») = ‹x›\n",
        Expect::Interned,
    ),
    namesake_union_cell(
        // The second alternative's `x` is a use of the first's.
        "or_pattern",
        "    let f (b: MethodBody<int>) =\n        match b with\n        | MethodBody.Il «x»\n        | MethodBody.Jit ‹x› -> ‹x›\n        | _ -> 0\n",
        Expect::Interned,
    ),
    namesake_union_cell(
        // `System.String` is tried first and finds its field `Empty`, which
        // is no literal: FS0729.
        "assembly_namesake_field",
        "    let f (b: String<int>) =\n        match b with\n        | String.Empty «x» -> ignore ‹x›\n        | _ -> ()\n",
        Expect::Abandoned,
    ),
    namesake_union_cell(
        // A literal field abandons it too: FS3191, then a type mismatch.
        "assembly_namesake_literal_field",
        "    let f (b: Int32<int>) =\n        match b with\n        | Int32.MaxValue «x» -> ignore ‹x›\n        | _ -> ()\n",
        Expect::Abandoned,
    ),
    namesake_union_cell(
        // `System.Environment.SpecialFolder`, a nested type: FS0730.
        "assembly_namesake_nested_type",
        "    let f (b: Environment<int>) =\n        match b with\n        | Environment.SpecialFolder «x» -> ignore ‹x›\n        | _ -> ()\n",
        Expect::Abandoned,
    ),
    namesake_union_cell(
        // A property finds nothing in pattern position, so FCS reaches the
        // union and binds `x`; the walk's rule is name-only and declines it.
        "assembly_namesake_property",
        "    let f (b: String<int>) =\n        match b with\n        | String.Length «x» -> ‹x›\n        | _ -> 0\n",
        Expect::Opaque,
    ),
    ProjectCell {
        // The record's namespace is opened later, so FCS tries it first:
        // FS0728, FS0729.
        id: "project_namesake_record_field",
        earlier: PROJECT_NAMESAKES,
        prelude: "module P\nopen N2\nopen N1\nlet x = \"outer\"\n",
        template: "let f (b: N2.T<int>) =\n    match b with\n    | T.C «x» -> ignore ‹x›\n    | _ -> ()\n",
        binder: Expect::Abandoned,
    },
    ProjectCell {
        // Opened the other way round, FCS tries the union first and binds
        // `x`: it orders a pattern head's namesakes latest first, not by
        // arity. The walk declines a head another project type may take.
        id: "project_namesake_record_field_opened_first",
        earlier: PROJECT_NAMESAKES,
        prelude: "module P\nopen N1\nopen N2\nlet x = \"outer\"\n",
        template: "let f (b: N2.T<int>) =\n    match b with\n    | T.C «x» -> ‹x›\n    | _ -> 0\n",
        binder: Expect::Opaque,
    },
    ProjectCell {
        // A record of the union's name and path, at another arity, is
        // another type: FCS tries it first.
        id: "project_namesake_record_field_at_the_same_path",
        earlier: &[
            (
                "NamesakeA.fs",
                "namespace N\ntype T<'a> =\n    | C of 'a\n    | D\n",
            ),
            ("NamesakeB.fs", "namespace N\ntype T = { C: int }\n"),
        ],
        prelude: "module P\nopen N\nlet x = \"outer\"\n",
        template: "let f (b: N.T<int>) =\n    match b with\n    | T.C «x» -> ignore ‹x›\n    | _ -> ()\n",
        binder: Expect::Abandoned,
    },
    ProjectCell {
        // The union is this file's, so the guard declines it in-file.
        id: "in_file_union_assembly_namesake_lacks_the_case_name",
        earlier: &[],
        prelude: "module P\nopen System.Reflection\ntype MethodBody<'a> =\n    | Il of 'a\n    | Jit of 'a\nlet x = \"outer\"\n",
        template: "let f (b: MethodBody<int>) =\n    match b with\n    | MethodBody.Il «x» -> ‹x›\n    | _ -> 0\n",
        binder: Expect::Interned,
    },
    ProjectCell {
        // `System` is opened after the union, so FCS tries `System.String`
        // first: FS0729.
        id: "in_file_union_assembly_namesake_field_opened_later",
        earlier: &[],
        prelude: "module P\ntype String<'a> =\n    | Empty of 'a\n    | Length of 'a\nopen System\nlet x = \"outer\"\n",
        template: "let f (b: String<int>) =\n    match b with\n    | String.Empty «x» -> ignore ‹x›\n    | _ -> ()\n",
        binder: Expect::Abandoned,
    },
    ProjectCell {
        // Opened before it, FCS tries the union first and binds `x`; the
        // walk declines, as `System.String` finds `Empty`.
        id: "in_file_union_assembly_namesake_field_opened_first",
        earlier: &[],
        prelude: "module P\nopen System\ntype String<'a> =\n    | Empty of 'a\n    | Length of 'a\nlet x = \"outer\"\n",
        template: "let f (b: String<int>) =\n    match b with\n    | String.Empty «x» -> ‹x›\n    | _ -> 0\n",
        binder: Expect::Opaque,
    },
    ProjectCell {
        id: "in_file_namesake_record_field",
        earlier: &[PROJECT_NAMESAKES[0]],
        prelude: "module P\nopen N2\ntype T = { C: int }\nlet x = \"outer\"\n",
        template: "let f (b: N2.T<int>) =\n    match b with\n    | T.C «x» -> ignore ‹x›\n    | _ -> ()\n",
        binder: Expect::Abandoned,
    },
];

fn range_of(start: usize, end: usize) -> TextRange {
    TextRange::new(
        u32::try_from(start).unwrap().into(),
        u32::try_from(end).unwrap().into(),
    )
}

/// What [`check_project_cell`] observed of a cell's binder.
struct Observed {
    fcs_binds: bool,
    walk_interns: bool,
}

/// Check one multi-file cell against `uses-project`, under the reference
/// assemblies: FCS checks against the BCL, which holds the assembly
/// namesakes, so an environment without them would answer another question.
///
/// `expect` pins the binder; `None` only holds the walk to
/// certain-implies-exact: it interns the binder only where FCS binds it, and
/// commits no use to anything but what FCS declares. Binder completeness
/// holds either way.
fn check_project_cell(
    id: &str,
    earlier: &[(&str, &str)],
    prelude: &str,
    template: &str,
    expect: Option<Expect>,
    failures: &mut Vec<String>,
) -> Observed {
    let (src, binders, uses) = materialise(template);
    let src = format!("{prelude}{}", &src[PRELUDE.len()..]);
    let shift = |r: &TextRange| {
        let at = |o: borzoi_cst::syntax::TextSize| usize::from(o) - PRELUDE.len() + prelude.len();
        range_of(at(r.start()), at(r.end()))
    };
    let [binder] = binders.iter().map(shift).collect::<Vec<_>>()[..] else {
        panic!("{id}: one binder per cell");
    };
    let uses: Vec<TextRange> = uses.iter().map(shift).collect();
    let mut files: Vec<(&str, &str)> = earlier.to_vec();
    files.push(("NamesakeUse.fs", &src));
    let (root, written) = temp_fs_tree(&format!("namesake_head_{id}"), &files);
    let paths: Vec<&Path> = written.iter().map(|(p, _)| p.as_path()).collect();
    let fcs = parse_fcs_uses_project(&invoke_fcs_dump_project_with_refs(&paths, &[]), &written);
    let _ = std::fs::remove_dir_all(&root);
    let last = written.len() - 1;
    let use_file = written[last].0.file_name();
    let file = fcs
        .iter()
        .find(|f| f.path.file_name() == use_file)
        .expect("the use file's uses");
    let proj = resolve_project_files(&project(&files), full_bcl_env());
    let rf = proj.file(last);

    let oracle_binders = project_oracle_binders(file);
    let oracle = oracle_binders
        .iter()
        .find(|b| b.range == binder && b.introduces_a_name());
    let walk_interns = rf.defs().any(|d| d.range == binder);
    match (expect, oracle) {
        (None, None) if walk_interns => failures.push(format!(
            "{id}: FCS abandons {binder:?}, but the walk interns it"
        )),
        (None, _) => {}
        (Some(Expect::Abandoned), Some(_)) => failures.push(format!(
            "{id}: FCS binds {binder:?}, which the cell says it abandons"
        )),
        (Some(Expect::Abandoned), None) => {
            if walk_interns || !rf.opaque_binders().contains(&binder) {
                failures.push(format!(
                    "{id}: FCS abandons {binder:?}, but the walk does not decline it"
                ));
            }
        }
        (Some(_), None) => failures.push(format!(
            "{id}: FCS does not bind {binder:?}, which the cell says it does"
        )),
        (Some(expect), Some(oracle)) => {
            let want = if expect == Expect::Interned {
                BinderVerdict::Interned
            } else {
                BinderVerdict::Opaque
            };
            let got = binder_verdict(rf, oracle);
            if got != want {
                failures.push(format!(
                    "{id}: {binder:?} pinned {want:?}, observed {got:?}"
                ));
            }
        }
    }
    // An interned binder's uses commit to it; no use commits to anything but
    // what FCS declares.
    for &u in &uses {
        let oracle_decl = file
            .uses
            .iter()
            .find(|o| range_of(o.start, o.end) == u)
            .and_then(|o| o.decl.as_ref())
            .filter(|d| d.file.file_name() == use_file)
            .map(|d| range_of(d.start, d.end));
        match rf.resolution_at(u) {
            None | Some(Resolution::Deferred(_)) if !walk_interns => {}
            Some(res)
                if oracle_decl.is_some()
                    && rf.resolved_def(res).map(|d| d.range) == oracle_decl => {}
            other => failures.push(format!(
                "{id}: the use at {u:?} gives {other:?}; FCS declares it at {oracle_decl:?}"
            )),
        }
    }
    failures.extend(unmodelled_project_binder_failures(
        id, &proj, &written, &fcs,
    ));
    Observed {
        fcs_binds: oracle.is_some(),
        walk_interns,
    }
}

#[test]
fn binders_under_a_namesake_declined_head_follow_fcs() {
    let mut failures = Vec::new();
    for cell in NAMESAKE_CELLS {
        check_project_cell(
            cell.id,
            cell.earlier,
            cell.prelude,
            cell.template,
            Some(cell.binder),
            &mut failures,
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The union every [`NAMESAKE_GRID_COMPETITORS`] cell's head can read:
/// `N0.T<'a>`, owning `C`.
const GRID_UNION: (&str, &str) = (
    "GridUnion.fs",
    "namespace N0\ntype T<'a> =\n    | C of 'a\n    | D\n",
);

/// Another project declaration of the name `T`, each a different thing FCS's
/// lookup of `C` in it can find: nothing, a union case, a property, a record
/// or class field, an exception field, or (through an abbreviation) the
/// union itself. Each is declared in every [`Place`].
const NAMESAKE_GRID_COMPETITORS: &[(&str, &str)] = &[
    ("none", ""),
    ("record", "type T = { C: int }"),
    ("generic_record", "type T<'a, 'b> = { C: 'a }"),
    (
        "union_with_the_case",
        "type T<'a, 'b> =\n    | C of 'b\n    | E",
    ),
    (
        "union_without_the_case",
        "type T =\n    | E of int\n    | F",
    ),
    ("static_property", "type T =\n    static member C = 1"),
    (
        "static_field",
        "type T() =\n    [<DefaultValue>]\n    static val mutable private C: int",
    ),
    ("exception_field", "exception T of C: int"),
    ("abbreviation_of_the_union", "type T = N0.T<int>"),
];

/// Where a [`NAMESAKE_GRID_COMPETITORS`] declaration sits, relative to the
/// use file's `open N0`.
#[derive(Clone, Copy, Debug)]
enum Place {
    /// An earlier file's, in `N0` itself.
    EarlierSameNamespace,
    /// An earlier file's, in `N1`, opened after `N0`.
    EarlierOpenedAfter,
    /// An earlier file's, in `N1`, opened before `N0`.
    EarlierOpenedBefore,
    /// The use file's, in a module opened after `N0`.
    LocalOpenedAfter,
    /// The use file's, in a module opened before `N0`.
    LocalOpenedBefore,
}

/// Every [`NAMESAKE_GRID_COMPETITORS`] declaration in every [`Place`], held
/// to certain-implies-exact: the walk commits the binder under `T.C` only
/// where FCS binds it. Where FCS's answer turns on which type it tries
/// first, the walk must decline; the grid checks that it does without
/// naming the cells.
#[test]
fn binders_under_namesake_grid_heads_are_certain() {
    let mut failures = Vec::new();
    let (mut cells, mut fcs_binds, mut walk_interns) = (0, 0, 0);
    for &(competitor, decl) in NAMESAKE_GRID_COMPETITORS {
        let places: &[Place] = if decl.is_empty() {
            &[Place::EarlierSameNamespace]
        } else {
            &[
                Place::EarlierSameNamespace,
                Place::EarlierOpenedAfter,
                Place::EarlierOpenedBefore,
                Place::LocalOpenedAfter,
                Place::LocalOpenedBefore,
            ]
        };
        for &place in places {
            let id = format!("{competitor}_{place:?}");
            let namespace = match place {
                Place::EarlierOpenedAfter | Place::EarlierOpenedBefore => "N1",
                _ => "N0",
            };
            let competitor_file = format!("namespace {namespace}\n{decl}\n");
            let mut earlier = vec![GRID_UNION];
            let local = format!("module Local =\n{}\n", indent(decl));
            let opens = match place {
                Place::EarlierSameNamespace => "open N0\n".to_string(),
                Place::EarlierOpenedAfter => "open N0\nopen N1\n".to_string(),
                Place::EarlierOpenedBefore => "open N1\nopen N0\n".to_string(),
                Place::LocalOpenedAfter => format!("open N0\n{local}open Local\n"),
                Place::LocalOpenedBefore => format!("{local}open Local\nopen N0\n"),
            };
            if !decl.is_empty()
                && matches!(
                    place,
                    Place::EarlierSameNamespace
                        | Place::EarlierOpenedAfter
                        | Place::EarlierOpenedBefore
                )
            {
                earlier.push(("GridCompetitor.fs", competitor_file.as_str()));
            }
            let prelude = format!("module P\n{opens}let x = \"outer\"\n");
            let observed = check_project_cell(
                &id,
                &earlier,
                &prelude,
                "let f (b: N0.T<int>) =\n    match b with\n    | T.C «x» -> ignore ‹x›\n    | _ -> ()\n",
                None,
                &mut failures,
            );
            cells += 1;
            fcs_binds += usize::from(observed.fcs_binds);
            walk_interns += usize::from(observed.walk_interns);
        }
    }
    eprintln!(
        "namesake grid: {cells} cells, FCS binds {fcs_binds}, the walk interns {walk_interns}"
    );
    // Liveness: the rule commits somewhere, so certain-implies-exact is not
    // passing vacuously.
    assert!(walk_interns > 0, "the grid commits no binder");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `decl` indented one level, to sit in a module.
fn indent(decl: &str) -> String {
    decl.lines()
        .map(|l| format!("    {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}
