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

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange};
use borzoi_sema::test_support::binder_completeness::{BinderVerdict, binder_verdict};
use borzoi_sema::{AssemblyEnv, ProjectItems, Resolution, SyntaxRecovery, resolve_file};

use crate::common::{
    census_oracle_binders, census_oracle_uses, invoke_fcs_dump_census, parse_census_jsonl,
    temp_fs_file,
};

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
