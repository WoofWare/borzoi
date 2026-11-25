//! `borzoi_sema::source_existence` held to FCS (Stage 1a of the
//! source-references plan).
//!
//! Each cell is a producer project A, described once as a [`GraphCell`]. FCS
//! reads A from source through the project-graph oracle's `referenced` op
//! (`common::referenced`, which holds the oracle to FCS's own view and to
//! the DLL FCS compiles). Ours is `source_existence` over A's files, parsed
//! from the same cell (`common::referenced::parse_cell`). The two are
//! compared in the currency every entity question reads: the facts of the
//! existence set built from each (`test_support::existence_facts`).
//!
//! The property, per cell: when ours is `Read` and FCS's reading is found,
//! every fact FCS's set holds, ours holds (**containment**). The verdict, with
//! ours's surplus or decline and FCS's errors, is pinned per cell.

use std::collections::BTreeSet;
use std::path::PathBuf;

use borzoi_assembly::existence::{ExistenceIndex, PickleLayer};
use borzoi_cst::syntax::{AstNode, ImplFile, SigFile};
use borzoi_oracle_harness::project_graph::{FixtureFile, GraphCell, PlainName, RefusalCause};
use borzoi_sema::test_support::{ExistenceFacts, existence_facts, surface_facts};
use borzoi_sema::{
    Budget, CompileItem, Producer, ProjectFile, ProviderReferences, SourceExistence, SourceFile,
    SyntaxRecovery, qualified_names, source_existence,
};

use crate::common::referenced::{Reading, Unknown, View, parse_cell, read};

/// One producer, and what the walk is told of its references.
#[derive(Clone)]
pub struct Cell {
    pub name: String,
    pub graph: GraphCell,
    pub providers: ProviderReferences,
}

impl Cell {
    /// A library of `files` (name and text, in Compile order).
    pub fn new(name: impl Into<String>, files: &[(&str, &str)]) -> Self {
        Cell {
            name: name.into(),
            graph: GraphCell::library(
                PlainName::new("Producer").expect("a plain name"),
                files
                    .iter()
                    .map(|(n, t)| FixtureFile {
                        name: (*n).to_owned(),
                        text: (*t).to_owned(),
                    })
                    .collect(),
            ),
            providers: ProviderReferences::None,
        }
    }
}

/// `cell`'s files as Compile items, parsed as FCS's check parses them.
pub fn project_files(cell: &Cell) -> Vec<ProjectFile> {
    let parses = parse_cell(&cell.graph);
    let mut files = Vec::new();
    let mut recoveries = Vec::new();
    for (f, parse) in cell.graph.files.iter().zip(parses) {
        recoveries.push(SyntaxRecovery::of(&parse));
        files.push(if f.name.ends_with(".fsi") {
            SourceFile::Sig(SigFile::cast(parse.root).expect("a signature root"))
        } else {
            SourceFile::Impl(ImplFile::cast(parse.root).expect("an implementation root"))
        });
    }
    let paths: Vec<PathBuf> = cell
        .graph
        .files
        .iter()
        .map(|f| PathBuf::from("/fixture").join(&f.name))
        .collect();
    files
        .iter()
        .cloned()
        .zip(recoveries)
        .zip(qualified_names(&files, &paths))
        .map(|((f, r), q)| ProjectFile::new(f, q, r))
        .collect()
}

/// Our reading of `cell` under `budget`.
pub fn ours_under(cell: &Cell, budget: Budget) -> SourceExistence {
    let project = project_files(cell);
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    source_existence(
        Producer {
            items: &items,
            providers: cell.providers,
        },
        budget,
    )
}

/// Our reading of `cell` under the default budget.
pub fn ours(cell: &Cell) -> SourceExistence {
    ours_under(cell, Budget::DEFAULT)
}

/// One indented line per item.
fn lines<T: std::fmt::Debug>(rows: &[T]) -> String {
    rows.iter().map(|r| format!("    {r:?}\n")).collect()
}

/// Grade `ours` against FCS's reading: the verdict, or why the property
/// fails.
pub fn grade(cell: &Cell, fcs: &Reading, ours: &SourceExistence) -> Result<String, String> {
    let rows = match &fcs.view {
        // FCS reads A from its DLL, which a producer the walk reads cannot
        // be: no type provider is in its domain.
        View::Unknown(Unknown::Refused(RefusalCause::ReadsDll)) => {
            return match ours {
                SourceExistence::Unread(why) => Ok(format!("unread {why:?}, FCS reads the DLL")),
                SourceExistence::Read(_) => Err(format!(
                    "{}: FCS reads A from its DLL, and ours is read",
                    cell.name
                )),
            };
        }
        View::Unknown(Unknown::Refused(cause)) => {
            return Ok(format!(
                "ungraded: the oracle refuses ({cause:?}); ours {}",
                short(ours)
            ));
        }
        View::Unknown(Unknown::Undecodable(_)) => {
            return Ok(format!(
                "ungraded: FCS's signature is undecodable; ours {}",
                short(ours)
            ));
        }
        View::Found(rows) => rows,
    };
    let surface = match ours {
        SourceExistence::Unread(why) => return Ok(format!("unread {why:?}")),
        SourceExistence::Read(s) => s,
    };
    let mine = surface_facts(surface);
    let theirs = existence_facts(
        &ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(rows.entities.clone()),
            extensions: Vec::new(),
        },
        &rows.auto_opens,
    );
    let state = if fcs.errors.is_empty() {
        ""
    } else {
        ", FCS rejects"
    };
    let lacking = facts_lacking(&mine, &theirs);
    if !lacking.is_empty() {
        return Err(format!(
            "{}: ours lacks facts FCS's signature holds{state}\n{}",
            cell.name,
            lines(&lacking)
        ));
    }
    let surplus = Surplus::of(&mine, &theirs);
    if surplus.is_zero() {
        Ok(format!("exact{state}"))
    } else {
        Ok(format!("covers{state} {surplus}"))
    }
}

/// `ours` in a few words, for a verdict that grades nothing.
fn short(ours: &SourceExistence) -> String {
    match ours {
        SourceExistence::Read(_) => "read".to_owned(),
        SourceExistence::Unread(why) => format!("unread {why:?}"),
    }
}

/// Every entity fact of `theirs` that `mine` lacks.
pub fn facts_lacking(mine: &ExistenceFacts, theirs: &ExistenceFacts) -> Vec<String> {
    fn paths(
        kind: &str,
        ours: &BTreeSet<Vec<String>>,
        theirs: &BTreeSet<Vec<String>>,
    ) -> Vec<String> {
        theirs
            .difference(ours)
            .map(|p| format!("{kind} {}", p.join(".")))
            .collect()
    }
    let mut lacking = Vec::new();
    if theirs.unknowable && !mine.unknowable {
        lacking.push("unknowable".to_owned());
    }
    lacking.extend(paths("prefix", &mine.prefixes, &theirs.prefixes));
    lacking.extend(paths("entity", &mine.entities, &theirs.entities));
    // An entity that may lend anything lends its children too.
    let lends_children: BTreeSet<Vec<String>> = mine
        .lends_children
        .union(&mine.lends_anything)
        .cloned()
        .collect();
    lacking.extend(paths(
        "lends-children",
        &lends_children,
        &theirs.lends_children,
    ));
    lacking.extend(paths(
        "lends-anything",
        &mine.lends_anything,
        &theirs.lends_anything,
    ));
    lacking.extend(paths(
        "abbreviation-lender",
        &mine.abbreviation_lenders,
        &theirs.abbreviation_lenders,
    ));
    lacking.extend(paths(
        "auto-open",
        &mine.auto_open_bases,
        &theirs.auto_open_bases,
    ));
    lacking
}

/// How many entity facts ours holds beyond FCS's, per kind.
struct Surplus {
    prefixes: usize,
    entities: usize,
    lends: usize,
}

impl Surplus {
    fn of(mine: &ExistenceFacts, theirs: &ExistenceFacts) -> Surplus {
        let n = |a: &BTreeSet<Vec<String>>, b: &BTreeSet<Vec<String>>| a.difference(b).count();
        Surplus {
            prefixes: n(&mine.prefixes, &theirs.prefixes),
            entities: n(&mine.entities, &theirs.entities),
            lends: n(&mine.lends_children, &theirs.lends_children)
                + n(&mine.lends_anything, &theirs.lends_anything),
        }
    }

    fn is_zero(&self) -> bool {
        self.prefixes + self.entities + self.lends == 0
    }
}

impl std::fmt::Display for Surplus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "surplus(prefix {}, entity {}, lends {})",
            self.prefixes, self.entities, self.lends
        )
    }
}

/// Grade every cell: the manifest entries (each with FCS's errors), and
/// every failure. A cell's panic (an oracle invariant) is its own failure.
pub fn grade_cells(cells: &[Cell]) -> (Vec<(String, String)>, Vec<String>) {
    let results = borzoi_oracle_harness::par_map::par_map(cells.len(), |i| {
        let cell = &cells[i];
        let _silence = borzoi_oracle_harness::panic_silence::silence_panics_here();
        let graded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let fcs = read(&cell.graph);
            let verdict = grade(cell, &fcs, &ours(cell));
            (verdict, fcs.errors)
        }));
        match graded {
            Ok((verdict, errors)) => (cell.name.clone(), verdict, errors),
            Err(panic) => {
                let message = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                    .unwrap_or_default();
                (
                    cell.name.clone(),
                    Err(format!("{}: panicked: {message}", cell.name)),
                    Vec::new(),
                )
            }
        }
    });
    let mut entries = Vec::new();
    let mut failures = Vec::new();
    for (name, verdict, errors) in results {
        match verdict {
            Ok(v) => {
                let fcs = if errors.is_empty() {
                    String::new()
                } else {
                    format!(" [FCS: {}]", errors.join(","))
                };
                entries.push((name, format!("{v}{fcs}")));
            }
            Err(e) => failures.push(e),
        }
    }
    (entries, failures)
}

/// Whether a verdict grades our reading against FCS's: a read FCS found.
pub fn graded(verdict: &str) -> bool {
    verdict.starts_with("exact") || verdict.starts_with("covers")
}
