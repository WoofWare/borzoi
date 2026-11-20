//! Every generator in the workspace draws hostile values, or says why not.
//!
//! [`BOUNDARIES`] is one table of every generative differential and
//! perturbation sweep under `crates/`: a row per source file, saying which
//! censuses the file runs and the kinds each draws, or the reason no hostile
//! kind applies to it. [`check`] holds the table to the source:
//!
//! - a file that [`scan`] finds to be a generator and that has no row fails,
//!   so a new generator cannot be added without the decision being made;
//! - a row that says a file draws must be true of the file (it uses this
//!   module and names each census), and each census must have its pinned
//!   manifest, covering exactly the dimensions of the kinds declared;
//! - a row that says no kind applies must not sit on a file that draws.
//!
//! A harness opens its census through the table ([`open`]), so what it owes
//! is what the table says and nothing it could quietly narrow.
//!
//! # What counts as a generator
//!
//! [`scan`] reads each file's tokens (with rustc's lexer, so a word in a
//! comment or a string is not a marker) and takes a file for a generator on
//! any of: a proptest strategy or runner; one of the workspace's hand-rolled
//! random number generators; one of the shared perturbation engines; this
//! module; or a file name that says so (`_grid`, `_sweep`, `_generative`
//! and the like). A grid built from nested loops over tables has no marker
//! but its name, and can be given a row by hand: a row needs only that its
//! file exists.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use proc_macro2::{TokenStream, TokenTree};

use super::census::{Census, Declared};
use super::{Dimension, Kind};
use crate::manifest::{self, Manifest};

/// The table, as checked in.
pub const BOUNDARIES: &str = include_str!("boundaries.tsv");

/// How many rows may be [`Status::Pending`], per level: the harnesses that
/// predate the library. `pending` is their status alone, so a new generator
/// cannot take it: a row added as pending exceeds the ceiling. Lower each
/// number as its level's retrofit decides rows.
pub const PENDING_BACKLOG: &[(u8, usize)] = &[(2, 82), (3, 238)];

/// The library's own sources, which [`scan`] passes over.
const LIBRARY: &str = "crates/oracle-harness/src/hostile/";

/// The workspace this crate was built in.
pub fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits at <workspace>/crates/<crate>")
        .to_owned()
}

/// What a row says of its file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    /// Not yet decided: the file predates the library, and the retrofit of
    /// this level (of the library's plan) will decide it.
    Pending {
        /// The level.
        level: u8,
    },
    /// No hostile kind applies, for this reason.
    NotApplicable {
        /// The reason.
        reason: String,
    },
    /// The file runs these censuses.
    Draws(Vec<Declared>),
}

/// One row: a source file, relative to the workspace, and its status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Boundary {
    /// The file.
    pub path: String,
    /// Its status.
    pub status: Status,
}

/// Read a table: one row per line, `path<TAB>status<TAB>detail`, sorted by
/// path, with `#` comment lines. The statuses are `pending` (detail: the
/// level), `not-applicable` (detail: the reason) and `draws` (detail:
/// `census=kind+kind;census=kind`).
///
/// # Errors
///
/// The first malformed line, with its number.
pub fn parse(table: &str) -> Result<Vec<Boundary>, String> {
    let mut rows: Vec<Boundary> = Vec::new();
    for (i, line) in table.lines().enumerate() {
        let bad = |why: &str| format!("line {}: {why}: {line:?}", i + 1);
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let [path, status, detail] = fields[..] else {
            return Err(bad("a row is path, status and detail, tab-separated"));
        };
        let status = match status {
            "pending" => Status::Pending {
                level: detail
                    .parse()
                    .map_err(|_| bad("a pending row's detail is its level"))?,
            },
            "not-applicable" => {
                if detail.trim().len() < 10 {
                    return Err(bad("a row that applies no kind says why"));
                }
                Status::NotApplicable {
                    reason: detail.to_owned(),
                }
            }
            "draws" => {
                let mut censuses: Vec<Declared> = Vec::new();
                for part in detail.split(';') {
                    let (census, kinds) = part
                        .split_once('=')
                        .ok_or_else(|| bad("a census is name=kind+kind"))?;
                    let valid_name = !census.is_empty()
                        && census
                            .bytes()
                            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_');
                    if !valid_name {
                        return Err(bad("a census's name is lower-case words joined by `_`"));
                    }
                    let mut set = BTreeSet::new();
                    for kind in kinds.split('+') {
                        let kind = Kind::from_id(kind)
                            .ok_or_else(|| bad(&format!("{kind:?} is no hostile kind")))?;
                        if !set.insert(kind) {
                            return Err(bad("a census names a kind twice"));
                        }
                    }
                    if censuses.iter().any(|c| c.census == census) {
                        return Err(bad("a file names a census twice"));
                    }
                    censuses.push(Declared {
                        harness: path.to_owned(),
                        census: census.to_owned(),
                        kinds: set,
                    });
                }
                Status::Draws(censuses)
            }
            _ => return Err(bad("the status is pending, not-applicable or draws")),
        };
        if let Some(previous) = rows.last()
            && previous.path.as_str() >= path
        {
            return Err(bad("rows are sorted by path, each path once"));
        }
        rows.push(Boundary {
            path: path.to_owned(),
            status,
        });
    }
    Ok(rows)
}

/// The crate a workspace-relative source path belongs to
/// (`crates/<crate>/…`).
fn crate_of(path: &str) -> Option<&str> {
    path.strip_prefix("crates/")?.split('/').next()
}

/// Where the manifest of `declared`'s census is pinned.
///
/// # Panics
///
/// If the harness is not under `crates/<crate>/`.
pub fn manifest_path(workspace: &Path, declared: &Declared) -> PathBuf {
    let krate = crate_of(&declared.harness).unwrap_or_else(|| {
        panic!(
            "{} is not under crates/<crate>/, so its census has nowhere to be pinned",
            declared.harness
        )
    });
    workspace
        .join("crates")
        .join(krate)
        .join("tests/manifests/hostile")
        .join(format!("{}.txt", declared.census))
}

/// Open the census `census` of the harness in `file` (pass `file!()`), as
/// [`BOUNDARIES`] declares it, excluding `excluded`.
///
/// # Panics
///
/// If the table does not say that `file` runs a census of that name. That is
/// the point: a harness draws what the table says it draws.
pub fn open(file: &str, census: &str, excluded: &[(Dimension, &'static str)]) -> Census {
    let declared = declared(BOUNDARIES, file, census).unwrap_or_else(|e| panic!("{e}"));
    Census::new(declared, excluded).owing_a_finish()
}

/// What `table` declares for the census `census` of the harness in `file`.
///
/// # Errors
///
/// If the table is malformed, or does not say that `file` runs a census of
/// that name.
pub fn declared(table: &str, file: &str, census: &str) -> Result<Declared, String> {
    let rows = parse(table).map_err(|e| format!("boundaries.tsv: {e}"))?;
    rows.iter()
        .find(|row| row.path == file)
        .and_then(|row| match &row.status {
            Status::Draws(censuses) => censuses.iter().find(|c| c.census == census),
            _ => None,
        })
        .cloned()
        .ok_or_else(|| {
            format!(
                "boundaries.tsv does not say that {file} runs a census named {census:?}. Add \
                 `{file}<TAB>draws<TAB>{census}=<kind>+<kind>` to \
                 crates/oracle-harness/src/hostile/boundaries.tsv."
            )
        })
}

/// A file [`scan`] takes for a generator, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generator {
    /// The file, relative to the workspace.
    pub path: String,
    /// What marks it as a generator.
    pub markers: BTreeSet<&'static str>,
    /// Whether it uses this module (`hostile::`).
    pub draws: bool,
    /// Every string literal in it, for finding a census's name.
    strings: BTreeSet<String>,
}

/// One token, flattened out of its groups: all a marker needs.
#[derive(Debug, PartialEq, Eq)]
enum Token {
    Ident(String),
    Punct(char),
    Literal(String),
}

fn flatten(stream: TokenStream, out: &mut Vec<Token>) {
    for tree in stream {
        match tree {
            TokenTree::Group(group) => flatten(group.stream(), out),
            TokenTree::Ident(ident) => out.push(Token::Ident(ident.to_string())),
            TokenTree::Punct(punct) => out.push(Token::Punct(punct.as_char())),
            TokenTree::Literal(literal) => out.push(Token::Literal(literal.to_string())),
        }
    }
}

/// Identifiers that mark a generator wherever they occur.
const IDENT_MARKERS: &[(&str, &str)] = &[
    ("TestRunner", "a proptest runner"),
    ("prop_oneof", "a proptest strategy"),
    ("prop_compose", "a proptest strategy"),
    ("Strategy", "a proptest strategy"),
    ("BoxedStrategy", "a proptest strategy"),
    ("SplitMix64", "a hand-rolled random number generator"),
    ("Rng", "a hand-rolled random number generator"),
    ("seed_tape", "a seeded tape of choices"),
    ("seeded_tape", "a seeded tape of choices"),
    ("generate_seed", "a seeded generator"),
    ("soak_parameters", "a seeded soak"),
    ("perturbations", "the read-set perturbation sweep"),
    ("fifo_perturbations", "the read-set perturbation sweep"),
];

/// Identifiers that mark a generator when a path goes through them
/// (`name::…`): the shared engines, which are modules.
const PATH_MARKERS: &[(&str, &str)] = &[
    ("soundness", "the read-set perturbation sweep"),
    ("perturb", "the source-text perturbation"),
    ("xml_pump", "the XML nesting pump"),
    ("repetition_shapes", "the tall-tree shapes"),
    ("modifier_metamorphic", "the custom-modifier probe"),
    ("shape_metamorphic", "the compiler-shape probe"),
];

/// Parts of a file's name that mark a generator.
const NAME_MARKERS: &[&str] = &[
    "_grid",
    "_matrix",
    "_gen_diff",
    "_generative",
    "_generated",
    "_sweep",
    "_perturbation",
    "_metamorphic",
    "_exhaustive",
    "soak",
];

/// Whether, and why, the Rust source `text` named `path` is a generator.
///
/// # Errors
///
/// If `text` does not lex as Rust: a file the check cannot read is not one
/// it may pass over.
pub fn classify(path: &str, text: &str) -> Result<Option<Generator>, String> {
    let stream = TokenStream::from_str(text).map_err(|e| format!("{path} does not lex: {e}"))?;
    let mut tokens = Vec::new();
    flatten(stream, &mut tokens);
    let mut markers = BTreeSet::new();
    let mut draws = false;
    let mut strings = BTreeSet::new();
    for (i, token) in tokens.iter().enumerate() {
        let next_is = |c: char| tokens.get(i + 1) == Some(&Token::Punct(c));
        match token {
            Token::Ident(ident) => {
                if ident == "proptest" && next_is('!') {
                    markers.insert("a proptest block");
                }
                if let Some((_, why)) = IDENT_MARKERS.iter().find(|(name, _)| name == ident) {
                    markers.insert(*why);
                }
                let in_path = next_is(':') && tokens.get(i + 2) == Some(&Token::Punct(':'));
                if in_path {
                    if let Some((_, why)) = PATH_MARKERS.iter().find(|(name, _)| name == ident) {
                        markers.insert(*why);
                    }
                    if ident == "hostile" {
                        markers.insert("the hostile-value library");
                        draws = true;
                    }
                }
            }
            Token::Literal(literal) => {
                // A plain string literal's content, which is all a census's
                // name can be (lower-case words, nothing to unescape).
                if let Some(content) = literal
                    .strip_prefix('"')
                    .and_then(|rest| rest.strip_suffix('"'))
                {
                    strings.insert(content.to_owned());
                }
            }
            Token::Punct(_) => {}
        }
    }
    let stem = Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    if NAME_MARKERS.iter().any(|marker| stem.contains(marker)) {
        markers.insert("its file name");
    }
    Ok((!markers.is_empty()).then(|| Generator {
        path: path.to_owned(),
        markers,
        draws,
        strings,
    }))
}

/// The Rust sources under `dir`. `optional` says the directory may be
/// absent (a crate need have no `tests/`); any other failure to list one is a
/// panic, since a scan that cannot read a directory has not scanned it.
fn rust_files(dir: &Path, optional: bool, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(e) if optional && e.kind() == std::io::ErrorKind::NotFound => return,
        Err(e) => panic!("list {}: {e}", dir.display()),
    };
    for entry in entries {
        let entry = entry.expect("read a directory entry");
        let path = entry.path();
        // The entry's own type: a link is not followed, so the scan stays in
        // the checkout and never opens what is not a regular file.
        let kind = entry.file_type().expect("a directory entry's type");
        if kind.is_dir() {
            rust_files(&path, false, out);
        } else if kind.is_file() {
            if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        } else {
            panic!(
                "{} is a link or a special file among the sources: the scan reads only \
                 regular files, and will not pass over one it cannot classify",
                path.display()
            );
        }
    }
}

/// Every generator under `workspace`'s `crates/*/src` and `crates/*/tests`,
/// sorted by path.
///
/// # Panics
///
/// If a source file cannot be read or does not lex.
pub fn scan(workspace: &Path) -> Vec<Generator> {
    let mut files = Vec::new();
    let crates = workspace.join("crates");
    for krate in
        std::fs::read_dir(&crates).unwrap_or_else(|e| panic!("read {}: {e}", crates.display()))
    {
        let krate = krate.expect("read a directory entry").path();
        if !krate.is_dir() {
            continue;
        }
        rust_files(&krate.join("src"), true, &mut files);
        rust_files(&krate.join("tests"), true, &mut files);
    }
    let mut generators: Vec<Generator> = files
        .iter()
        .filter_map(|file| {
            let relative = file
                .strip_prefix(workspace)
                .expect("a scanned file is under the workspace")
                .to_str()
                .unwrap_or_else(|| panic!("{} is not text", file.display()));
            // The library is what the generators draw from, not one of them.
            if relative.starts_with(LIBRARY) {
                return None;
            }
            let text = std::fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("read {}: {e}", file.display()));
            classify(relative, &text).unwrap_or_else(|e| panic!("{e}"))
        })
        .collect();
    generators.sort_by(|a, b| a.path.cmp(&b.path));
    generators
}

/// The keys a census's manifest must hold: the harness's own values, and
/// every dimension of the kinds it declares.
fn manifest_keys(declared: &Declared) -> BTreeSet<String> {
    let mut keys = BTreeSet::from(["plain".to_owned()]);
    keys.extend(
        declared
            .kinds
            .iter()
            .flat_map(|k| k.dimensions())
            .map(Dimension::key),
    );
    keys
}

/// What a passing check found, for a report.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Coverage {
    /// Generators with a row.
    pub generators: usize,
    /// Rows whose file draws hostile values.
    pub drawing: usize,
    /// Rows that apply no kind.
    pub not_applicable: usize,
    /// Rows not yet decided, by level.
    pub pending: BTreeMap<u8, usize>,
}

/// Hold `table` to the source under `workspace`.
///
/// # Errors
///
/// Every way the two disagree, one message each.
pub fn check(workspace: &Path, table: &str) -> Result<Coverage, Vec<String>> {
    let rows = parse(table).map_err(|e| vec![format!("the table is malformed: {e}")])?;
    let generators = scan(workspace);
    let by_path: BTreeMap<&str, &Generator> =
        generators.iter().map(|g| (g.path.as_str(), g)).collect();
    let rows_by_path: BTreeMap<&str, &Boundary> =
        rows.iter().map(|r| (r.path.as_str(), r)).collect();
    let mut problems = Vec::new();
    let mut coverage = Coverage::default();

    for generator in &generators {
        if rows_by_path.contains_key(generator.path.as_str()) {
            coverage.generators += 1;
        } else {
            problems.push(format!(
                "{} is a generator ({}) with no row. Add one saying which hostile kinds it \
                 draws (`draws`), or why none applies (`not-applicable`).",
                generator.path,
                generator
                    .markers
                    .iter()
                    .copied()
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }

    let mut census_owner: BTreeMap<(String, String), &str> = BTreeMap::new();
    for row in &rows {
        if !workspace.join(&row.path).is_file() {
            problems.push(format!("{} has a row and does not exist.", row.path));
            continue;
        }
        let generator = by_path.get(row.path.as_str());
        let draws = generator.is_some_and(|g| g.draws);
        match &row.status {
            Status::Pending { level } => {
                *coverage.pending.entry(*level).or_default() += 1;
                if draws {
                    problems.push(format!(
                        "{} is pending and uses the hostile library: say what it draws.",
                        row.path
                    ));
                }
            }
            Status::NotApplicable { .. } => {
                coverage.not_applicable += 1;
                if draws {
                    problems.push(format!(
                        "{} applies no hostile kind, its row says, and it uses the hostile \
                         library.",
                        row.path
                    ));
                }
            }
            Status::Draws(censuses) => {
                coverage.drawing += 1;
                if !draws {
                    problems.push(format!(
                        "{} draws hostile values, its row says, and it never uses the hostile \
                         library.",
                        row.path
                    ));
                }
                for declared in censuses {
                    if generator.is_some_and(|g| !g.strings.contains(&declared.census)) {
                        problems.push(format!(
                            "{} never names its census {:?}.",
                            row.path, declared.census
                        ));
                    }
                    let Some(krate) = crate_of(&row.path) else {
                        problems.push(format!("{} is not under crates/<crate>/.", row.path));
                        continue;
                    };
                    let key = (krate.to_owned(), declared.census.clone());
                    if let Some(other) = census_owner.insert(key, &row.path) {
                        problems.push(format!(
                            "{} and {other} both name a census {:?}: one crate's censuses \
                             share a directory of manifests.",
                            row.path, declared.census
                        ));
                    }
                    let path = manifest_path(workspace, declared);
                    let pinned = std::fs::read_to_string(&path)
                        .map_err(|e| e.to_string())
                        .and_then(|text| {
                            Manifest::parse(&text).map_err(|(line, e)| format!("line {line}: {e}"))
                        });
                    match pinned {
                        Err(e) => problems.push(format!(
                            "{}'s census {:?} has no readable manifest at {} ({e}): the \
                             census has never run.",
                            row.path,
                            declared.census,
                            path.display()
                        )),
                        Ok(pinned) => {
                            let keys: BTreeSet<String> = pinned
                                .entries()
                                .iter()
                                .map(|e| manifest::key_of(e).to_owned())
                                .collect();
                            let owed = manifest_keys(declared);
                            if keys != owed {
                                problems.push(format!(
                                    "{}'s census {:?} is pinned over other dimensions than its \
                                     row declares (only pinned: {:?}; only declared: {:?}): \
                                     rerun the census.",
                                    row.path,
                                    declared.census,
                                    keys.difference(&owed).collect::<Vec<_>>(),
                                    owed.difference(&keys).collect::<Vec<_>>()
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    if problems.is_empty() {
        Ok(coverage)
    } else {
        Err(problems)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A workspace of one crate holding `files`, each a path under the crate
    /// and its text.
    fn workspace_of(files: &[(&str, &str)]) -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        for (path, text) in files {
            let path = dir.path().join("crates/demo").join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        dir
    }

    const DRAWING: &str = r#"
        use borzoi_oracle_harness::hostile;
        #[test]
        fn sweep() {
            let census = hostile::coverage::open(file!(), "demo_changes", &[]);
        }
    "#;

    fn manifest_for(kinds: &[Kind]) -> String {
        let declared = Declared {
            harness: "crates/demo/tests/x.rs".into(),
            census: "demo_changes".into(),
            kinds: kinds.iter().copied().collect(),
        };
        manifest_keys(&declared)
            .into_iter()
            .map(|key| format!("{key}\treached\n"))
            .collect()
    }

    #[test]
    fn the_checked_in_table_matches_the_workspace() {
        match check(&workspace(), BOUNDARIES) {
            Ok(coverage) => {
                eprintln!("hostile coverage: {coverage:?}");
                for (level, pending) in &coverage.pending {
                    let ceiling = PENDING_BACKLOG
                        .iter()
                        .find(|(l, _)| l == level)
                        .map_or(0, |(_, n)| *n);
                    assert!(
                        *pending <= ceiling,
                        "{pending} rows are pending at level {level}, and the backlog of \
                         harnesses that predate the library was {ceiling}: a new generator \
                         says what it draws or why nothing applies, it is not pending"
                    );
                }
            }
            Err(problems) => panic!(
                "crates/oracle-harness/src/hostile/boundaries.tsv does not match the \
                 workspace:\n  {}",
                problems.join("\n  ")
            ),
        }
    }

    #[test]
    fn markers_are_tokens_not_text() {
        let quiet = r#"
            // proptest! { } and SplitMix64 in a comment
            const DOC: &str = "TestRunner::new and hostile::name";
            fn strategy_free() {}
        "#;
        assert_eq!(classify("crates/demo/tests/plain.rs", quiet), Ok(None));
        for (text, marker) in [
            ("proptest! { fn f(x in 0..1) {} }", "a proptest block"),
            (
                "fn s() -> impl Strategy<Value = u8> { 0u8 }",
                "a proptest strategy",
            ),
            (
                "fn f() { let mut r = SplitMix64(1); }",
                "a hand-rolled random number generator",
            ),
            (
                "fn f() { soundness::sweep(); }",
                "the read-set perturbation sweep",
            ),
            ("fn f() { xml_pump::pumps(); }", "the XML nesting pump"),
            (
                "fn f() { hostile::name::alphabet(); }",
                "the hostile-value library",
            ),
        ] {
            let found = classify("crates/demo/tests/plain.rs", text)
                .unwrap()
                .unwrap();
            assert!(
                found.markers.contains(marker),
                "{text}: {:?}",
                found.markers
            );
        }
        // A module declaration is not a use of the module.
        assert_eq!(
            classify(
                "crates/demo/src/lib.rs",
                "pub mod xml_pump; pub mod hostile;"
            ),
            Ok(None)
        );
        // A file's name alone marks it.
        let grid = classify("crates/demo/tests/all/case_grid.rs", "fn f() {}").unwrap();
        assert!(grid.unwrap().markers.contains("its file name"));
        assert!(classify("crates/demo/tests/bad.rs", "fn f() { \" }").is_err());
    }

    #[test]
    fn a_generator_with_no_row_fails() {
        let ws = workspace_of(&[("tests/new_sweep.rs", "proptest! {}")]);
        let problems = check(ws.path(), "").unwrap_err();
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(problems[0].starts_with(
            "crates/demo/tests/new_sweep.rs is a generator (a proptest block, its file name) \
             with no row"
        ));
        // With a row of any status, it passes.
        for row in [
            "pending\t2",
            "not-applicable\tits values are internal model terms",
        ] {
            let table = format!("crates/demo/tests/new_sweep.rs\t{row}\n");
            check(ws.path(), &table).unwrap();
        }
    }

    #[test]
    fn a_row_for_a_missing_file_fails() {
        let ws = workspace_of(&[("src/lib.rs", "")]);
        let problems = check(ws.path(), "crates/demo/tests/gone.rs\tpending\t2\n").unwrap_err();
        assert_eq!(
            problems,
            ["crates/demo/tests/gone.rs has a row and does not exist."]
        );
    }

    #[test]
    fn a_drawing_row_needs_the_use_the_name_and_the_manifest() {
        let table = "crates/demo/tests/x.rs\tdraws\tdemo_changes=change+cwd\n";
        let manifest = manifest_for(&[Kind::FsChange, Kind::WorkingDirectory]);
        let good = workspace_of(&[
            ("tests/x.rs", DRAWING),
            ("tests/manifests/hostile/demo_changes.txt", &manifest),
        ]);
        let coverage = check(good.path(), table).unwrap();
        assert_eq!((coverage.generators, coverage.drawing), (1, 1));

        // No manifest: the census never ran.
        let unrun = workspace_of(&[("tests/x.rs", DRAWING)]);
        let problems = check(unrun.path(), table).unwrap_err();
        assert!(
            problems[0].contains("the census has never run"),
            "{problems:?}"
        );

        // A manifest over other dimensions than the row declares.
        let narrow = workspace_of(&[
            ("tests/x.rs", DRAWING),
            (
                "tests/manifests/hostile/demo_changes.txt",
                &manifest_for(&[Kind::FsChange]),
            ),
        ]);
        let problems = check(narrow.path(), table).unwrap_err();
        assert!(
            problems[0].contains("only declared: [\"cwd."),
            "{problems:?}"
        );

        // A file that does not use the library, or never names the census.
        let idle = workspace_of(&[
            ("tests/x.rs", "proptest! {}"),
            ("tests/manifests/hostile/demo_changes.txt", &manifest),
        ]);
        let problems = check(idle.path(), table).unwrap_err();
        assert!(
            problems[0].contains("never uses the hostile library"),
            "{problems:?}"
        );
        assert!(
            problems[1].contains("never names its census"),
            "{problems:?}"
        );
    }

    #[test]
    fn a_file_that_draws_cannot_be_pending_or_not_applicable() {
        let ws = workspace_of(&[("tests/x.rs", DRAWING)]);
        for row in ["pending\t2", "not-applicable\tno hostile kind applies here"] {
            let table = format!("crates/demo/tests/x.rs\t{row}\n");
            let problems = check(ws.path(), &table).unwrap_err();
            assert!(problems[0].contains("uses the hostile"), "{problems:?}");
        }
    }

    #[test]
    fn malformed_tables_are_refused() {
        for (table, why) in [
            ("a.rs\tpending\n", "tab-separated"),
            ("a.rs\tpending\tsoon\n", "its level"),
            ("a.rs\tnot-applicable\tno\n", "says why"),
            ("a.rs\tdraws\tx=nonsense\n", "no hostile kind"),
            ("a.rs\tdraws\tX=fs\n", "lower-case"),
            ("a.rs\tdraws\tx=fs+fs\n", "a kind twice"),
            ("a.rs\tdraws\tx=fs;x=cwd\n", "a census twice"),
            ("a.rs\tskipped\tx\n", "the status is"),
            ("b.rs\tpending\t2\na.rs\tpending\t2\n", "sorted by path"),
            ("a.rs\tpending\t2\na.rs\tpending\t2\n", "sorted by path"),
        ] {
            let error = parse(table).unwrap_err();
            assert!(error.contains(why), "{table:?}: {error}");
        }
        let rows = parse("# comment\n\na.rs\tdraws\tone=fs+name;two=wire\n").unwrap();
        let Status::Draws(censuses) = &rows[0].status else {
            panic!("{rows:?}")
        };
        assert_eq!(censuses.len(), 2);
        assert_eq!(
            censuses[0].kinds,
            BTreeSet::from([Kind::FileName, Kind::FsState])
        );
    }

    #[test]
    fn a_census_is_declared_only_by_the_table() {
        let table = "crates/demo/tests/x.rs\tdraws\tone=fs+name\ny.rs\tpending\t2\n";
        let found = declared(table, "crates/demo/tests/x.rs", "one").unwrap();
        assert_eq!(found.kinds, BTreeSet::from([Kind::FileName, Kind::FsState]));
        assert_eq!(found.harness, "crates/demo/tests/x.rs");
        for (file, census) in [
            ("crates/demo/tests/x.rs", "two"),
            ("y.rs", "one"),
            ("z.rs", "one"),
        ] {
            let error = declared(table, file, census).unwrap_err();
            assert!(error.contains("does not say"), "{error}");
        }
    }
}
