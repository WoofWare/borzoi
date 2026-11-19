//! `borzoi_sema::source_existence` held to FCS (Stage 1a of the
//! source-references plan).
//!
//! Each cell is a producer project A. FCS checks a consumer with A handed to
//! it from source (`fcs-dump`'s `referenced` op, through the project-graph
//! request), and three readings of A's surface are compared in one currency,
//! the existence rows of `borzoi_assembly::existence` (pickle entity rows,
//! pickle extension rows, assembly-level `AutoOpen` paths):
//!
//! - **FCS's in-memory signature**: the raw streams that cross the
//!   `FSharpReference` boundary, decoded with
//!   `borzoi_assembly::unpickle_signature`, and the `AutoOpen` strings that
//!   travel beside them;
//! - **the DLL FCS compiles** from the same argument vector, read through
//!   `Ecma335Assembly::existence_index` (D1 in rows: the two must agree);
//! - **ours**: `source_existence` over A's files parsed under A's defines.
//!
//! FCS's own view of the in-memory assembly (`FSharpAssembly.Contents`, the
//! `assembly-entities` kind) is held to the decoded rows too, so the decoder
//! is graded on what a dependant reads.
//!
//! The properties, per cell and per [`MarkerRoutes`] reading:
//!
//! - **covers**: when ours is `Read`, every FCS row is one of ours (multiset
//!   containment), and every FCS auto-open path is ours;
//! - **exact**: when ours is `Read` and names no approximation, ours equals
//!   FCS's, row for row. A cell FCS rejects is outside that domain;
//! - the per-cell verdict is pinned in `tests/manifests/source_existence_diff.txt`.
//!
//! Cells are graded under the certificate a correct caller gives
//! ([`certify_by_spelling`] when A's references add no route to a marker,
//! a hand-written one otherwise) and under [`MarkerRoutes::Unknown`].

use std::collections::{BTreeMap, HashSet};
use std::path::PathBuf;

use borzoi_assembly::existence::{ExtensionRow, IndexLayer, PickleLayer, PickledEntityRow};
use borzoi_assembly::{Ecma335Assembly, EcmaView};
use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_cst::syntax::{AstNode, ImplFile, SigFile};
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::{
    CompileResponse, FixtureFile, FixtureProject, PlainName, ProjectGraphFixture,
    ReferencedResponse, Target, framework_references, parse_response,
};
use borzoi_sema::{
    CompileItem, Marker, MarkerRoutes, Producer, ProjectFile, SourceExistence, SourceFile,
    SyntaxRecovery, certify_by_spelling, qualified_names, source_existence,
};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::common::invoke_fcs_dump_graph;

/// A project A's reference besides the framework: compiled from source.
#[derive(Clone)]
pub struct RefLib {
    pub name: &'static str,
    pub files: Vec<(String, String)>,
}

/// How a cell's certificate is made.
#[derive(Clone)]
pub enum Certificate {
    /// [`certify_by_spelling`]: A's references add no route to a marker.
    BySpelling,
    /// By spelling, then these written names (dot-joined) denote these
    /// markers instead.
    Override(Vec<(&'static str, Vec<Marker>)>),
}

/// One producer project.
#[derive(Clone)]
pub struct Cell {
    pub name: String,
    /// File name and text, in Compile order.
    pub files: Vec<(String, String)>,
    pub defines: Vec<String>,
    pub refs: Vec<RefLib>,
    pub certificate: Certificate,
    pub target: Target,
}

impl Cell {
    pub fn new(name: impl Into<String>, files: &[(&str, &str)]) -> Self {
        Cell {
            name: name.into(),
            files: files
                .iter()
                .map(|(n, t)| ((*n).to_owned(), (*t).to_owned()))
                .collect(),
            defines: Vec::new(),
            refs: Vec::new(),
            certificate: Certificate::BySpelling,
            target: Target::Library,
        }
    }
}

/// The three readings of A in row currency.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rows {
    pub entities: Vec<PickledEntityRow>,
    pub extensions: Vec<ExtensionRow>,
    pub auto_opens: Vec<String>,
}

impl Rows {
    fn sorted(mut self) -> Self {
        self.entities.sort();
        self.extensions.sort();
        self
    }
}

/// What FCS made of a cell.
pub struct Fcs {
    /// FCS's in-memory signature, decoded: what a dependant reads, so
    /// empty when FCS imports nothing of the producer.
    pub memory: Rows,
    /// Whether A checked with no error.
    pub clean: bool,
    pub errors: Vec<String>,
}

fn plain(s: &str) -> PlainName {
    PlainName::new(s).expect("a plain name")
}

fn request<T: serde::de::DeserializeOwned>(line: &str) -> Result<T, String> {
    parse_response(&invoke_fcs_dump_graph(line)).map_err(|e| format!("{e:?}"))
}

fn files_of(files: &[(String, String)]) -> Vec<FixtureFile> {
    files
        .iter()
        .map(|(name, text)| FixtureFile {
            name: name.clone(),
            text: text.clone(),
        })
        .collect()
}

/// Decode one assembly's signature streams into rows.
fn decode(primary: &[u8], b: Option<&[u8]>) -> Result<(Vec<PickledEntityRow>, Vec<ExtensionRow>), String> {
    let ccu = borzoi_assembly::unpickle_signature(primary, b).map_err(|e| e.to_string())?;
    borzoi_assembly::existence::pickled_rows(&ccu)
}

/// The producer's assembly name: fixed, so no generated name can collide
/// with it.
const PRODUCER: &str = "SourceExistenceProducer";

/// Ask FCS about `cell`: its in-memory signature, and (D1 in rows) that the
/// DLL FCS compiles reads the same.
pub fn fcs(cell: &Cell) -> Fcs {
    let mut projects: Vec<FixtureProject> = cell
        .refs
        .iter()
        .map(|r| FixtureProject::new(plain(r.name), files_of(&r.files)))
        .collect();
    let mut a = FixtureProject::new(plain(PRODUCER), files_of(&cell.files));
    a.defines = cell.defines.clone();
    a.target = cell.target;
    projects.push(a);
    let mut b = FixtureProject::new(
        plain("SourceExistenceConsumer"),
        vec![FixtureFile {
            name: "Consumer.fs".to_owned(),
            text: "module SourceExistenceConsumer.Use\nlet x = 1\n".to_owned(),
        }],
    );
    b.project_refs = vec![plain(PRODUCER)];
    projects.push(b);
    let fixture = ProjectGraphFixture::materialise(projects).expect("materialise the cell");
    let mut framework: Vec<PathBuf> = framework_references().to_vec();
    for r in &cell.refs {
        let line = fixture
            .compile_request(&plain(r.name), framework_references(), &BTreeMap::new());
        let out: CompileResponse = request(line.as_line()).expect("compile a reference");
        let dll = out
            .output
            .unwrap_or_else(|| panic!("{}: reference {} failed: {:?}", cell.name, r.name, out.diagnostics));
        framework.push(dll);
    }
    let graph = fixture.request(
        &plain("SourceExistenceConsumer"),
        &framework,
        &BTreeMap::new(),
    );
    let line = graph
        .referenced_line(&plain(PRODUCER))
        .expect("the consumer references the producer");
    let response: ReferencedResponse =
        request(&line).unwrap_or_else(|e| panic!("{}: referenced: {e}", cell.name));
    let errors: Vec<String> = response.errors().map(|d| format!("FS{}", d["ErrorNumber"])).collect();
    let streams: Vec<_> = response
        .signature
        .streams
        .iter()
        .filter(|s| s.ccu == PRODUCER)
        .collect();
    assert!(
        streams.len() == 1 || (streams.is_empty() && !errors.is_empty()),
        "{}: {} signatures for the producer",
        cell.name,
        streams.len()
    );
    // A producer FCS builds no assembly data for is one a dependant reads
    // nothing of.
    let (entities, extensions) = match streams.first() {
        None => (Vec::new(), Vec::new()),
        Some(s) => {
            let primary = s.primary_bytes().expect("hex");
            let b = s.b_bytes().expect("hex");
            decode(&primary, b.as_deref()).unwrap_or_else(|e| {
                panic!("{}: the in-memory signature does not decode: {e}", cell.name)
            })
        }
    };
    let memory = Rows {
        entities,
        extensions,
        auto_opens: response.signature.auto_opens.clone(),
    }
    .sorted();
    // FCS's own view of the in-memory assembly, when it imports it, reads
    // the same entities.
    let mut theirs: Vec<String> = response
        .entities
        .iter()
        .map(|e| {
            format!(
                "{} | {} | {} ({}) | {:?} | public={} auto_open={} extension={}",
                e.namespace,
                e.enclosing.join("+"),
                e.logical_name,
                e.compiled_name,
                e.kind,
                e.access == borzoi_oracle_harness::assembly_entities::FcsAccess::Public,
                e.auto_open,
                e.extension
            )
        })
        .collect();
    let mut decoded: Vec<String> = memory
        .entities
        .iter()
        .filter(|r| r.kind != borzoi_assembly::existence::PickledEntityKind::Namespace)
        .map(|r| {
            format!(
                "{} | {} | {} ({}) | {:?} | public={} auto_open={} extension={}",
                r.namespace.join("."),
                r.enclosing.join("+"),
                r.logical_name,
                r.compiled_name,
                r.kind,
                r.public,
                r.auto_open,
                r.extension
            )
        })
        .collect();
    theirs.sort();
    decoded.sort();
    assert!(
        response.imported || !errors.is_empty(),
        "{}: FCS imported nothing of a clean producer",
        cell.name
    );
    assert!(
        !response.imported || decoded == theirs,
        "{}: the decoded in-memory signature is not FCS's view of it\n  decoded: {decoded:#?}\n  FCS: {theirs:#?}",
        cell.name
    );
    assert!(
        response.read_errors.is_empty(),
        "{}: FCS could not read {:?}",
        cell.name,
        response.read_errors
    );
    // D1 in rows: the DLL FCS compiles from the same arguments reads the same.
    if errors.is_empty() {
        let line = fixture
            .compile_request(&plain(PRODUCER), &framework, &BTreeMap::new());
        let out: CompileResponse = request(line.as_line()).expect("compile the producer");
        let dll = out
            .output
            .unwrap_or_else(|| panic!("{}: compile failed: {:?}", cell.name, out.diagnostics));
        let bytes = std::fs::read(&dll).expect("read the DLL");
        let assembly = Ecma335Assembly::parse(&bytes).expect("parse the DLL");
        let index = assembly.existence_index().expect("existence index");
        let PickleLayer::Read(rows) = index.pickle else {
            panic!("{}: the DLL's pickle is {:?}", cell.name, index.pickle);
        };
        let dll_rows = Rows {
            entities: rows,
            extensions: index
                .extensions
                .into_iter()
                .filter(|r| r.layer == IndexLayer::Pickle)
                .collect(),
            auto_opens: assembly.assembly_auto_opens().expect("auto-opens"),
        }
        .sorted();
        assert_eq!(
            dll_rows, memory,
            "{}: D1 in rows: the compiled DLL and the in-memory signature differ",
            cell.name
        );
    }
    // What a dependant reads: nothing of a producer FCS does not import.
    let memory = if response.imported {
        memory
    } else {
        Rows {
            entities: Vec::new(),
            extensions: Vec::new(),
            auto_opens: Vec::new(),
        }
    };
    Fcs {
        memory,
        clean: errors.is_empty(),
        errors,
    }
}

/// Our reading of `cell` under `routes`, or how it declines.
pub fn ours(cell: &Cell, routes: Option<&MarkerRoutes>) -> (SourceExistence, MarkerRoutes) {
    let symbols: HashSet<String> = cell.defines.iter().cloned().collect();
    let dir = PathBuf::from("/fixture");
    let mut files = Vec::new();
    let mut recoveries = Vec::new();
    for (name, text) in &cell.files {
        let kind = if name.ends_with(".fsi") {
            FileKind::Sig
        } else {
            FileKind::Impl
        };
        let parse = parse_with_options(
            text,
            ParseOptions {
                file_kind: kind,
                symbols: &symbols,
                lang: borzoi_cst::language_version::LanguageVersion::V10_0,
            },
        );
        recoveries.push(SyntaxRecovery::of(&parse));
        files.push(match kind {
            FileKind::Sig => SourceFile::Sig(SigFile::cast(parse.root).expect("a sig root")),
            _ => SourceFile::Impl(ImplFile::cast(parse.root).expect("an impl root")),
        });
    }
    let paths: Vec<PathBuf> = cell.files.iter().map(|(n, _)| dir.join(n)).collect();
    let project: Vec<ProjectFile> = files
        .iter()
        .cloned()
        .zip(recoveries)
        .zip(qualified_names(&files, &paths))
        .map(|((f, r), q)| ProjectFile::new(f, q, r))
        .collect();
    let refs: Vec<&ProjectFile> = project.iter().collect();
    let routes = match routes {
        Some(r) => r.clone(),
        None => certificate(cell, &refs),
    };
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    (
        source_existence(Producer::Evaluated {
            items: &items,
            routes: &routes,
        }),
        routes,
    )
}

fn certificate(cell: &Cell, files: &[&ProjectFile]) -> MarkerRoutes {
    let MarkerRoutes::Certified(mut map) = certify_by_spelling(files) else {
        unreachable!("by spelling is a certificate")
    };
    if let Certificate::Override(names) = &cell.certificate {
        for (name, markers) in names {
            let key: Vec<String> = name.split('.').map(str::to_owned).collect();
            map.insert(key, markers.iter().copied().collect());
        }
    }
    MarkerRoutes::Certified(map)
}

/// Whether `ours` holds every row of `theirs`, as multisets; the rows of
/// `theirs` it lacks otherwise.
fn missing<T: Ord + Clone + std::fmt::Debug>(ours: &[T], theirs: &[T]) -> Vec<T> {
    let mut count: BTreeMap<&T, i64> = BTreeMap::new();
    for r in ours {
        *count.entry(r).or_default() += 1;
    }
    let mut lacking = Vec::new();
    for r in theirs {
        let n = count.entry(r).or_default();
        *n -= 1;
        if *n < 0 {
            lacking.push(r.clone());
        }
    }
    lacking
}

/// One indented line per row.
fn lines<T: std::fmt::Debug>(rows: &[T]) -> String {
    rows.iter().map(|r| format!("    {r:?}\n")).collect()
}

/// Grade `ours` against FCS's rows: the verdict, or why a property fails.
pub fn grade(cell: &Cell, fcs: &Fcs, ours: &SourceExistence) -> Result<String, String> {
    let surface = match ours {
        SourceExistence::Unread(why) => return Ok(format!("unread {why:?}")),
        SourceExistence::Read(s) => s,
    };
    let PickleLayer::Read(rows) = &surface.index.pickle else {
        return Err("a Read surface has no read pickle".to_owned());
    };
    let mine = Rows {
        entities: rows.clone(),
        extensions: surface.index.extensions.clone(),
        auto_opens: surface.assembly_auto_opens.clone(),
    }
    .sorted();
    let theirs = &fcs.memory;
    let lacking_entities = missing(&mine.entities, &theirs.entities);
    let lacking_extensions = missing(&mine.extensions, &theirs.extensions);
    let lacking_opens = missing(&mine.auto_opens, &theirs.auto_opens);
    if !lacking_entities.is_empty() || !lacking_extensions.is_empty() || !lacking_opens.is_empty()
    {
        return Err(format!(
            "{}: ours does not cover FCS's rows (approximations {:?})\n  FCS has, ours lacks:\n{}{}    auto-opens {lacking_opens:?}\n  ours:\n{}{}",
            cell.name,
            surface.approximations,
            lines(&lacking_entities),
            lines(&lacking_extensions),
            lines(&mine.entities),
            lines(&mine.extensions),
        ));
    }
    if !fcs.clean {
        return Ok(format!("covers, FCS rejects ({:?})", surface.approximations));
    }
    if surface.approximations.is_empty() {
        if mine != *theirs {
            return Err(format!(
                "{}: no approximation named, yet ours is not FCS's\n  ours has, FCS lacks:\n{}{}    ours auto-opens {:?}, FCS's {:?}",
                cell.name,
                lines(&missing(&theirs.entities, &mine.entities)),
                lines(&missing(&theirs.extensions, &mine.extensions)),
                mine.auto_opens,
                theirs.auto_opens
            ));
        }
        Ok("exact".to_owned())
    } else {
        let names: Vec<String> = surface
            .approximations
            .iter()
            .map(|a| format!("{a:?}"))
            .collect();
        Ok(format!("covers [{}]", names.join(",")))
    }
}

/// Grade every cell under its certificate and under `Unknown`: the manifest
/// entries, and every failure.
pub fn grade_cells(cells: &[Cell]) -> (Vec<(String, String)>, Vec<String>) {
    let results = borzoi_oracle_harness::par_map::par_map(cells.len(), |i| {
        let cell = &cells[i];
        // A cell's panic (an oracle invariant) is its own failure, not the
        // run's: every other cell is still graded.
        let graded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let fcs = fcs(cell);
            let (certified, _) = ours(cell, None);
            let (unknown, _) = ours(cell, Some(&MarkerRoutes::Unknown));
            let c = grade(cell, &fcs, &certified);
            let u = grade(cell, &fcs, &unknown);
            (c, u, fcs.errors.clone())
        }));
        match graded {
            Ok((c, u, errors)) => (cell.name.clone(), c, u, errors),
            Err(panic) => {
                let message = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                    .unwrap_or_default();
                let e = Err(format!("{}: panicked: {message}", cell.name));
                (cell.name.clone(), e.clone(), e, Vec::new())
            }
        }
    });
    let mut entries = Vec::new();
    let mut failures = Vec::new();
    for (name, c, u, errors) in results {
        match (&c, &u) {
            (Ok(c), Ok(u)) => {
                let fcs_errors = if errors.is_empty() { String::new() } else { format!(" [FCS: {}]", errors.join(",")) };
                entries.push((name, format!("certified: {c}; unknown: {u}{fcs_errors}")));
            }
            _ => {
                if let Err(e) = c {
                    failures.push(format!("certified: {e}"));
                }
                if let Err(e) = u {
                    failures.push(format!("unknown: {e}"));
                }
            }
        }
    }
    (entries, failures)
}

/// The hand-written grid of declaration forms.
fn grid() -> Vec<Cell> {
    crate::source_existence_grid::cells()
}

#[test]
fn source_rows_are_fcs_rows_over_the_grid() {
    let cells = grid();
    let (entries, failures) = grade_cells(&cells);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "source_existence_diff",
        &manifest,
        &regenerate("source_existence_diff::source_rows_are_fcs_rows_over_the_grid"),
    );
}
