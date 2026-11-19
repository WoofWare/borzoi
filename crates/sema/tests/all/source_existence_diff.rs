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

use borzoi_assembly::existence::{
    ExtensionRow, IndexLayer, PickleLayer, PickledEntityKind, PickledEntityRow,
};
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
    /// Whether A's check failed and FCS's recovered signature does not
    /// decode, so `memory` holds FCS's view of its entities alone.
    pub undecodable: bool,
    /// Whether A checked with no error.
    pub clean: bool,
    pub errors: Vec<String>,
    /// The errors of FCS's compile of a clean A, which then wrote no DLL.
    pub compile_errors: Vec<String>,
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
fn decode(
    primary: &[u8],
    b: Option<&[u8]>,
) -> Result<(Vec<PickledEntityRow>, Vec<ExtensionRow>), String> {
    let ccu = borzoi_assembly::unpickle_signature(primary, b).map_err(|e| e.to_string())?;
    borzoi_assembly::existence::pickled_rows(&ccu)
}

/// FCS's view of one entity as an existence row.
fn fcs_row(e: &borzoi_oracle_harness::assembly_entities::FcsEntity) -> PickledEntityRow {
    use borzoi_assembly::existence::PickledEntityKind;
    use borzoi_oracle_harness::assembly_entities::FcsEntityKind;
    PickledEntityRow {
        namespace: if e.namespace.is_empty() {
            Vec::new()
        } else {
            e.namespace.split('.').map(str::to_owned).collect()
        },
        enclosing: e.enclosing.clone(),
        logical_name: e.logical_name.clone(),
        compiled_name: e.compiled_name.clone(),
        kind: match e.kind {
            FcsEntityKind::Module => PickledEntityKind::Module,
            FcsEntityKind::Abbreviation => PickledEntityKind::Abbreviation,
            FcsEntityKind::Exception => PickledEntityKind::Exception,
            FcsEntityKind::Measure => PickledEntityKind::Measure,
            FcsEntityKind::Type => PickledEntityKind::Type,
        },
        public: e.access == borzoi_oracle_harness::assembly_entities::FcsAccess::Public,
        auto_open: e.auto_open,
        extension: e.extension,
    }
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
        let line =
            fixture.compile_request(&plain(r.name), framework_references(), &BTreeMap::new());
        let out: CompileResponse = request(line.as_line()).expect("compile a reference");
        let dll = out.output.unwrap_or_else(|| {
            panic!(
                "{}: reference {} failed: {:?}",
                cell.name, r.name, out.diagnostics
            )
        });
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
    let errors: Vec<String> = response
        .errors()
        .map(|d| format!("FS{}", d["ErrorNumber"]))
        .collect();
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
    // A producer FCS builds no assembly data for, or does not import, is one
    // a dependant reads nothing of: its signature (a check that failed) is
    // not graded.
    //
    // A producer whose check fails may still be imported, with a recovered
    // signature `unpickle_signature` need not read (no compiler writes one
    // to a DLL). Its entities are then graded by FCS's own view of them, and
    // its extension rows not at all. So are those of a clean producer whose
    // signature the decoder cannot read, provided the DLL FCS compiles fails
    // it identically (a decoder gap, #1081, not an in-memory layout).
    let mut undecodable = false;
    let mut decode_error: Option<String> = None;
    let (entities, extensions) = match streams.first() {
        _ if !response.imported => (Vec::new(), Vec::new()),
        None => (Vec::new(), Vec::new()),
        Some(s) => {
            let primary = s.primary_bytes().expect("hex");
            let b = s.b_bytes().expect("hex");
            match decode(&primary, b.as_deref()) {
                Ok(rows) => rows,
                Err(e) => {
                    if errors.is_empty() {
                        decode_error = Some(e);
                    }
                    undecodable = true;
                    (response.entities.iter().map(fcs_row).collect(), Vec::new())
                }
            }
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
        !response.imported || undecodable || decoded == theirs,
        "{}: the decoded in-memory signature is not FCS's view of it\n  decoded: {decoded:#?}\n  FCS: {theirs:#?}",
        cell.name
    );
    assert!(
        response.read_errors.is_empty() || !errors.is_empty(),
        "{}: FCS could not read {:?}",
        cell.name,
        response.read_errors
    );
    // And every extension member FCS reads is a decoded row, as
    // `assembly_entities_diff` holds a DLL's (one way only: FCS's view lists
    // no class `let`, whose val the pickle holds).
    if response.imported && !undecodable {
        let index = borzoi_assembly::existence::ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(memory.entities.clone()),
            extensions: memory.extensions.clone(),
        };
        let failures = crate::assembly_entities_diff::pickle_extension_failures(
            &index,
            &response.extension_members,
            false,
        );
        assert!(
            failures.is_empty(),
            "{}: the decoded extension rows are not FCS's view of them\n{}",
            cell.name,
            failures.join("\n")
        );
    }
    // D1 in rows: the DLL FCS compiles from the same arguments reads the same.
    // A check can pass where the compile fails (two types given one
    // compiled name): there is then no DLL to hold the signature to.
    let mut compile_errors = Vec::new();
    let mut compile_output: Option<PathBuf> = None;
    if errors.is_empty() {
        let line = fixture.compile_request(&plain(PRODUCER), &framework, &BTreeMap::new());
        let out: CompileResponse = request(line.as_line()).expect("compile the producer");
        compile_errors = out
            .errors()
            .map(|d| format!("FS{}", d["ErrorNumber"]))
            .collect();
        assert!(
            out.output.is_some() || !compile_errors.is_empty(),
            "{}: the compile wrote no DLL and reported no error",
            cell.name
        );
        compile_output = out.output;
    }
    if let Some(dll) = compile_output.filter(|_| compile_errors.is_empty()) {
        let bytes = std::fs::read(&dll).expect("read the DLL");
        let assembly = Ecma335Assembly::parse(&bytes).expect("parse the DLL");
        let index = assembly.existence_index().expect("existence index");
        let rows = match (index.pickle, &decode_error) {
            (PickleLayer::Read(rows), None) => rows,
            (PickleLayer::Unreadable(dll), Some(memory)) if dll == *memory => Vec::new(),
            (pickle, _) => panic!(
                "{}: the DLL's pickle is {pickle:?}, the in-memory one's decode {decode_error:?}",
                cell.name
            ),
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
        assert!(
            decode_error.is_some() || dll_rows == memory,
            "{}: D1 in rows: the compiled DLL and the in-memory signature differ\n  DLL: {dll_rows:#?}\n  memory: {memory:#?}",
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
        undecodable,
        clean: errors.is_empty(),
        errors,
        compile_errors,
    }
}

/// Our reading of `cell` under `routes`, or how it declines.
pub fn ours(cell: &Cell, routes: Option<&MarkerRoutes>) -> (SourceExistence, MarkerRoutes) {
    // FCS defines `COMPILED` in every compiled project (the LSP does too).
    let symbols: HashSet<String> = cell
        .defines
        .iter()
        .cloned()
        .chain(std::iter::once("COMPILED".to_owned()))
        .collect();
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
    // A producer FCS rejects: its imported surface is FCS's recovery, whose
    // kinds and flags the walk does not model exactly. Ours must still cover
    // every fact an existence question reads of it, in the direction that
    // answers "something may be there" more often: every entity's place and
    // names, with its `[<AutoOpen>]` and `[<Extension>]` flags and its being
    // an abbreviation (what `ExistenceSet` lends names by) where FCS's has
    // them; every extension's place and names, of either staticness where
    // FCS's says; every auto-open path.
    if !fcs.clean {
        let covers_entity = |f: &PickledEntityRow| {
            mine.entities.iter().any(|r| {
                (
                    &r.namespace,
                    &r.enclosing,
                    &r.logical_name,
                    &r.compiled_name,
                ) == (
                    &f.namespace,
                    &f.enclosing,
                    &f.logical_name,
                    &f.compiled_name,
                ) && (r.auto_open || !f.auto_open)
                    && (r.extension || !f.extension)
                    && (f.kind != PickledEntityKind::Abbreviation
                        || r.kind == PickledEntityKind::Abbreviation)
            })
        };
        let covers_extension = |f: &ExtensionRow| {
            mine.extensions.iter().any(|r| {
                (&r.namespace, &r.enclosing, &r.names) == (&f.namespace, &f.enclosing, &f.names)
                    && (r.instance.is_none() || r.instance == f.instance)
            })
        };
        let lacking: Vec<String> = theirs
            .entities
            .iter()
            .filter(|f| !covers_entity(f))
            .map(|f| format!("{f:?}"))
            .chain(
                theirs
                    .extensions
                    .iter()
                    .filter(|f| !covers_extension(f))
                    .map(|f| format!("{f:?}")),
            )
            .chain(
                theirs
                    .auto_opens
                    .iter()
                    .filter(|p| !mine.auto_opens.contains(p))
                    .map(|p| format!("auto-open {p}")),
            )
            .collect();
        if !lacking.is_empty() {
            return Err(format!(
                "{}: FCS rejects it, and ours does not cover the facts of its recovered surface\n{}",
                cell.name,
                lines(&lacking)
            ));
        }
        let undecodable = if fcs.undecodable {
            ", its signature undecodable"
        } else {
            ""
        };
        return Ok(format!(
            "covers recovered facts, FCS rejects{undecodable} ({:?})",
            surface.approximations
        ));
    }
    let lacking_entities = missing(&mine.entities, &theirs.entities);
    let lacking_extensions = missing(&mine.extensions, &theirs.extensions);
    let lacking_opens = missing(&mine.auto_opens, &theirs.auto_opens);
    if !lacking_entities.is_empty() || !lacking_extensions.is_empty() || !lacking_opens.is_empty() {
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
    if fcs.clean && fcs.undecodable {
        return Ok(format!(
            "covers FCS's entities, the signature undecodable (#1081) ({:?})",
            surface.approximations
        ));
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
            let mut errors = fcs.errors.clone();
            errors.extend(fcs.compile_errors.iter().map(|e| format!("compile {e}")));
            (c, u, errors)
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
                let fcs_errors = if errors.is_empty() {
                    String::new()
                } else {
                    format!(" [FCS: {}]", errors.join(","))
                };
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

/// The cells the generator makes from seeds `first..first + count`.
fn generated(first: u64, count: u64) -> Vec<Cell> {
    (first..first + count)
        .map(crate::source_existence_gen::cell)
        .collect()
}

/// The pinned default run of the generator: its seeds are fixed, so each
/// case's verdict is pinned in `source_existence_gen.txt`.
#[test]
fn source_rows_are_fcs_rows_over_generated_projects() {
    let cells = generated(0, 60);
    let (entries, failures) = grade_cells(&cells);
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
        &regenerate("source_existence_diff::source_rows_are_fcs_rows_over_generated_projects"),
    );
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
    let cells = generated(first, count);
    let (entries, failures) = grade_cells(&cells);
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
    let cell = crate::source_existence_gen::cell(seed);
    for (name, text) in &cell.files {
        eprintln!("--- {name}\n{text}");
    }
    let (ours, _) = ours(&cell, None);
    match &ours {
        SourceExistence::Unread(why) => eprintln!("ours: unread {why:?}"),
        SourceExistence::Read(s) => eprintln!("ours: read, {:?}", s.approximations),
    }
    let fcs = fcs(&cell);
    eprintln!("FCS errors: {:?}", fcs.errors);
}

/// Every name the walk takes as a type FSharp.Core declares in a namespace
/// every file has open is one: an abbreviation or a type of
/// `Microsoft.FSharp.Core`, by FSharp.Core's own pickle.
#[test]
fn the_fsharp_core_type_names_are_fsharp_core_types() {
    let core = crate::common::ensure_fsharp_core_dll();
    let bytes = std::fs::read(core).expect("read FSharp.Core.dll");
    let index = Ecma335Assembly::parse(&bytes)
        .and_then(|a| a.existence_index())
        .expect("FSharp.Core's existence index");
    let PickleLayer::Read(rows) = index.pickle else {
        panic!("FSharp.Core's pickle is {:?}", index.pickle);
    };
    let declared: Vec<&str> = rows
        .iter()
        .filter(|r| {
            r.namespace == ["Microsoft", "FSharp", "Core"]
                && r.enclosing.is_empty()
                && r.public
                && matches!(
                    r.kind,
                    borzoi_assembly::existence::PickledEntityKind::Abbreviation
                        | borzoi_assembly::existence::PickledEntityKind::Type
                )
        })
        .map(|r| r.logical_name.as_str())
        .collect();
    for name in borzoi_sema::test_support::fsharp_core_type_names() {
        assert!(
            declared.contains(name),
            "{name} is no public type of Microsoft.FSharp.Core"
        );
    }
}
