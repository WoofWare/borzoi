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

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::PathBuf;

use borzoi_assembly::existence::{
    ExistenceIndex, ExtensionRow, IndexLayer, PickleLayer, PickledEntityRow,
};
use borzoi_assembly::{Ecma335Assembly, EcmaView};
use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_cst::syntax::{AstNode, ImplFile, SigFile};
use borzoi_oracle_harness::assembly_entities::{ExtensionStyle, FcsExtensionMember};
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::{
    CompileResponse, FixtureFile, FixtureProject, PlainName, ProjectGraphFixture,
    ReferencedResponse, Target, framework_references, parse_response,
};
use borzoi_sema::test_support::{ExistenceFacts, existence_facts};
use borzoi_sema::{
    CompileItem, ExistenceUnread, Marker, MarkerRoutes, Producer, ProjectFile, ProviderReferences,
    SourceExistence, SourceFile, SyntaxRecovery, certify_by_spelling, qualified_names,
    source_existence,
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
    /// The hostile dimensions mixed into the cell's source.
    pub hostile: crate::source_existence_gen::Hostile,
    /// Whether the walk is told a reference may be a type provider.
    pub providers_possible: bool,
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
            hostile: Default::default(),
            providers_possible: false,
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
    /// The entities of a clean A whose members FCS's view could not read.
    pub view_unread: Vec<String>,
    /// Why the oracle describes no CCU for A, where it refuses.
    pub refused: Option<Refusal>,
}

/// Why the oracle describes no CCU for a producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    /// FCS reads A from its DLL (a type provider), not from source.
    ReadsDll,
    /// A source holds a `#r` or `#load` fsc acts on.
    NamesUnreadCode,
    /// A's check fails and FCS builds it no assembly data, which it also
    /// does for a type provider, and a source may name one: whether FCS would
    /// read A from its DLL cannot be told, so A is not graded.
    MayReadDll,
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
/// FCS's own view of a producer's extension members as rows: a lower bound
/// on the rows its signature holds, for a signature the decoder cannot read.
/// Each row names only what FCS reports (its logical and compiled name), and
/// a C#-style accessor is left out, since FCS's view lists every accessor of
/// a property one of whose accessors is marked and the signature marks only
/// that one.
fn view_extension_rows(members: &[FcsExtensionMember]) -> Vec<ExtensionRow> {
    members
        .iter()
        .filter(|m| {
            m.style != ExtensionStyle::Csharp
                || !["get_", "set_"]
                    .iter()
                    .any(|p| m.logical_name.starts_with(p))
        })
        .map(|m| {
            let mut names = vec![m.logical_name.clone(), m.compiled_name.clone()];
            names.sort();
            names.dedup();
            ExtensionRow {
                layer: IndexLayer::Pickle,
                namespace: if m.namespace.is_empty() {
                    Vec::new()
                } else {
                    m.namespace.split('.').map(str::to_owned).collect()
                },
                enclosing: m.enclosing.clone(),
                names,
                instance: Some(m.is_instance),
            }
        })
        .collect()
}

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
    let response: ReferencedResponse = match request(&line) {
        Ok(r) => r,
        // FCS reads a type-provider assembly from its DLL, never from its
        // source; and a source with a `#r` or `#load` fsc acts on names code
        // the check does not read. The walk must decline either.
        Err(e)
            if e.contains("FCS reads it from its DLL")
                || e.contains("FCS may read it from its DLL")
                || e.contains("names code the project check does not read") =>
        {
            return Fcs {
                memory: Rows {
                    entities: Vec::new(),
                    extensions: Vec::new(),
                    auto_opens: Vec::new(),
                },
                undecodable: false,
                clean: true,
                errors: Vec::new(),
                compile_errors: Vec::new(),
                view_unread: Vec::new(),
                refused: Some(if e.contains("FCS reads it from its DLL") {
                    Refusal::ReadsDll
                } else if e.contains("FCS may read it from its DLL") {
                    Refusal::MayReadDll
                } else {
                    Refusal::NamesUnreadCode
                }),
            };
        }
        Err(e) => panic!("{}: referenced: {e}", cell.name),
    };
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
    // to a DLL). Its entities and extension rows are then graded by FCS's
    // own view of them: the extension rows only as a lower bound
    // ([`view_extension_rows`]), so its surplus counts against less than the
    // signature holds. So are those of a clean producer whose
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
                    (
                        response.entities.iter().map(fcs_row).collect(),
                        view_extension_rows(&response.extension_members),
                    )
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
    // FCS's view may fail to read an entity's members (its API throws on a
    // class with a constructor in a `module rec` that also holds an
    // `[<Extension>]` `let`). The rows are graded from the decoded
    // signature regardless; only the cross-check below loses that entity, so
    // each such entity is pinned in the cell's verdict.
    let view_unread: Vec<String> = response
        .read_errors
        .iter()
        .filter(|_| errors.is_empty())
        .map(|e| e.split(':').next().unwrap_or(e).trim().to_owned())
        .collect();
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
    // The compile op refuses a source that may hold a line directive (its
    // diagnostics' ranges would move): such a producer has no DLL to hold the
    // signature to, and its D1 is not checked.
    let compiled: Option<CompileResponse> = if errors.is_empty() {
        let line = fixture.compile_request(&plain(PRODUCER), &framework, &BTreeMap::new());
        match request(line.as_line()) {
            Ok(out) => Some(out),
            Err(e) if e.contains("may hold a line directive") => None,
            Err(e) => panic!("compile the producer: {e}"),
        }
    } else {
        None
    };
    if let Some(out) = compiled {
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
        // The assembly-level auto-opens are read apart from the pickle, so
        // they are held to each other even where neither pickle decodes.
        assert_eq!(
            dll_rows.auto_opens, memory.auto_opens,
            "{}: D1: the compiled DLL's assembly auto-opens and the in-memory signature's differ",
            cell.name
        );
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
        view_unread,
        refused: None,
    }
}

/// Our reading of `cell` under `routes`, or how it declines.
/// `cell`'s files, parsed as the walk reads them.
fn project_files(cell: &Cell) -> Vec<ProjectFile> {
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
    project
}

/// Our reading of `cell` under `routes`, or certified by spelling.
pub fn ours(cell: &Cell, routes: Option<&MarkerRoutes>) -> (SourceExistence, MarkerRoutes) {
    ours_with(cell, routes, |walk| walk())
}

/// [`ours`], with the walk itself (and nothing that prepares its input)
/// run inside `around`: what a test that observes the walk alone wraps.
pub fn ours_with(
    cell: &Cell,
    routes: Option<&MarkerRoutes>,
    around: impl FnOnce(&mut dyn FnMut() -> SourceExistence) -> SourceExistence,
) -> (SourceExistence, MarkerRoutes) {
    let project = project_files(cell);
    let refs: Vec<&ProjectFile> = project.iter().collect();
    let routes = match routes {
        Some(r) => r.clone(),
        None => certificate(cell, &refs),
    };
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    // A reference that may be a type provider is one whose source names the
    // attribute that makes it one.
    let providers = if cell.providers_possible
        || cell.refs.iter().any(|r| {
            r.files
                .iter()
                .any(|(_, t)| t.contains("TypeProviderAssembly"))
        }) {
        ProviderReferences::Possible
    } else {
        ProviderReferences::None
    };
    let read = around(&mut || {
        source_existence(Producer::Evaluated {
            items: &items,
            routes: &routes,
            providers,
        })
    });
    (read, routes)
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

/// One indented line per row.
fn lines<T: std::fmt::Debug>(rows: &[T]) -> String {
    rows.iter().map(|r| format!("    {r:?}\n")).collect()
}

/// Grade `ours` against FCS's rows: the verdict, or why a property fails.
pub fn grade(cell: &Cell, fcs: &Fcs, ours: &SourceExistence) -> Result<String, String> {
    match (fcs.refused, ours) {
        (None, _) => {}
        (Some(Refusal::MayReadDll), _) => {
            return Ok("ungraded: its check fails, and FCS may read its DLL".to_owned());
        }
        (Some(Refusal::ReadsDll), SourceExistence::Unread(ExistenceUnread::TypeProvider(_))) => {
            return Ok("unread TypeProvider, FCS reads the DLL".to_owned());
        }
        (
            Some(Refusal::NamesUnreadCode),
            SourceExistence::Unread(ExistenceUnread::HashReference(_)),
        ) => return Ok("unread HashReference, a source names code".to_owned()),
        (Some(why), other) => {
            return Err(format!(
                "{}: the oracle refuses A ({why:?}), and ours is {other:?}",
                cell.name
            ));
        }
    }
    let surface = match ours {
        SourceExistence::Unread(why) => return Ok(format!("unread {why:?}")),
        SourceExistence::Read(s) => s,
    };
    // Both sides as the entity questions read them: the facts of the set
    // each index builds, by the code every question runs. The extension
    // facts are A's `ExtensionNames`', graded by the gate grids, not here.
    let mine = existence_facts(&surface.index(), &surface.assembly_auto_opens);
    let theirs = existence_facts(
        &ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(fcs.memory.entities.clone()),
            extensions: Vec::new(),
        },
        &fcs.memory.auto_opens,
    );
    let lacking: Vec<String> = facts_lacking(&mine, &theirs);
    if !lacking.is_empty() {
        let state = if fcs.clean {
            "FCS accepts it"
        } else {
            "FCS rejects it"
        };
        return Err(format!(
            "{}: {state}, and ours lacks facts FCS's CCU holds (approximations {:?})\n{}",
            cell.name,
            surface.approximations,
            lines(&lacking)
        ));
    }
    // The fold's own reading of the same files: every module it declares and
    // every type it places is one of ours, on a producer FCS accepts.
    if fcs.clean {
        let fold = borzoi_sema::test_support::fold_entity_paths(&project_files(cell));
        let missing: Vec<String> = fold
            .difference(&mine.entities)
            .map(|p| p.join("."))
            .collect();
        if !missing.is_empty() {
            return Err(format!(
                "{}: the resolver's fold declares entities ours lacks: {missing:?}",
                cell.name
            ));
        }
    }
    let surplus = Surplus::of(&mine, &theirs);
    let state = match (fcs.clean, fcs.undecodable) {
        (true, false) => "",
        (true, true) => ", FCS's signature undecodable (#1081)",
        (false, false) => ", FCS rejects",
        (false, true) => ", FCS rejects, its signature undecodable",
    };
    let names: Vec<String> = surface
        .approximations
        .iter()
        .map(|a| format!("{a:?}"))
        .collect();
    if surplus.is_zero() {
        Ok(format!("exact{state} [{}]", names.join(",")))
    } else {
        Ok(format!("covers{state} {surplus} [{}]", names.join(",")))
    }
}

/// Every entity fact of `theirs` that `mine` lacks: the facts open
/// certification reads.
fn facts_lacking(mine: &ExistenceFacts, theirs: &ExistenceFacts) -> Vec<String> {
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
        "auto-open",
        &mine.auto_open_bases,
        &theirs.auto_open_bases,
    ));
    lacking
}

/// How many entity facts ours holds beyond FCS's, per kind: what the
/// superset costs open certification.
struct Surplus {
    prefixes: usize,
    entities: usize,
    lends: usize,
    auto_opens: usize,
}

impl Surplus {
    fn of(mine: &ExistenceFacts, theirs: &ExistenceFacts) -> Surplus {
        let n = |a: &BTreeSet<Vec<String>>, b: &BTreeSet<Vec<String>>| a.difference(b).count();
        Surplus {
            prefixes: n(&mine.prefixes, &theirs.prefixes),
            entities: n(&mine.entities, &theirs.entities),
            lends: n(&mine.lends_children, &theirs.lends_children)
                + n(&mine.lends_anything, &theirs.lends_anything),
            auto_opens: n(&mine.auto_open_bases, &theirs.auto_open_bases),
        }
    }

    fn is_zero(&self) -> bool {
        self.prefixes + self.entities + self.lends + self.auto_opens == 0
    }
}

impl std::fmt::Display for Surplus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "surplus(prefix {}, entity {}, lends {}, auto-open {})",
            self.prefixes, self.entities, self.lends, self.auto_opens
        )
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
            errors.extend(fcs.view_unread.iter().map(|e| format!("view-unread {e}")));
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

/// The grid's cells whose names start with one of `BORZOI_SOURCE_EXISTENCE_CELL`'s
/// comma-separated prefixes,
/// graded without the manifest: the inner loop on a handful of cells.
#[test]
#[ignore = "an inner-loop aid; set BORZOI_SOURCE_EXISTENCE_CELL"]
fn grid_cells_by_name() {
    let prefix = std::env::var("BORZOI_SOURCE_EXISTENCE_CELL").unwrap_or_default();
    let cells: Vec<Cell> = grid()
        .into_iter()
        .filter(|c| prefix.split(",").any(|p| c.name.starts_with(p)))
        .collect();
    let (entries, failures) = grade_cells(&cells);
    for e in &entries {
        println!("{e:?}");
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
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

/// The `referenced` op describes the producer under exactly the references
/// the request names: a producer FCS checks against an assembly the request
/// does not give it (here, the consumer's `System.Runtime` reaching it) is
/// refused, not reported.
#[test]
fn the_referenced_op_refuses_a_producer_checked_against_other_references() {
    use borzoi_oracle_harness::project_graph::{GraphProject, GraphRequest, Reference};
    let framework = framework_references();
    let without_runtime: Vec<Reference> = framework
        .iter()
        .filter(|p| p.file_name().is_none_or(|n| n != "System.Runtime.dll"))
        .cloned()
        .map(Reference::Dll)
        .collect();
    assert!(
        without_runtime.len() < framework.len(),
        "the framework set holds System.Runtime.dll"
    );
    let producer_source = crate::common::temp_fs_file(
        "referenced_producer",
        "module RefProducer\nlet f (s: string) = s\n",
    );
    let consumer_source = crate::common::temp_fs_file(
        "referenced_consumer",
        "module RefConsumer\nlet x = RefProducer.f \"x\"\n",
    );
    let mut consumer_refs: Vec<Reference> = framework.iter().cloned().map(Reference::Dll).collect();
    consumer_refs.push(Reference::Project(plain("Producer")));
    let request = GraphRequest::new(
        vec![
            GraphProject {
                id: plain("Producer"),
                assembly_name: plain("RefProducer"),
                target: Target::Library,
                sources: vec![producer_source],
                defines: Vec::new(),
                references: without_runtime,
            },
            GraphProject {
                id: plain("Consumer"),
                assembly_name: plain("RefConsumer"),
                target: Target::Library,
                sources: vec![consumer_source],
                defines: Vec::new(),
                references: consumer_refs,
            },
        ],
        plain("Consumer"),
    )
    .expect("a valid graph request");
    let line = request
        .referenced_line(&plain("Producer"))
        .expect("the consumer references the producer");
    let answer = request_referenced(&line);
    assert!(
        answer.as_ref().is_err_and(|e| e.contains("does not name")),
        "the oracle answered a producer checked against other references: {answer:?}"
    );
}

fn request_referenced(line: &str) -> Result<ReferencedResponse, String> {
    request(line)
}
