//! The project-graph oracle's `referenced` op, read: what FCS reads of a
//! producer project from source, in the currency of
//! `borzoi_assembly::existence` (pickle entity rows, pickle extension rows,
//! assembly-level `AutoOpen` paths), or why that reading is unknown.
//!
//! [`read`] asks the oracle about one [`GraphCell`] and holds the answer to
//! three things before returning it. Any disagreement panics: it is a defect
//! of the oracle or of the decoder, not of a subject.
//!
//! - **The decoded signature is FCS's view.** The streams that cross the
//!   `FSharpReference` boundary, decoded by
//!   `borzoi_assembly::unpickle_signature`, name exactly the entities FCS's
//!   own view of the imported assembly lists (`FSharpAssembly.Contents`), and
//!   every extension member that view lists is a decoded row.
//! - **D1 in rows.** The DLL FCS compiles from the same argument vector reads
//!   the same entity and extension rows. Its assembly-level auto-opens may
//!   differ from the in-memory list: FCS takes an assembly attribute for
//!   `AutoOpen` by its owner's identity in memory (`classifyAssemblyAttrib`)
//!   and by its owner's name in a DLL (`TryFindAutoOpenAttr`). The split is
//!   reported ([`D1::Held`]) for the caller to pin, not excused.
//! - **No fallback.** A signature the decoder cannot read is
//!   [`Unknown::Undecodable`]. FCS's view never stands in for it, and the DLL
//!   FCS compiles must fail the decoder identically, or the in-memory layout
//!   differs from the one compilers write and the reader panics.

use borzoi_assembly::existence::{
    ExistenceIndex, ExtensionRow, IndexLayer, PickleLayer, PickledEntityKind, PickledEntityRow,
};
use borzoi_assembly::{Ecma335Assembly, EcmaView};
use borzoi_cst::language_version::LanguageVersion;
use borzoi_cst::parser::{FileKind, Parse, ParseOptions, parse_with_options};
use borzoi_oracle_harness::assembly_entities::FcsAccess;
use borzoi_oracle_harness::project_graph::{
    CompileResponse, GraphCell, PreparedCell, ReferencedFound, ReferencedResponse, RefusalCause,
    framework_references, parse_response,
};

use super::invoke_fcs_dump_graph;

/// A producer's surface in row currency.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Rows {
    /// Sorted.
    pub entities: Vec<PickledEntityRow>,
    /// Sorted.
    pub extensions: Vec<ExtensionRow>,
    /// In the order FCS lists them.
    pub auto_opens: Vec<String>,
}

/// What a dependant reads of the producer from source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum View {
    /// The decoded signature.
    Found(Rows),
    /// No reading is known.
    Unknown(Unknown),
}

/// Why no reading of the producer is known.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unknown {
    /// The oracle describes no source reading of the producer.
    Refused(RefusalCause),
    /// FCS reads the producer from source, and the decoder cannot read the
    /// signature it reads (the decoder's message).
    Undecodable(String),
}

/// How D1 (the in-memory signature against the DLL FCS compiles from the same
/// arguments) went.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum D1 {
    /// No DLL to compare: the oracle refused, or the producer's check fails.
    NotApplicable,
    /// The rows agree, or both fail the decoder with one message.
    /// `auto_open_split` holds the DLL's assembly-level auto-opens and the
    /// in-memory ones where the two differ.
    Held {
        auto_open_split: Option<(Vec<String>, Vec<String>)>,
    },
}

/// The oracle's answer for one producer, checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reading {
    pub view: View,
    /// The producer's own check's errors, as `FS<n>`.
    pub errors: Vec<String>,
    pub d1: D1,
}

impl Reading {
    /// One line for a manifest.
    pub fn verdict(&self) -> String {
        let mut line = match &self.view {
            View::Unknown(Unknown::Refused(cause)) => format!("refused {cause:?}"),
            View::Unknown(Unknown::Undecodable(why)) => format!("unknown undecodable ({why})"),
            View::Found(rows) => format!(
                "found entities={} extensions={} auto-opens={:?}",
                rows.entities.len(),
                rows.extensions.len(),
                rows.auto_opens
            ),
        };
        if !self.errors.is_empty() {
            line.push_str(&format!(" [FCS: {}]", self.errors.join(",")));
        }
        match &self.d1 {
            D1::NotApplicable => {}
            D1::Held {
                auto_open_split: None,
            } => line.push_str("; D1 held"),
            D1::Held {
                auto_open_split: Some((dll, memory)),
            } => line.push_str(&format!(
                "; D1 held, auto-opens DLL {dll:?} memory {memory:?}"
            )),
        }
        line
    }
}

/// The cell's sources parsed as FCS's check of the producer parses them: at
/// the cell's language version, under [`GraphCell::parse_symbols`].
pub fn parse_cell(cell: &GraphCell) -> Vec<Parse> {
    let lang = LanguageVersion::from_lang_version_text(&cell.lang_version.to_string())
        .unwrap_or_else(|| panic!("{} is no language version", cell.lang_version));
    let symbols = cell.parse_symbols().into_iter().collect();
    cell.files
        .iter()
        .map(|f| {
            let file_kind = if f.name.ends_with(".fsi") {
                FileKind::Sig
            } else {
                FileKind::Impl
            };
            parse_with_options(
                &f.text,
                ParseOptions {
                    file_kind,
                    symbols: &symbols,
                    lang,
                },
            )
        })
        .collect()
}

/// Write `cell` out and compile its reference libraries through the
/// project-graph oracle.
pub fn prepare(cell: &GraphCell) -> PreparedCell {
    cell.prepare(framework_references(), &mut invoke_fcs_dump_graph)
        .unwrap_or_else(|e| panic!("prepare {}: {e}", cell.assembly_name))
}

/// Ask the oracle what a dependant reads of `cell`'s producer, and check the
/// answer (the module docs).
pub fn read(cell: &GraphCell) -> Reading {
    let prepared = prepare(cell);
    let response: ReferencedResponse =
        parse_response(&invoke_fcs_dump_graph(&prepared.referenced_line()))
            .unwrap_or_else(|e| panic!("referenced {}: {e:?}", cell.assembly_name));
    check(cell, &prepared, response)
}

/// Check one `referenced` answer for `cell` (the module docs).
pub fn check(cell: &GraphCell, prepared: &PreparedCell, response: ReferencedResponse) -> Reading {
    let name = cell.assembly_name.as_str();
    let found = match response {
        ReferencedResponse::Refused(refusal) => {
            return Reading {
                view: View::Unknown(Unknown::Refused(refusal.cause)),
                errors: Vec::new(),
                d1: D1::NotApplicable,
            };
        }
        ReferencedResponse::Found(found) => found,
    };
    let errors: Vec<String> = found
        .errors()
        .map(|d| format!("FS{}", d["ErrorNumber"]))
        .collect();
    // FCS's view is what the decoded rows are held to, so a view FCS could
    // not read in full holds them to less than it claims.
    assert!(
        found.read_errors.is_empty(),
        "{name}: FCS's view of the producer could not be read in full: {:?}",
        found.read_errors
    );
    let decoded = decode(name, &found);
    let auto_opens = found.signature.auto_opens.clone();
    let view = match &decoded {
        Ok((entities, extensions)) => {
            let rows = sorted(Rows {
                entities: entities.clone(),
                extensions: extensions.clone(),
                auto_opens: auto_opens.clone(),
            });
            hold_to_fcs_view(name, &rows, &found);
            View::Found(rows)
        }
        Err(why) => View::Unknown(Unknown::Undecodable(why.clone())),
    };
    let d1 = if errors.is_empty() {
        d1(name, prepared, &decoded, &auto_opens)
    } else {
        D1::NotApplicable
    };
    Reading { view, errors, d1 }
}

/// The entity and extension rows of the signature `found` carries for the
/// producer `name`, or the decoder's message.
pub fn decode(
    name: &str,
    found: &ReferencedFound,
) -> Result<(Vec<PickledEntityRow>, Vec<ExtensionRow>), String> {
    let streams: Vec<_> = found
        .signature
        .streams
        .iter()
        .filter(|s| s.ccu == name)
        .collect();
    let [stream] = streams[..] else {
        panic!("{name}: {} signatures for the producer", streams.len());
    };
    let primary = stream.primary_bytes().expect("hex");
    let b = stream.b_bytes().expect("hex");
    borzoi_assembly::unpickle_signature(&primary, b.as_deref())
        .map_err(|e| e.to_string())
        .and_then(|ccu| borzoi_assembly::existence::pickled_rows(&ccu))
}

fn sorted(mut rows: Rows) -> Rows {
    rows.entities.sort();
    rows.extensions.sort();
    rows
}

/// One entity as both sides are compared. FCS's view cannot tell a quoted
/// namespace segment holding a `.` from two segments, so namespaces are
/// compared dotted, as FCS spells them.
struct EntityLine<'a> {
    namespace: String,
    enclosing: &'a [String],
    logical: &'a str,
    compiled: &'a str,
    kind: String,
    public: bool,
    auto_open: bool,
    extension: bool,
}

impl std::fmt::Display for EntityLine<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} | {} | {} ({}) | {} | public={} auto_open={} extension={}",
            self.namespace,
            self.enclosing.join("+"),
            self.logical,
            self.compiled,
            self.kind,
            self.public,
            self.auto_open,
            self.extension
        )
    }
}

/// The decoded rows name exactly the entities FCS's view lists, and every
/// extension member it lists is a decoded row.
fn hold_to_fcs_view(name: &str, rows: &Rows, found: &ReferencedFound) {
    let mut theirs: Vec<String> = found
        .entities
        .iter()
        .map(|e| {
            EntityLine {
                namespace: e.namespace.clone(),
                enclosing: &e.enclosing,
                logical: &e.logical_name,
                compiled: &e.compiled_name,
                kind: format!("{:?}", e.kind).to_lowercase(),
                public: e.access == FcsAccess::Public,
                auto_open: e.auto_open,
                extension: e.extension,
            }
            .to_string()
        })
        .collect();
    let mut decoded: Vec<String> = rows
        .entities
        .iter()
        .filter(|r| r.kind != PickledEntityKind::Namespace)
        .map(|r| {
            EntityLine {
                namespace: r.namespace.join("."),
                enclosing: &r.enclosing,
                logical: &r.logical_name,
                compiled: &r.compiled_name,
                kind: format!("{:?}", r.kind).to_lowercase(),
                public: r.public,
                auto_open: r.auto_open,
                extension: r.extension,
            }
            .to_string()
        })
        .collect();
    theirs.sort();
    decoded.sort();
    assert_eq!(
        decoded, theirs,
        "{name}: the decoded signature is not FCS's view of it (left decoded, right FCS)"
    );
    let index = ExistenceIndex {
        il: Vec::new(),
        pickle: PickleLayer::Read(rows.entities.clone()),
        extensions: rows.extensions.clone(),
    };
    let failures = crate::assembly_entities_diff::pickle_extension_failures(
        &index,
        &found.extension_members,
        false,
    );
    assert!(
        failures.is_empty(),
        "{name}: the decoded extension rows are not FCS's view of them\n{}",
        failures.join("\n")
    );
}

/// D1 in rows: compile the producer from the same arguments and read the
/// DLL.
fn d1(
    name: &str,
    prepared: &PreparedCell,
    decoded: &Result<(Vec<PickledEntityRow>, Vec<ExtensionRow>), String>,
    auto_opens: &[String],
) -> D1 {
    let out: CompileResponse =
        parse_response(&invoke_fcs_dump_graph(prepared.compile_line().as_line()))
            .unwrap_or_else(|e| panic!("{name}: compile: {e:?}"));
    let compile_errors: Vec<String> = out
        .errors()
        .map(|d| format!("FS{}", d["ErrorNumber"]))
        .collect();
    // FCS's check and its compile agree on one argument vector, so a clean
    // check compiles: a compile that fails holds the signature to nothing.
    let Some(dll) = out.output.filter(|_| compile_errors.is_empty()) else {
        panic!("{name}: the producer checks clean and its compile fails: {compile_errors:?}");
    };
    let bytes = std::fs::read(&dll).unwrap_or_else(|e| panic!("read {}: {e}", dll.display()));
    let assembly = Ecma335Assembly::parse(&bytes).expect("parse the DLL");
    let index = assembly.existence_index().expect("existence index");
    match (&index.pickle, decoded) {
        (PickleLayer::Read(rows), Ok((entities, extensions))) => {
            let dll_rows = sorted(Rows {
                entities: rows.clone(),
                extensions: index
                    .extensions
                    .iter()
                    .filter(|r| r.layer == IndexLayer::Pickle)
                    .cloned()
                    .collect(),
                auto_opens: Vec::new(),
            });
            let memory = sorted(Rows {
                entities: entities.clone(),
                extensions: extensions.clone(),
                auto_opens: Vec::new(),
            });
            assert_eq!(
                dll_rows, memory,
                "{name}: D1 in rows: the compiled DLL (left) and the in-memory signature (right) differ"
            );
        }
        (PickleLayer::Unreadable(dll_why), Err(memory_why)) if dll_why == memory_why => {}
        (pickle, decoded) => panic!(
            "{name}: D1: the DLL's pickle is {pickle:?}, the in-memory one decodes to {:?}",
            decoded.as_ref().map(|(e, x)| (e.len(), x.len()))
        ),
    }
    let dll_auto_opens = assembly.assembly_auto_opens().expect("auto-opens");
    D1::Held {
        auto_open_split: (dll_auto_opens != auto_opens)
            .then(|| (dll_auto_opens, auto_opens.to_vec())),
    }
}
