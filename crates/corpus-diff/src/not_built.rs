//! A report-only measurement of what today's unbuilt-reference grade costs.
//!
//! A project B whose F# `<ProjectReference>` A has no built output resolves
//! with A graded `NotBuilt`: B's env stays complete and holds nothing of A, so
//! name resolution assumes A declares nothing, and a name A's entity would
//! shadow can commit to something else. FCS, as an IDE runs it, checks A's
//! sources instead. This puts each dependent project through the LSP's
//! runtime path and grades it against FCS with every F# reference passed from
//! source ([`ProjectGraphOracle`]), counting what B commits correctly, what it
//! declines and what it gets wrong, and, separately, the uses FCS binds into a
//! referenced project.
//!
//! A grade is only as good as the request FCS was handed, so the census
//! grades a dependent only when every input of that request is one the build
//! would use: the graph is the one the LSP's env fold walks
//! ([`SemanticState::compile_graph_for_project`]), and each project's
//! assembly name, output kind, language version, Compile set and defines must
//! be trusted, and each reference evaluated at the TFM the dependent compiles
//! it at. Anything else is [`NotBuiltReport::Ungraded`], with its reason. A
//! dependent FCS reports errors in, in a reference or in its own files, is
//! graded but kept apart ([`NotBuiltReport::Recovered`]): FCS exports a
//! recovered signature for an erroring project, and bindings after an error
//! are not reliable.
//!
//! It also counts, per referenced project, the reasons borzoi could not read
//! it from source today (an untrusted Compile set or defines, a damaged or
//! unretained parse, a refused fold, a TFM the LSP does not evaluate): the
//! darkness a source-reading design would introduce where it reads nothing.
//!
//! It asserts nothing about the numbers. It is a measurement, run by hand
//! (`tools/not-built-census.sh`), whose output is the input to the
//! source-references stages.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use borzoi::project_deferral::FoldOutcome;
use borzoi::project_graph::{NodeTfm, ProjectGraph, ProjectKind};
use borzoi::semantic::{ProjectId, SemanticState};
use borzoi::workspace::{ServedTfm, Workspace};
use borzoi_msbuild::{ItemMetadataValue, ParsedProject, PropertyRead};
use borzoi_oracle_harness::project_graph::{
    GraphProject, GraphRequest, OutputKind, PlainName, parse_graph_response,
};
use borzoi_sema::SyntaxRecovery;

use crate::{
    Comparison, FileUses, ItemOutcome, LoadedProject, ProjectGraphOracle, UseDecl,
    compare_project_uses, corpus_semantic_state, load_lsp_project, parse_project_uses, path_key,
};

/// One referenced F# project, as the measurement read it.
#[derive(Debug, Clone)]
pub struct ReferencedProject {
    pub project: PathBuf,
    pub assembly_name: String,
    pub compile_items: usize,
    /// Why borzoi could not read it from source today; empty when it could.
    pub unreadable: Vec<String>,
    /// FCS's error diagnostics for it, checked from source; `None` when it
    /// was not put to FCS.
    pub fcs_errors: Option<usize>,
}

/// How the uses FCS binds into one of the referenced projects graded.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CrossProjectUses {
    pub matches: usize,
    pub declines: usize,
    pub wrong: usize,
    pub set_aside: usize,
    /// Records at a range where FCS also reports a use that binds elsewhere
    /// (an attribute alias and its target, a synthetic parameter): not
    /// attributed either way.
    pub ambiguous: usize,
}

/// One graded dependent.
#[derive(Debug)]
pub struct Grade {
    pub comparison: Box<Comparison>,
    pub cross_project: CrossProjectUses,
    /// Wrong commits, rendered, for the report.
    pub wrong: Vec<String>,
}

/// One project's measurement.
#[derive(Debug)]
pub enum NotBuiltReport {
    /// Its compile graph holds no other F# project.
    NotADependent { project: PathBuf },
    /// A dependent the census could not hand FCS the build's inputs for.
    Ungraded {
        project: PathBuf,
        reason: String,
        /// What it read of the references before it stopped.
        referenced: Vec<ReferencedProject>,
    },
    /// Graded, but FCS reported errors in a reference or in the dependent's
    /// own files, so the grade is kept apart from the clean totals.
    Recovered {
        project: PathBuf,
        referenced: Vec<ReferencedProject>,
        grade: Grade,
    },
    /// Graded, with no FCS error anywhere in the graph.
    Compared {
        project: PathBuf,
        referenced: Vec<ReferencedProject>,
        grade: Grade,
    },
}

/// What a request needs of one project, every part trusted, or why some part
/// is not.
struct Trusted {
    name: PlainName,
    target: OutputKind,
    lang_version: String,
}

/// The assembly name `parsed` builds, when it is trusted.
fn assembly_name(project: &Path, parsed: &ParsedProject) -> Option<String> {
    match &parsed.target_name {
        ItemMetadataValue::Known(Some(name)) => Some(name.clone()),
        ItemMetadataValue::Known(None) => project
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned()),
        ItemMetadataValue::Unknown => None,
    }
}

/// The parts of a request every project shares, or each reason one is not
/// trusted.
fn trusted(
    workspace: &mut Workspace,
    project: &Path,
    parsed: &ParsedProject,
) -> Result<Trusted, Vec<String>> {
    let mut why = Vec::new();
    let name = match assembly_name(project, parsed) {
        None => {
            why.push("untrusted assembly name".to_owned());
            None
        }
        Some(n) => match PlainName::new(&n) {
            Ok(n) => Some(n),
            Err(_) => {
                why.push(format!(
                    "assembly name {n:?} is outside the oracle's plain-name domain"
                ));
                None
            }
        },
    };
    let target = match parsed.property("OutputType") {
        PropertyRead::Value(v) => {
            let kind = OutputKind::from_output_type(Some(&v));
            if kind.is_none() {
                why.push(format!("output type {v:?} fsc would not take"));
            }
            kind
        }
        PropertyRead::Unset => Some(OutputKind::Library),
        other => {
            why.push(format!("untrusted output type ({other:?})"));
            None
        }
    };
    let selection = workspace.lang_version_selection(project);
    if selection.refusal.is_some() {
        why.push("its compiler refuses its language version".to_owned());
    }
    if parsed.items_uncertain {
        why.push("untrusted Compile set".to_owned());
    }
    if parsed.define_constants_uncertain {
        why.push("untrusted defines".to_owned());
    }
    match (name, target) {
        (Some(name), Some(target)) if why.is_empty() => Ok(Trusted {
            name,
            target,
            lang_version: selection.version.to_string(),
        }),
        _ => Err(why),
    }
}

fn canonical(p: &Path) -> PathBuf {
    p.canonicalize().unwrap_or_else(|_| p.to_path_buf())
}

/// The env fold's graph for `project`, under its served TFM.
fn compile_graph(
    semantic: &SemanticState,
    workspace: &mut Workspace,
    project: &Path,
) -> ProjectGraph {
    let tfm = workspace.served_tfm_for_project(project);
    semantic.compile_graph_for_project(project, &tfm, workspace)
}

/// `graph`'s F# projects other than `entry`, canonicalised, and whether some
/// node's reference list was suppressed as untrusted.
fn closure_of(graph: &ProjectGraph, entry: &Path) -> (Vec<PathBuf>, bool) {
    let entry = canonical(entry);
    let suppressed = graph.nodes.iter().any(|n| n.references_uncertain);
    let closure = graph
        .nodes
        .iter()
        .filter(|n| n.kind == ProjectKind::FSharp)
        .map(|n| canonical(&n.path))
        .filter(|p| *p != entry)
        .collect();
    (closure, suppressed)
}

/// Whether the TFM a dependent's graph compiles a reference at is the one
/// the LSP evaluates the reference at.
fn same_tfm(compiled_at: &NodeTfm, evaluated_at: &ServedTfm) -> bool {
    match (compiled_at, evaluated_at) {
        (NodeTfm::Known(a), ServedTfm::Tfm(b)) => a.eq_ignore_ascii_case(b),
        (NodeTfm::NoneDeclared, ServedTfm::NoneDeclared) => true,
        _ => false,
    }
}

/// One referenced project's request entry, or why it has none; its
/// readability is recorded either way.
#[allow(clippy::too_many_arguments)]
fn reference_entry(
    semantic: &mut SemanticState,
    workspace: &mut Workspace,
    docs: &borzoi::vfs::Vfs,
    a: &Path,
    compiled_at: &NodeTfm,
    closure: &[PathBuf],
    suppressed: bool,
    ids: &BTreeMap<PathBuf, PlainName>,
) -> (ReferencedProject, Option<GraphProject>) {
    let mut record = ReferencedProject {
        project: a.to_path_buf(),
        assembly_name: a
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default(),
        compile_items: 0,
        unreadable: Vec::new(),
        fcs_errors: None,
    };
    let Some(parsed) = workspace.project(a).cloned() else {
        record.unreadable.push("its evaluation failed".to_owned());
        return (record, None);
    };
    record.compile_items = parsed.items.len();
    if let Some(name) = assembly_name(a, &parsed) {
        record.assembly_name = name;
    }
    let shared = trusted(workspace, a, &parsed);
    if let Err(why) = &shared {
        record.unreadable.extend(why.iter().cloned());
    }
    if parsed.project_references_uncertain || suppressed {
        record
            .unreadable
            .push("untrusted project references".to_owned());
    }
    let served = workspace.served_tfm_for_project(a);
    if parsed.target_frameworks.len() > 1 || !same_tfm(compiled_at, &served) {
        record.unreadable.push(format!(
            "compiled at {compiled_at:?}, which the LSP does not evaluate it at ({served:?})"
        ));
    }
    let parses = semantic.parses_for_project(a, workspace, docs).cloned();
    match &parses {
        Some(parses) => {
            let damaged = parses
                .files
                .iter()
                .filter(
                    |f| matches!(&f.recovery, SyntaxRecovery::Reported(spans) if !spans.is_empty()),
                )
                .count();
            if damaged > 0 {
                record
                    .unreadable
                    .push(format!("{damaged} damaged parse(s)"));
            }
            let unretained = parses
                .files
                .iter()
                .filter(|f| matches!(f.recovery, SyntaxRecovery::Unretained))
                .count();
            if unretained > 0 {
                record
                    .unreadable
                    .push(format!("{unretained} parse(s) with unretained recovery"));
            }
            if parses.len() < parsed.items.len() {
                record.unreadable.push(format!(
                    "{} of {} Compile items unparsed",
                    parsed.items.len() - parses.len(),
                    parsed.items.len()
                ));
            }
        }
        None => {
            let id = ProjectId::new(a);
            record.unreadable.push(
                match semantic.fold_outcome(&id, workspace.evaluation_id(&id)) {
                    FoldOutcome::Refused(refusal) => format!("fold refused: {refusal:?}"),
                    FoldOutcome::Succeeded | FoldOutcome::Unknown => "no parses".to_owned(),
                },
            );
        }
    }
    let (Ok(shared), Some(parses), true) = (shared, parses, record.unreadable.is_empty()) else {
        return (record, None);
    };
    let dotnet_root = workspace.dotnet_root_for_project(a);
    let (refs, retryable) =
        semantic.env_reference_dlls_for_project(a, dotnet_root.as_deref(), &served, workspace);
    // An empty set would leave FCS checking the project against the running
    // SDK's framework rather than its own.
    if refs.is_empty() || retryable {
        record
            .unreadable
            .push("no stable resolved reference set".to_owned());
        return (record, None);
    }
    let entry = GraphProject {
        id: shared.name.clone(),
        assembly_name: shared.name,
        paths: parses.paths,
        exclusive_refs: true,
        refs,
        defines: parsed.define_constants.clone(),
        lang_version: Some(shared.lang_version),
        project_refs: closure.iter().filter_map(|p| ids.get(p).cloned()).collect(),
        target: shared.target,
    };
    (record, Some(entry))
}

/// Measure `project`.
pub fn measure_not_built(project: &Path, oracle: &mut ProjectGraphOracle) -> NotBuiltReport {
    let ungraded = |reason: String, referenced: Vec<ReferencedProject>| NotBuiltReport::Ungraded {
        project: project.to_path_buf(),
        reason,
        referenced,
    };
    let mut workspace = Workspace::new();
    let mut semantic = corpus_semantic_state();
    let docs = borzoi::vfs::Vfs::new();
    let Some(parsed) = workspace.project(project).cloned() else {
        return ungraded("its evaluation failed".to_owned(), Vec::new());
    };

    let graph_b = compile_graph(&semantic, &mut workspace, project);
    let (b_closure, b_suppressed) = closure_of(&graph_b, project);
    if b_closure.is_empty() && !b_suppressed {
        return NotBuiltReport::NotADependent {
            project: project.to_path_buf(),
        };
    }

    // Every project the request needs, with its own compile closure, and the
    // TFM a graph that reaches it compiles it at (the dependent's first).
    let mut compiled_at: BTreeMap<PathBuf, NodeTfm> = BTreeMap::new();
    let note_tfms = |graph: &ProjectGraph, compiled_at: &mut BTreeMap<PathBuf, NodeTfm>| {
        for n in &graph.nodes {
            compiled_at
                .entry(canonical(&n.path))
                .or_insert_with(|| n.tfm.clone());
        }
    };
    note_tfms(&graph_b, &mut compiled_at);
    let mut closures: BTreeMap<PathBuf, (Vec<PathBuf>, bool)> = BTreeMap::new();
    let mut pending = b_closure.clone();
    while let Some(a) = pending.pop() {
        if closures.contains_key(&a) {
            continue;
        }
        let graph_a = compile_graph(&semantic, &mut workspace, &a);
        note_tfms(&graph_a, &mut compiled_at);
        let (closure, suppressed) = closure_of(&graph_a, &a);
        pending.extend(
            closure
                .iter()
                .filter(|q| !closures.contains_key(*q))
                .cloned(),
        );
        closures.insert(a, (closure, suppressed));
    }

    // Ids first: an entry names its references by them.
    let mut ids: BTreeMap<PathBuf, PlainName> = BTreeMap::new();
    for a in closures.keys() {
        if let Some(parsed_a) = workspace.project(a).cloned()
            && let Some(Ok(name)) = assembly_name(a, &parsed_a).map(|n| PlainName::new(&n))
        {
            ids.insert(a.clone(), name);
        }
    }
    let mut referenced = Vec::new();
    let mut graph = Vec::new();
    for (a, (closure, suppressed)) in &closures {
        let (record, entry) = reference_entry(
            &mut semantic,
            &mut workspace,
            &docs,
            a,
            compiled_at.get(a).unwrap_or(&NodeTfm::NotEvaluated),
            closure,
            *suppressed,
            &ids,
        );
        referenced.push(record);
        graph.extend(entry);
    }
    if let Some(unreadable) = referenced.iter().find(|r| !r.unreadable.is_empty()) {
        let why = format!(
            "its reference {} is unreadable from source: {}",
            unreadable.assembly_name,
            unreadable.unreadable.join(", ")
        );
        return ungraded(why, referenced);
    }
    if b_suppressed {
        return ungraded(
            "its compile graph has an untrusted reference list".to_owned(),
            referenced,
        );
    }
    let b = match trusted(&mut workspace, project, &parsed) {
        Ok(b) => b,
        Err(why) => return ungraded(why.join(", "), referenced),
    };

    let loaded = match load_lsp_project(project) {
        Ok(loaded) => loaded,
        Err(skip) => return ungraded(format!("the LSP could not load it: {skip}"), referenced),
    };
    if !loaded.assembly_env.references_not_built() {
        return ungraded(
            "no reference of it is graded NotBuilt".to_owned(),
            referenced,
        );
    }
    if loaded.fcs_extra_refs.is_empty() {
        return ungraded("no resolved reference set".to_owned(), referenced);
    }
    // A file two projects of the graph both compile names one declaration
    // site for two assemblies, which the comparison cannot tell apart.
    let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
    let shared = graph
        .iter()
        .flat_map(|p| p.paths.iter())
        .chain(loaded.parses.paths.iter())
        .find(|p| !seen.insert(path_key(p)));
    if let Some(shared) = shared {
        return ungraded(
            format!(
                "{} is compiled by two projects of its graph",
                shared.display()
            ),
            referenced,
        );
    }
    graph.push(GraphProject {
        id: b.name.clone(),
        assembly_name: b.name.clone(),
        paths: loaded.parses.paths.clone(),
        refs: loaded.fcs_extra_refs.clone(),
        defines: loaded.define_constants.clone(),
        lang_version: Some(b.lang_version),
        exclusive_refs: true,
        project_refs: b_closure
            .iter()
            .filter_map(|p| ids.get(p).cloned())
            .collect(),
        target: b.target,
    });
    let request = match GraphRequest::new(graph, b.name) {
        Ok(r) => r,
        Err(e) => return ungraded(format!("its graph is not one FCS checks: {e}"), referenced),
    };
    let line = match oracle.check_raw(&request) {
        Ok(line) => line,
        Err(e) => return ungraded(format!("FCS did not check it: {e}"), referenced),
    };
    let response = match parse_graph_response(&line) {
        Ok(r) => r,
        Err(e) => return ungraded(format!("unreadable FCS answer: {e}"), referenced),
    };
    for r in &mut referenced {
        r.fcs_errors = response
            .referenced
            .iter()
            .find(|answer| answer.assembly_name == r.assembly_name)
            .map(|answer| answer.errors().count());
    }
    let sources: Vec<_> = loaded
        .parses
        .paths
        .iter()
        .cloned()
        .zip(loaded.parses.texts.iter().cloned())
        .collect();
    let fcs = match parse_project_uses(&line, &sources) {
        Ok(fcs) => fcs,
        Err(e) => return ungraded(format!("unreadable FCS uses: {e}"), referenced),
    };
    let comparison = compare_project_uses(&loaded, &fcs);
    let names: BTreeSet<&str> = referenced
        .iter()
        .map(|r| r.assembly_name.as_str())
        .collect();
    let cross_project = cross_project_uses(&loaded, &comparison, &fcs, &names);
    let recovered = !comparison.fcs_error_files.is_empty()
        || response.errors().next().is_some()
        || referenced.iter().any(|r| r.fcs_errors != Some(0));
    let grade = Grade {
        wrong: render_wrong(&comparison),
        comparison: Box::new(comparison),
        cross_project,
    };
    let project = project.to_path_buf();
    if recovered {
        NotBuiltReport::Recovered {
            project,
            referenced,
            grade,
        }
    } else {
        NotBuiltReport::Compared {
            project,
            referenced,
            grade,
        }
    }
}

fn render_wrong(comparison: &Comparison) -> Vec<String> {
    let file = |p: &Path| {
        p.file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned()
    };
    comparison
        .assembly_divergences
        .iter()
        .map(|d| {
            format!(
                "{}:{:?} {:?}: FCS {} in {:?}, we {}",
                file(&d.file),
                d.range,
                d.name,
                d.expected.full_name,
                d.expected.assembly,
                d.actual
            )
        })
        .chain(comparison.divergences.iter().map(|d| {
            format!(
                "{}:{:?} {:?}: FCS {}, we {}",
                file(&d.file),
                d.range,
                d.name,
                d.expected.file.display(),
                d.actual
            )
        }))
        .chain(comparison.reverse_divergences.iter().map(|d| {
            format!(
                "{}:{:?} unoracled commit: we {}",
                file(&d.file),
                d.range,
                d.actual
            )
        }))
        .collect()
}

/// How the comparison graded each use FCS binds into a project of `names`.
/// A range is attributed only when every FCS record at it binds into such a
/// project; one shared with a record that binds elsewhere is ambiguous.
fn cross_project_uses(
    loaded: &LoadedProject,
    comparison: &Comparison,
    fcs: &[FileUses],
    names: &BTreeSet<&str>,
) -> CrossProjectUses {
    // Per range: whether every record binds into a reference, and whether one does.
    let mut ranges: BTreeMap<(PathBuf, (usize, usize)), (bool, bool)> = BTreeMap::new();
    for f in fcs {
        let Some(path) = loaded
            .parses
            .paths
            .iter()
            .find(|p| path_key(p) == path_key(&f.path))
        else {
            continue;
        };
        for u in &f.uses {
            let into = !matches!(u.decl, UseDecl::InProject(_))
                && u.assembly.as_deref().is_some_and(|a| names.contains(a));
            let entry = ranges
                .entry((path.clone(), (u.start, u.end)))
                .or_insert((true, false));
            entry.0 &= into;
            entry.1 |= into;
        }
    }
    let mut out = CrossProjectUses::default();
    for item in &comparison.ledger {
        let Some(&(all, any)) = ranges.get(&(item.file.clone(), item.range)) else {
            continue;
        };
        if !any {
            continue;
        }
        if !all {
            out.ambiguous += 1;
            continue;
        }
        match item.outcome {
            ItemOutcome::Match(..) => out.matches += 1,
            ItemOutcome::Deferral { .. } => out.declines += 1,
            ItemOutcome::Divergence(_) | ItemOutcome::ReverseDivergence => out.wrong += 1,
            ItemOutcome::SetAside(_)
            | ItemOutcome::UnoracledDefinition
            | ItemOutcome::UnoracledOrPatternAlias
            | ItemOutcome::UnmodelledBinder(_) => out.set_aside += 1,
        }
    }
    out
}

fn write_referenced(f: &mut fmt::Formatter<'_>, referenced: &[ReferencedProject]) -> fmt::Result {
    for r in referenced {
        let errors = r
            .fcs_errors
            .map_or("not checked".to_owned(), |n| n.to_string());
        writeln!(
            f,
            "  references {} ({} Compile items, FCS errors from source: {errors}): {}",
            r.assembly_name,
            r.compile_items,
            if r.unreadable.is_empty() {
                "readable from source".to_owned()
            } else {
                format!("unreadable from source: {}", r.unreadable.join(", "))
            }
        )?;
    }
    Ok(())
}

fn write_grade(f: &mut fmt::Formatter<'_>, grade: &Grade) -> fmt::Result {
    let c = &grade.comparison;
    let x = &grade.cross_project;
    writeln!(
        f,
        "  files: {} compared, {} skipped for FCS errors",
        c.files_compared,
        c.fcs_error_files.len()
    )?;
    writeln!(
        f,
        "  all uses: {} matches, {} declines, {} wrong ({} project, {} assembly, {} unoracled)",
        c.matches + c.assembly_matches,
        c.deferrals + c.assembly_deferrals,
        c.divergences.len() + c.assembly_divergences.len() + c.reverse_divergences.len(),
        c.divergences.len(),
        c.assembly_divergences.len(),
        c.reverse_divergences.len()
    )?;
    writeln!(
        f,
        "  uses FCS binds into a referenced project: {} matches, {} declines, {} wrong, {} set aside, {} ambiguous",
        x.matches, x.declines, x.wrong, x.set_aside, x.ambiguous
    )?;
    for w in &grade.wrong {
        writeln!(f, "    wrong: {w}")?;
    }
    for e in &c.fcs_error_files {
        let first = e.errors.first().map_or(String::new(), |d| {
            format!("FS{:04} {}", d.error_number, d.message)
        });
        writeln!(
            f,
            "    FCS errors in {}: {} ({first})",
            e.path.file_name().unwrap_or_default().to_string_lossy(),
            e.errors.len()
        )?;
    }
    Ok(())
}

impl fmt::Display for NotBuiltReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NotBuiltReport::NotADependent { project } => {
                writeln!(f, "{}: not a dependent", project.display())
            }
            NotBuiltReport::Ungraded {
                project,
                reason,
                referenced,
            } => {
                writeln!(f, "{}: ungraded: {reason}", project.display())?;
                write_referenced(f, referenced)
            }
            NotBuiltReport::Recovered {
                project,
                referenced,
                grade,
            } => {
                writeln!(
                    f,
                    "{}: graded against a recovered FCS check (kept apart)",
                    project.display()
                )?;
                write_referenced(f, referenced)?;
                write_grade(f, grade)
            }
            NotBuiltReport::Compared {
                project,
                referenced,
                grade,
            } => {
                writeln!(f, "{}: graded", project.display())?;
                write_referenced(f, referenced)?;
                write_grade(f, grade)
            }
        }
    }
}

/// Totals over a set of grades.
#[derive(Default)]
struct Totals {
    projects: usize,
    files: usize,
    erroring_files: usize,
    matches: usize,
    declines: usize,
    wrong: usize,
    cross: CrossProjectUses,
}

impl Totals {
    fn add(&mut self, grade: &Grade) {
        let c = &grade.comparison;
        let x = &grade.cross_project;
        self.projects += 1;
        self.files += c.files_compared;
        self.erroring_files += c.fcs_error_files.len();
        self.matches += c.matches + c.assembly_matches;
        self.declines += c.deferrals + c.assembly_deferrals;
        self.wrong +=
            c.divergences.len() + c.assembly_divergences.len() + c.reverse_divergences.len();
        self.cross.matches += x.matches;
        self.cross.declines += x.declines;
        self.cross.wrong += x.wrong;
        self.cross.set_aside += x.set_aside;
        self.cross.ambiguous += x.ambiguous;
    }

    fn render(&self, label: &str) -> String {
        let x = &self.cross;
        format!(
            "{label}: {} projects; files {} compared, {} skipped for FCS errors; \
             all uses {} matches, {} declines, {} wrong; \
             uses into a referenced project {} matches, {} declines, {} wrong, {} set aside, {} ambiguous\n",
            self.projects,
            self.files,
            self.erroring_files,
            self.matches,
            self.declines,
            self.wrong,
            x.matches,
            x.declines,
            x.wrong,
            x.set_aside,
            x.ambiguous
        )
    }
}

/// The totals over `reports`: clean grades and recovered ones apart, and the
/// referenced projects' readability, each counted once by path.
pub fn render_not_built_totals(reports: &[NotBuiltReport]) -> String {
    let mut clean = Totals::default();
    let mut recovered = Totals::default();
    let mut not_dependents = 0;
    let mut ungraded = Vec::new();
    let mut refs: BTreeMap<PathBuf, &ReferencedProject> = BTreeMap::new();
    for r in reports {
        let referenced = match r {
            NotBuiltReport::NotADependent { .. } => {
                not_dependents += 1;
                continue;
            }
            NotBuiltReport::Ungraded {
                project,
                reason,
                referenced,
            } => {
                ungraded.push(format!(
                    "{}: {reason}",
                    project.file_name().unwrap_or_default().to_string_lossy()
                ));
                referenced
            }
            NotBuiltReport::Recovered {
                referenced, grade, ..
            } => {
                recovered.add(grade);
                referenced
            }
            NotBuiltReport::Compared {
                referenced, grade, ..
            } => {
                clean.add(grade);
                referenced
            }
        };
        for a in referenced {
            refs.entry(a.project.clone()).or_insert(a);
        }
    }
    let unreadable: Vec<String> = refs
        .values()
        .filter(|a| !a.unreadable.is_empty())
        .map(|a| format!("{}: {}", a.assembly_name, a.unreadable.join(", ")))
        .collect();
    let mut out = format!(
        "projects: {} graded clean, {} graded recovered, {} ungraded, {not_dependents} not dependents\n",
        clean.projects,
        recovered.projects,
        ungraded.len()
    );
    out.push_str(&clean.render("clean"));
    out.push_str(&recovered.render("recovered"));
    for u in &ungraded {
        out.push_str(&format!("ungraded {u}\n"));
    }
    out.push_str(&format!(
        "referenced projects: {} distinct, {} readable from source, {} not\n",
        refs.len(),
        refs.len() - unreadable.len(),
        unreadable.len()
    ));
    for u in &unreadable {
        out.push_str(&format!("  unreadable {u}\n"));
    }
    out
}
