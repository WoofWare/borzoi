//! A report-only measurement of what today's unbuilt-reference grade costs.
//!
//! A project B whose F# `<ProjectReference>` A has no built output resolves
//! with A graded `NotBuilt`: B's env stays complete and holds nothing of A, so
//! name resolution assumes A declares nothing, and a name A's entity would
//! shadow can commit to something else. FCS, as an IDE runs it, checks A's
//! sources instead. This puts
//! each dependent project through the LSP's runtime path and grades it against
//! FCS with every F# reference passed from source
//! ([`ProjectGraphOracle`](crate::ProjectGraphOracle)), counting what B commits
//! correctly, what it declines and what it gets wrong, and, separately, the
//! uses FCS binds into a referenced project.
//!
//! It also counts, per referenced project, the reasons borzoi could not read
//! it from source today (an untrusted Compile set or defines, several target
//! frameworks, a damaged parse, a refused fold): the darkness a
//! source-reading design would introduce where it reads nothing.
//!
//! It asserts nothing about the numbers. It is a measurement, run by hand
//! (`tools/not-built-census.sh`), whose output is the input to the
//! source-references stages.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use borzoi::project_deferral::FoldOutcome;
use borzoi::semantic::ProjectId;
use borzoi::workspace::Workspace;
use borzoi_msbuild::{ItemMetadataValue, ParsedProject};
use borzoi_oracle_harness::project_graph::{
    GraphProject, GraphRequest, PlainName, parse_graph_response,
};
use borzoi_sema::SyntaxRecovery;

use crate::{
    Comparison, ItemOutcome, LoadedProject, ProjectGraphOracle, ProjectUse, UseDecl,
    compare_project_uses, corpus_semantic_state, load_lsp_project, parse_project_uses,
};

/// One referenced F# project, as the measurement read it.
#[derive(Debug, Clone)]
pub struct ReferencedProject {
    pub project: PathBuf,
    pub assembly_name: String,
    pub compile_items: usize,
    /// Why borzoi could not read it from source today; empty when it could.
    pub unreadable: Vec<String>,
    /// FCS's error diagnostics for it, checked from source.
    pub fcs_errors: usize,
}

/// How the uses FCS binds into one of the referenced projects graded.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CrossProjectUses {
    pub matches: usize,
    pub declines: usize,
    pub wrong: usize,
    pub set_aside: usize,
}

/// One dependent project's measurement.
#[derive(Debug)]
pub enum NotBuiltReport {
    /// The project could not be put to both sides.
    Skipped { project: PathBuf, reason: String },
    Compared {
        project: PathBuf,
        referenced: Vec<ReferencedProject>,
        /// Whether B's env records an unbuilt reference
        /// (`AssemblyEnv::references_not_built`): the grade being measured.
        env_not_built: bool,
        comparison: Box<Comparison>,
        cross_project: CrossProjectUses,
        /// Wrong commits, rendered, for the report.
        wrong: Vec<String>,
    },
}

/// The plain name `fcs-dump` accepts for `s`: its characters outside
/// [`PlainName`]'s alphabet replaced.
fn plain(s: &str) -> PlainName {
    let mapped: String = s
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-') {
                c
            } else {
                '_'
            }
        })
        .collect();
    PlainName::new(if mapped.is_empty() { "_" } else { &mapped }).expect("mapped to a plain name")
}

/// The assembly name `parsed` builds, and whether it is trusted.
fn assembly_name(project: &Path, parsed: &ParsedProject) -> (String, bool) {
    let stem = || {
        project
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default()
    };
    match &parsed.target_name {
        ItemMetadataValue::Known(Some(name)) => (name.clone(), true),
        ItemMetadataValue::Known(None) => (stem(), true),
        ItemMetadataValue::Unknown => (stem(), false),
    }
}

/// `parsed`'s F# project references, canonicalised.
fn fsharp_references(parsed: &ParsedProject) -> Vec<PathBuf> {
    parsed
        .project_references
        .iter()
        .filter(|r| {
            r.include
                .extension()
                .is_some_and(|e| e.eq_ignore_ascii_case("fsproj"))
        })
        .map(|r| {
            r.include
                .canonicalize()
                .unwrap_or_else(|_| r.include.clone())
        })
        .collect()
}

/// Measure the dependent project `project`.
pub fn measure_not_built(project: &Path, oracle: &mut ProjectGraphOracle) -> NotBuiltReport {
    let skipped = |reason: String| NotBuiltReport::Skipped {
        project: project.to_path_buf(),
        reason,
    };
    let loaded = match load_lsp_project(project) {
        Ok(loaded) => loaded,
        Err(skip) => return skipped(format!("the LSP could not load it: {skip}")),
    };

    // A second workspace for the referenced projects: the loader's own is
    // not kept, and each reference is read as the LSP would read it as a
    // project of its own.
    let mut workspace = Workspace::new();
    let mut semantic = corpus_semantic_state();
    let docs = borzoi::vfs::Vfs::new();
    let Some(parsed) = workspace.project(project).cloned() else {
        return skipped("its evaluation failed".to_owned());
    };

    // The referenced closure, in dependency order.
    let mut order: Vec<PathBuf> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<(PathBuf, bool)> = fsharp_references(&parsed)
        .into_iter()
        .rev()
        .map(|p| (p, false))
        .collect();
    while let Some((p, expanded)) = stack.pop() {
        if expanded {
            order.push(p);
            continue;
        }
        if !seen.insert(p.clone()) {
            continue;
        }
        stack.push((p.clone(), true));
        if let Some(r) = workspace.project(&p).cloned() {
            for q in fsharp_references(&r).into_iter().rev() {
                if !seen.contains(&q) {
                    stack.push((q, false));
                }
            }
        }
    }

    let mut ids: BTreeMap<PathBuf, PlainName> = BTreeMap::new();
    let mut graph = Vec::new();
    let mut referenced = Vec::new();
    for a in &order {
        let Some(parsed_a) = workspace.project(a).cloned() else {
            return skipped(format!("its reference {} did not evaluate", a.display()));
        };
        let (name, name_trusted) = assembly_name(a, &parsed_a);
        let mut unreadable = Vec::new();
        if parsed_a.items_uncertain {
            unreadable.push("untrusted Compile set".to_owned());
        }
        if parsed_a.define_constants_uncertain {
            unreadable.push("untrusted defines".to_owned());
        }
        if parsed_a.project_references_uncertain {
            unreadable.push("untrusted project references".to_owned());
        }
        if parsed_a.target_frameworks.len() > 1 {
            unreadable.push(format!(
                "{} target frameworks",
                parsed_a.target_frameworks.len()
            ));
        }
        if !name_trusted {
            unreadable.push("untrusted assembly name".to_owned());
        }
        let parses = semantic
            .parses_for_project(a, &mut workspace, &docs)
            .cloned();
        let paths: Vec<PathBuf> = match &parses {
            Some(parses) => {
                let damaged = parses
                    .files
                    .iter()
                    .filter(|f| matches!(&f.recovery, SyntaxRecovery::Reported(spans) if !spans.is_empty()))
                    .count();
                if damaged > 0 {
                    unreadable.push(format!("{damaged} damaged parse(s)"));
                }
                if parses.len() < parsed_a.items.len() {
                    unreadable.push(format!(
                        "{} of {} Compile items unparsed",
                        parsed_a.items.len() - parses.len(),
                        parsed_a.items.len()
                    ));
                }
                parses.paths.clone()
            }
            None => {
                let id = ProjectId::new(a);
                let why = match semantic.fold_outcome(&id, workspace.evaluation_id(&id)) {
                    FoldOutcome::Refused(refusal) => format!("fold refused: {refusal:?}"),
                    FoldOutcome::Succeeded | FoldOutcome::Unknown => "no parses".to_owned(),
                };
                unreadable.push(why);
                parsed_a.items.iter().map(|i| i.include.clone()).collect()
            }
        };
        let dotnet_root = workspace.dotnet_root_for_project(a);
        let tfm = workspace.served_tfm_for_project(a);
        let (refs, _) =
            semantic.env_reference_dlls_for_project(a, dotnet_root.as_deref(), &tfm, &workspace);
        let id = plain(&name);
        ids.insert(a.clone(), id.clone());
        let project_refs = fsharp_references(&parsed_a)
            .iter()
            .filter_map(|r| ids.get(r).cloned())
            .collect();
        graph.push(GraphProject {
            id: id.clone(),
            assembly_name: id,
            paths,
            exclusive_refs: !refs.is_empty(),
            refs,
            defines: parsed_a.define_constants.clone(),
            lang_version: parsed_a.lang_version.clone(),
            project_refs,
        });
        referenced.push(ReferencedProject {
            project: a.clone(),
            assembly_name: name,
            compile_items: parsed_a.items.len(),
            unreadable,
            fcs_errors: 0,
        });
    }

    let (name, _) = assembly_name(project, &parsed);
    let check = plain(&name);
    graph.push(GraphProject {
        id: check.clone(),
        assembly_name: check.clone(),
        paths: loaded.parses.paths.clone(),
        refs: loaded.fcs_extra_refs.clone(),
        defines: loaded.define_constants.clone(),
        lang_version: loaded.lang_version.clone(),
        exclusive_refs: !loaded.fcs_extra_refs.is_empty(),
        project_refs: fsharp_references(&parsed)
            .iter()
            .filter_map(|r| ids.get(r).cloned())
            .collect(),
    });
    let request = match GraphRequest::new(graph, check) {
        Ok(r) => r,
        Err(e) => return skipped(format!("its graph is not one FCS checks: {e}")),
    };
    let line = match oracle.check_raw(&request) {
        Ok(line) => line,
        Err(e) => return skipped(format!("FCS did not check it: {e}")),
    };
    let response = match parse_graph_response(&line) {
        Ok(r) => r,
        Err(e) => return skipped(format!("unreadable FCS answer: {e}")),
    };
    for (r, answer) in referenced.iter_mut().zip(&response.referenced) {
        r.fcs_errors = answer.errors().count();
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
        Err(e) => return skipped(format!("unreadable FCS uses: {e}")),
    };
    let comparison = compare_project_uses(&loaded, &fcs);
    let names: BTreeSet<&str> = referenced
        .iter()
        .map(|r| r.assembly_name.as_str())
        .collect();
    let cross_project = cross_project_uses(&loaded, &comparison, &fcs, &names);
    let wrong = comparison
        .assembly_divergences
        .iter()
        .map(|d| {
            format!(
                "{}:{:?} {:?}: FCS {} in {:?}, we {}",
                d.file.file_name().unwrap_or_default().to_string_lossy(),
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
                d.file.file_name().unwrap_or_default().to_string_lossy(),
                d.range,
                d.name,
                d.expected.file.display(),
                d.actual
            )
        }))
        .chain(comparison.reverse_divergences.iter().map(|d| {
            format!(
                "{}:{:?} unoracled commit: we {}",
                d.file.file_name().unwrap_or_default().to_string_lossy(),
                d.range,
                d.actual
            )
        }))
        .collect();
    NotBuiltReport::Compared {
        project: project.to_path_buf(),
        referenced,
        env_not_built: loaded.assembly_env.references_not_built(),
        comparison: Box::new(comparison),
        cross_project,
        wrong,
    }
}

/// How the comparison graded each use FCS binds into a project of `names`.
fn cross_project_uses(
    loaded: &LoadedProject,
    comparison: &Comparison,
    fcs: &[crate::FileUses],
    names: &BTreeSet<&str>,
) -> CrossProjectUses {
    let into_reference = |u: &ProjectUse| {
        !matches!(u.decl, UseDecl::InProject(_))
            && u.assembly.as_deref().is_some_and(|a| names.contains(a))
    };
    let mut keys: BTreeSet<(PathBuf, (usize, usize))> = BTreeSet::new();
    for f in fcs {
        let Some(path) = loaded
            .parses
            .paths
            .iter()
            .find(|p| crate::path_key(p) == crate::path_key(&f.path))
        else {
            continue;
        };
        for u in f.uses.iter().filter(|u| into_reference(u)) {
            keys.insert((path.clone(), (u.start, u.end)));
        }
    }
    let mut out = CrossProjectUses::default();
    for item in &comparison.ledger {
        if !keys.contains(&(item.file.clone(), item.range)) {
            continue;
        }
        match item.outcome {
            ItemOutcome::Match(..) => out.matches += 1,
            ItemOutcome::Deferral { .. } => out.declines += 1,
            ItemOutcome::Divergence(_) => out.wrong += 1,
            _ => out.set_aside += 1,
        }
    }
    out
}

impl fmt::Display for NotBuiltReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NotBuiltReport::Skipped { project, reason } => {
                writeln!(f, "{}: skipped: {reason}", project.display())
            }
            NotBuiltReport::Compared {
                project,
                referenced,
                env_not_built,
                comparison: c,
                cross_project: x,
                wrong,
            } => {
                writeln!(
                    f,
                    "{}: env marks an unbuilt reference: {env_not_built}",
                    project.display()
                )?;
                for r in referenced {
                    writeln!(
                        f,
                        "  references {} ({} Compile items, FCS errors from source: {}): {}",
                        r.assembly_name,
                        r.compile_items,
                        r.fcs_errors,
                        if r.unreadable.is_empty() {
                            "readable from source".to_owned()
                        } else {
                            format!("unreadable from source: {}", r.unreadable.join(", "))
                        }
                    )?;
                }
                let erroring: usize = c.fcs_error_files.len();
                writeln!(
                    f,
                    "  files: {} compared, {} skipped for FCS errors",
                    c.files_compared, erroring
                )?;
                let wrong_total = c.divergences.len()
                    + c.assembly_divergences.len()
                    + c.reverse_divergences.len();
                writeln!(
                    f,
                    "  all uses: {} matches, {} declines, {} wrong ({} project, {} assembly, {} unoracled)",
                    c.matches + c.assembly_matches,
                    c.deferrals + c.assembly_deferrals,
                    wrong_total,
                    c.divergences.len(),
                    c.assembly_divergences.len(),
                    c.reverse_divergences.len()
                )?;
                writeln!(
                    f,
                    "  uses FCS binds into a referenced project: {} matches, {} declines, {} wrong, {} set aside",
                    x.matches, x.declines, x.wrong, x.set_aside
                )?;
                for w in wrong {
                    writeln!(f, "    wrong: {w}")?;
                }
                if erroring > 0 {
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
                }
                Ok(())
            }
        }
    }
}

/// The totals over `reports`: one line per measure.
pub fn render_not_built_totals(reports: &[NotBuiltReport]) -> String {
    let mut compared = 0;
    let mut skipped = 0;
    let (mut matches, mut declines, mut wrong, mut erroring, mut files) = (0, 0, 0, 0, 0);
    let mut x = CrossProjectUses::default();
    let mut refs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for r in reports {
        match r {
            NotBuiltReport::Skipped { .. } => skipped += 1,
            NotBuiltReport::Compared {
                comparison: c,
                cross_project,
                referenced,
                ..
            } => {
                compared += 1;
                matches += c.matches + c.assembly_matches;
                declines += c.deferrals + c.assembly_deferrals;
                wrong += c.divergences.len()
                    + c.assembly_divergences.len()
                    + c.reverse_divergences.len();
                erroring += c.fcs_error_files.len();
                files += c.files_compared;
                x.matches += cross_project.matches;
                x.declines += cross_project.declines;
                x.wrong += cross_project.wrong;
                x.set_aside += cross_project.set_aside;
                for a in referenced {
                    refs.insert(a.assembly_name.clone(), a.unreadable.clone());
                }
            }
        }
    }
    let readable = refs.values().filter(|u| u.is_empty()).count();
    format!(
        "dependent projects: {compared} compared, {skipped} skipped\n\
         files: {files} compared, {erroring} skipped for FCS errors\n\
         all uses: {matches} matches, {declines} declines, {wrong} wrong\n\
         uses FCS binds into a referenced project: {} matches, {} declines, {} wrong, {} set aside\n\
         referenced projects: {} distinct, {readable} readable from source, {} not ({})\n",
        x.matches,
        x.declines,
        x.wrong,
        x.set_aside,
        refs.len(),
        refs.len() - readable,
        refs.iter()
            .filter(|(_, u)| !u.is_empty())
            .map(|(n, u)| format!("{n}: {}", u.join(", ")))
            .collect::<Vec<_>>()
            .join("; ")
    )
}
