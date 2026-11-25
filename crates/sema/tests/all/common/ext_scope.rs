//! One project checked by inference and by FCS against the extension-universe
//! fixture ([`super::ensure_ext_universe_fixture_built`]), for the tests of
//! the extension-scope gate: certain-implies-exact soundness in every file,
//! and, for each probed call of the last file, what each side made of it.

use std::path::{Path, PathBuf};

use super::{
    GradedDumps, ensure_ext_universe_fixture_built, ext_universe_env,
    invoke_fcs_dump_types_project_with_refs, temp_fs_tree,
};
use borzoi_cst::parser::{parse, parse_sig};
use borzoi_cst::syntax::{AstNode, ImplFile, SigFile, TextRange, TextSize};
use borzoi_sema::{
    GateInput, Incomplete, ProjectFile, SourceFile, SyntaxRecovery, infer_project, qualified_names,
    resolve_project_files,
};

/// A probed call of the last file: the binder of the binding it is the body
/// of, and its exact text.
#[derive(Debug, Clone, Copy)]
pub struct Call {
    pub binder: &'static str,
    pub text: &'static str,
}

/// What each side made of one [`Call`].
#[derive(Debug, Clone)]
pub struct CallOutcome {
    /// The type inference committed for the call's node, rendered.
    pub ours: Option<String>,
    /// The type FCS reports for it.
    pub fcs: Option<String>,
    /// The census of the call's binding.
    pub census: Vec<Incomplete>,
    /// Which input of the extension-scope gate declines a value-receiver
    /// call of the method's name in the last file, asked directly
    /// ([`borzoi_sema::test_support::extension_gate_decline`]): whether or not
    /// inference reaches the gate at this call.
    pub gate: Option<GateInput>,
    /// Whether the call's file holds an `open` the gate reads as
    /// unenumerated ([`borzoi_sema::ResolvedFile::opens_unenumerated`]).
    pub opens_unenumerated: bool,
}

impl CallOutcome {
    /// Whether the extension-scope gate declined the call.
    pub fn gated(&self) -> bool {
        self.census
            .iter()
            .any(|r| matches!(r, Incomplete::ExtensionInScope))
    }
}

/// What checking one project found.
pub struct Checked {
    /// Every commit FCS disagrees with, in any file, and anything that kept
    /// the project from being graded.
    pub unsound: Vec<String>,
    /// Per probed call, in order.
    pub calls: Vec<CallOutcome>,
    /// Every error FCS reported, as `<file>: FS<code>`.
    pub fcs_errors: Vec<String>,
}

/// The method a call's text names: the member accessed on a parenthesised
/// receiver (`(asR x).get_Z(1)`), or else the identifier between the last `.`
/// before the argument list and that list (`"abc".Equals(1)`).
fn probe_method_name(text: &str) -> &str {
    let spelled = match text.find(").") {
        Some(q) => {
            let after = &text[q + 2..];
            &after[..after.find('(').expect("an argument list")]
        }
        None => {
            let head = &text[..text.find('(').expect("an argument list")];
            &head[head.rfind('.').expect("a method call") + 1..]
        }
    };
    // A backticked name is its text.
    spelled
        .strip_prefix("``")
        .and_then(|s| s.strip_suffix("``"))
        .unwrap_or(spelled)
}

/// The range of `probe`'s text on the line that binds `probe.binder`.
fn probe_range(source: &str, probe: &Probe) -> Option<TextRange> {
    let line = source.find(&format!("let {} ", probe.binder))?;
    let start = line + source[line..].find(probe.text.as_str())?;
    let at = |n: usize| TextSize::new(u32::try_from(n).expect("small source"));
    Some(TextRange::new(at(start), at(start + probe.text.len())))
}

/// Check `sources` (Compile order; a `.fsi` name is a signature) as one
/// project. The `calls` must be the last bindings of the last file, in order,
/// each binding's census entry being the call's.
pub fn check(sources: &[(&str, String)], calls: &[Call]) -> Checked {
    check_in(ext_universe_env(), sources, calls)
}

/// [`check`] with inference reading `env`, which must hold exactly
/// [`ext_universe_env`]'s assemblies (the oracle reads those): a copy that
/// differs only in what the host marked on it.
pub fn check_in(
    env: &borzoi_sema::AssemblyEnv,
    sources: &[(&str, String)],
    calls: &[Call],
) -> Checked {
    let last = sources.len() - 1;
    let probes: Vec<Probe> = calls
        .iter()
        .map(|c| Probe {
            file: last,
            binder: c.binder.to_string(),
            text: c.text.to_string(),
        })
        .collect();
    check_files(
        env,
        &[ensure_ext_universe_fixture_built()],
        sources,
        &probes,
    )
}

/// A probed call in any file of a project: the file's index, the binder of
/// the binding it is the body of, and its exact text.
#[derive(Debug, Clone)]
pub struct Probe {
    pub file: usize,
    pub binder: String,
    pub text: String,
}

/// Check `sources` (Compile order; a `.fsi` name is a signature) as one
/// project with `refs` referenced, inference reading `env`, which must hold exactly
/// the assemblies the oracle reads (the SDK's and `refs`). Each file's probes
/// must be its last bindings, in order, each binding's census entry being the
/// call's; the outcomes come back in the probes' order.
pub fn check_files(
    env: &borzoi_sema::AssemblyEnv,
    refs: &[&Path],
    sources: &[(&str, String)],
    probes: &[Probe],
) -> Checked {
    let parsed: Vec<(SourceFile, SyntaxRecovery)> = sources
        .iter()
        .map(|(name, s)| {
            if name.ends_with(".fsi") {
                let p = parse_sig(s);
                let recovery = SyntaxRecovery::of(&p);
                (
                    SourceFile::Sig(SigFile::cast(p.root).expect("sig file")),
                    recovery,
                )
            } else {
                let p = parse(s);
                let recovery = SyntaxRecovery::of(&p);
                (
                    SourceFile::Impl(ImplFile::cast(p.root).expect("impl file")),
                    recovery,
                )
            }
        })
        .collect();
    let paths: Vec<PathBuf> = sources.iter().map(|(p, _)| (*p).into()).collect();
    let files: Vec<SourceFile> = parsed.iter().map(|(f, _)| f.clone()).collect();
    let project: Vec<ProjectFile> = files
        .iter()
        .cloned()
        .zip(parsed.iter().map(|(_, r)| r.clone()))
        .zip(qualified_names(&files, &paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect();
    let resolved = resolve_project_files(&project, env);
    let inferred = infer_project(&project, &resolved, env);

    let rows: Vec<(&str, &str)> = sources.iter().map(|(p, s)| (*p, s.as_str())).collect();
    let (root, written) = temp_fs_tree("ext_scope", &rows);
    let fs_paths: Vec<&Path> = written.iter().map(|(p, _)| p.as_path()).collect();
    let dumps = invoke_fcs_dump_types_project_with_refs(&fs_paths, refs);
    let _ = std::fs::remove_dir_all(&root);

    let mut unsound = Vec::new();
    let mut fcs_errors = Vec::new();
    let mut fcs_at: Vec<Option<String>> = vec![None; probes.len()];
    for (idx, (types_json, binders_json)) in dumps.iter().enumerate() {
        let (path, source) = &sources[idx];
        let Some(dump) =
            GradedDumps::read(types_json, binders_json, source, parsed[idx].0.as_impl())
        else {
            unsound.push(format!(
                "{path}: an unconverted declaration could not be placed"
            ));
            continue;
        };
        fcs_errors.extend(
            dump.errors
                .iter()
                .map(|e| format!("{path}: FS{:04}", e.code)),
        );
        for (k, probe) in probes.iter().enumerate().filter(|(_, p)| p.file == idx) {
            fcs_at[k] = probe_range(source, probe).and_then(|r| {
                dump.types
                    .get(&(u32::from(r.start()) as usize, u32::from(r.end()) as usize))
                    .cloned()
            });
        }
        let Some(file) = inferred.file(idx) else {
            continue;
        };
        for (range, ty) in file.types() {
            let key = (
                u32::from(range.start()) as usize,
                u32::from(range.end()) as usize,
            );
            if dump.is_ungraded(key) {
                continue;
            }
            let ours = ty.render(env);
            match dump.types.get(&key) {
                Some(theirs) if *theirs == ours => {}
                theirs => unsound.push(format!(
                    "{path}: `{}` typed `{ours}`, FCS {theirs:?}",
                    &source[key.0..key.1]
                )),
            }
        }
        let rf = resolved.file(idx);
        for (def_id, ty) in file.def_types() {
            let def = rf.def(*def_id);
            let key = (
                u32::from(def.range.start()) as usize,
                u32::from(def.range.end()) as usize,
            );
            if dump.is_ungraded(key) {
                continue;
            }
            let ours = ty.render(env);
            match dump.binders.get(&key) {
                Some(theirs) if *theirs == ours => {}
                theirs => unsound.push(format!(
                    "{path}: binder `{}` typed `{ours}`, FCS {theirs:?}",
                    def.spelling(env)
                )),
            }
        }
    }

    let mut outcomes: Vec<Option<CallOutcome>> = vec![None; probes.len()];
    for (idx, (path, source)) in sources.iter().enumerate() {
        let mine: Vec<usize> = (0..probes.len())
            .filter(|&k| probes[k].file == idx)
            .collect();
        if mine.is_empty() {
            continue;
        }
        let Some(file) = inferred.file(idx) else {
            unsound.push(format!("{path} was not inferred"));
            continue;
        };
        let census = file.incompleteness();
        if census.len() < mine.len() {
            unsound.push(format!(
                "{path}: {} census entries for {} calls",
                census.len(),
                mine.len()
            ));
            continue;
        }
        let tail = &census[census.len() - mine.len()..];
        for (j, &k) in mine.iter().enumerate() {
            let probe = &probes[k];
            outcomes[k] = Some(CallOutcome {
                ours: probe_range(source, probe)
                    .and_then(|r| file.type_at(r))
                    .map(|t| t.render(env)),
                fcs: fcs_at[k].clone(),
                census: tail[j].clone(),
                gate: borzoi_sema::test_support::extension_gate_decline(
                    resolved.file(idx),
                    env,
                    probe_method_name(&probe.text),
                    false,
                ),
                opens_unenumerated: resolved.file(idx).opens_unenumerated(),
            });
        }
    }
    if outcomes.iter().any(Option::is_none) {
        return Checked {
            unsound,
            calls: Vec::new(),
            fcs_errors,
        };
    }
    Checked {
        unsound,
        calls: outcomes.into_iter().flatten().collect(),
        fcs_errors,
    }
}
