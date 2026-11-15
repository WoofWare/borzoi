//! One project checked by inference and by FCS against the extension-universe
//! fixture ([`super::ensure_ext_universe_fixture_built`]), for the tests of
//! the extension-scope gate: certain-implies-exact soundness in every file,
//! and, for each probed call of the last file, what each side made of it.

use std::path::{Path, PathBuf};

use super::{
    GradedDumps, ensure_ext_universe_fixture_built, ext_universe_env,
    invoke_fcs_dump_types_project_with_refs, temp_fs_tree,
};
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange, TextSize};
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
}

/// The method a call's text names: the identifier between its last `.` and
/// the `(` after it.
fn method_name(call: Call) -> &'static str {
    let dot = call.text.rfind('.').expect("a method call");
    let rest = &call.text[dot + 1..];
    &rest[..rest.find('(').expect("an argument list")]
}

/// The range of `call`'s text on the line that binds `call.binder`.
fn call_range(source: &str, call: Call) -> Option<TextRange> {
    let line = source.find(&format!("let {} ", call.binder))?;
    let start = line + source[line..].find(call.text)?;
    let at = |n: usize| TextSize::new(u32::try_from(n).expect("small source"));
    Some(TextRange::new(at(start), at(start + call.text.len())))
}

/// Check `sources` (Compile order; implementation files only) as one
/// project. The `calls` must be the last bindings of the last file, in order,
/// each binding's census entry being the call's.
pub fn check(sources: &[(&str, String)], calls: &[Call]) -> Checked {
    let env = ext_universe_env();
    let parsed: Vec<(ImplFile, SyntaxRecovery)> = sources
        .iter()
        .map(|(_, s)| {
            let p = parse(s);
            let recovery = SyntaxRecovery::of(&p);
            (ImplFile::cast(p.root).expect("impl file"), recovery)
        })
        .collect();
    let paths: Vec<PathBuf> = sources.iter().map(|(p, _)| (*p).into()).collect();
    let files: Vec<SourceFile> = parsed
        .iter()
        .map(|(f, _)| SourceFile::Impl(f.clone()))
        .collect();
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
    let dumps =
        invoke_fcs_dump_types_project_with_refs(&fs_paths, &[ensure_ext_universe_fixture_built()]);
    let _ = std::fs::remove_dir_all(&root);

    let last = sources.len() - 1;
    let mut unsound = Vec::new();
    let mut fcs_at: Vec<Option<String>> = vec![None; calls.len()];
    for (idx, (types_json, binders_json)) in dumps.iter().enumerate() {
        let (path, source) = &sources[idx];
        let Some(dump) = GradedDumps::read(types_json, binders_json, source, Some(&parsed[idx].0))
        else {
            unsound.push(format!(
                "{path}: an unconverted declaration could not be placed"
            ));
            continue;
        };
        if idx == last {
            for (k, call) in calls.iter().enumerate() {
                fcs_at[k] = call_range(source, *call).and_then(|r| {
                    dump.types
                        .get(&(u32::from(r.start()) as usize, u32::from(r.end()) as usize))
                        .cloned()
                });
            }
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

    let source = &sources[last].1;
    let mut outcomes = Vec::with_capacity(calls.len());
    match inferred.file(last) {
        None => unsound.push(format!("{} was not inferred", sources[last].0)),
        Some(file) => {
            let census = file.incompleteness();
            if census.len() < calls.len() {
                unsound.push(format!(
                    "{}: {} census entries for {} calls",
                    sources[last].0,
                    census.len(),
                    calls.len()
                ));
                return Checked {
                    unsound,
                    calls: outcomes,
                };
            }
            let tail = &census[census.len() - calls.len()..];
            for (k, call) in calls.iter().enumerate() {
                outcomes.push(CallOutcome {
                    ours: call_range(source, *call)
                        .and_then(|r| file.type_at(r))
                        .map(|t| t.render(env)),
                    fcs: fcs_at[k].clone(),
                    census: tail[k].clone(),
                    gate: borzoi_sema::test_support::extension_gate_decline(
                        resolved.file(last),
                        parsed[last].0.syntax(),
                        env,
                        method_name(*call),
                        false,
                        call_range(source, *call).map_or(TextSize::from(0), |r| r.end()),
                    ),
                });
            }
        }
    }
    Checked {
        unsound,
        calls: outcomes,
    }
}
