//! One project checked by inference and by FCS against the extension-universe
//! fixture ([`super::ensure_ext_universe_fixture_built`]), for the tests of
//! the extension-scope gate: certain-implies-exact soundness in every file,
//! and, for each probed call of the last file, what each side made of it.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use super::{
    GradedDumps, ensure_ext_universe_fixture_built, ext_universe_env, invoke_fcs_dump_graph,
    invoke_fcs_dump_types_project_with_refs, temp_fs_tree,
};
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange, TextSize};
use borzoi_oracle_harness::project_graph::{
    FixtureFile, FixtureProject, GraphResponse, PlainName, ProjectGraphFixture,
    framework_references, parse_response,
};
use borzoi_sema::{
    BuiltOutput, CompileItem, GateInput, Incomplete, Producer, ProjectFile, ProviderReferences,
    SourceFile, SyntaxRecovery, certify_by_spelling, infer_project, qualified_names,
    resolve_project_files, source_existence,
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
    /// The type FCS reports for it. Under [`check_referenced`]:
    /// `System.Int64` where FCS binds the extension, the binding's assembly
    /// where it binds another member, and `None` where it reports no use of
    /// the method at the call.
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
}

/// The method a call's text names: the member accessed on a parenthesised
/// receiver (`(asR x).get_Z(1)`), or else the identifier between the last `.`
/// before the argument list and that list (`"abc".Equals(1)`).
fn probe_method_name(text: &str) -> &str {
    match text.find(").") {
        Some(q) => {
            let after = &text[q + 2..];
            &after[..after.find('(').expect("an argument list")]
        }
        None => {
            let head = &text[..text.find('(').expect("an argument list")];
            &head[head.rfind('.').expect("a method call") + 1..]
        }
    }
}

/// The range of `probe`'s text on the line that binds `probe.binder`.
fn probe_range(source: &str, probe: &Probe) -> Option<TextRange> {
    let line = source.find(&format!("let {} ", probe.binder))?;
    let start = line + source[line..].find(probe.text.as_str())?;
    let at = |n: usize| TextSize::new(u32::try_from(n).expect("small source"));
    Some(TextRange::new(at(start), at(start + probe.text.len())))
}

/// Check `sources` (Compile order; implementation files only) as one
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

/// Check `sources` (Compile order; implementation files only) as one project
/// with `refs` referenced, inference reading `env`, which must hold exactly
/// the assemblies the oracle reads (the SDK's and `refs`). Each file's probes
/// must be its last bindings, in order, each binding's census entry being the
/// call's; the outcomes come back in the probes' order.
pub fn check_files(
    env: &borzoi_sema::AssemblyEnv,
    refs: &[&Path],
    sources: &[(&str, String)],
    probes: &[Probe],
) -> Checked {
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
    let dumps = invoke_fcs_dump_types_project_with_refs(&fs_paths, refs);
    let _ = std::fs::remove_dir_all(&root);

    let mut unsound = Vec::new();
    let mut fcs_at: Vec<Option<String>> = vec![None; probes.len()];
    for (idx, (types_json, binders_json)) in dumps.iter().enumerate() {
        let (path, source) = &sources[idx];
        let Some(dump) = GradedDumps::read(types_json, binders_json, source, Some(&parsed[idx].0))
        else {
            unsound.push(format!(
                "{path}: an unconverted declaration could not be placed"
            ));
            continue;
        };
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
        };
    }
    Checked {
        unsound,
        calls: outcomes.into_iter().flatten().collect(),
    }
}

/// The assembly name of the producer [`check_referenced`] hands its consumer
/// from source.
pub const PRODUCER: &str = "ExtProducer";

/// The assembly name of [`check_referenced`]'s consumer.
pub const CONSUMER: &str = "ExtConsumer";

/// `sources` (Compile order; implementation files only) as one project's
/// files.
fn project_files(sources: &[(&str, String)]) -> Vec<ProjectFile> {
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
    files
        .iter()
        .cloned()
        .zip(parsed.iter().map(|(_, r)| r.clone()))
        .zip(qualified_names(&files, &paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect()
}

/// The 1-based line and 0-based column of byte offset `at` in `text`, as
/// FCS's ranges spell a position (the grids' sources are ASCII).
fn line_col(text: &str, at: usize) -> (u64, u64) {
    let line = text[..at].matches('\n').count() as u64 + 1;
    let col = (at - text[..at].rfind('\n').map_or(0, |i| i + 1)) as u64;
    (line, col)
}

/// A producer project A, read from source, and a consumer B that references
/// it, each checked against the extension-universe fixture. Our side reads
/// A as a project reference from source: its entity half through
/// `source_existence` (certified by spelling) and its extension names off
/// its own fold, both into the env
/// ([`borzoi_sema::AssemblyEnv::add_source_existence`]). FCS checks B with A
/// handed to it from source (the graph oracle). For each probed call of B's
/// last file: the gate's input and inference's commit, and FCS's binding,
/// read off its symbol use at the call's method name: `fcs` is
/// `System.Int64` where `extension` says the binding is the extension under
/// test (every extension a grid declares returns a type that is not the
/// intrinsic's), and names the binding's assembly otherwise. The graph
/// check reports symbol uses, not types, so B is graded at its probed calls
/// by that binding: a commit FCS binds to the extension is unsound.
pub fn check_referenced(
    producer: &[(&str, String)],
    consumer: &[(&str, String)],
    calls: &[Call],
    extension: &dyn Fn(&serde_json::Value) -> bool,
) -> Checked {
    let a_files = project_files(producer);
    let a_refs: Vec<&ProjectFile> = a_files.iter().collect();
    let routes = certify_by_spelling(&a_refs);
    let items: Vec<CompileItem<'_>> = a_files.iter().map(CompileItem::Parsed).collect();
    let existence = source_existence(Producer::Evaluated {
        items: &items,
        routes: &routes,
        providers: ProviderReferences::None,
        output: BuiltOutput::Absent,
    });
    let base = ext_universe_env();
    let a_names = resolve_project_files(&a_files, base).extension_names();
    let mut env = base.clone();
    env.add_source_existence(&existence, &a_names);
    let b_files = project_files(consumer);
    let resolved = resolve_project_files(&b_files, &env);
    let inferred = infer_project(&b_files, &resolved, &env);

    let mut unsound = Vec::new();
    let fixture_files = |sources: &[(&str, String)]| -> Vec<FixtureFile> {
        sources
            .iter()
            .map(|(n, t)| FixtureFile {
                name: (*n).to_owned(),
                text: t.clone(),
            })
            .collect()
    };
    let a_name = PlainName::new(PRODUCER).expect("a plain name");
    let b_name = PlainName::new(CONSUMER).expect("a plain name");
    let a = FixtureProject::new(a_name.clone(), fixture_files(producer));
    let mut b = FixtureProject::new(b_name.clone(), fixture_files(consumer));
    b.project_refs = vec![a_name];
    let fixture = ProjectGraphFixture::materialise(vec![a, b]).expect("materialise the projects");
    let mut dlls: Vec<PathBuf> = framework_references().to_vec();
    dlls.push(ensure_ext_universe_fixture_built().to_path_buf());
    let graph = fixture.request(&b_name, &dlls, &BTreeMap::new());
    let response: GraphResponse =
        match parse_response(&invoke_fcs_dump_graph(&graph.to_json_line())) {
            Ok(r) => r,
            Err(e) => {
                return Checked {
                    unsound: vec![format!("the graph oracle refused the projects: {e:?}")],
                    calls: Vec::new(),
                };
            }
        };
    let last = consumer.len() - 1;
    let (last_name, last_source) = &consumer[last];
    let last_path = fixture.paths(&b_name)[last].clone();
    let uses: Vec<&serde_json::Value> = response
        .files
        .iter()
        .filter(|f| f["Path"].as_str().map(Path::new) == Some(last_path.as_path()))
        .flat_map(|f| f["Uses"].as_array().into_iter().flatten())
        .collect();
    let Some(file) = inferred.file(last) else {
        return Checked {
            unsound: vec![format!("{last_name} was not inferred")],
            calls: Vec::new(),
        };
    };
    let census = file.incompleteness();
    if census.len() < calls.len() {
        return Checked {
            unsound: vec![format!(
                "{last_name}: {} census entries for {} calls",
                census.len(),
                calls.len()
            )],
            calls: Vec::new(),
        };
    }
    let tail = &census[census.len() - calls.len()..];
    let mut outcomes = Vec::new();
    for (j, call) in calls.iter().enumerate() {
        let probe = Probe {
            file: last,
            binder: call.binder.to_string(),
            text: call.text.to_string(),
        };
        let Some(range) = probe_range(last_source, &probe) else {
            unsound.push(format!("`{}` is not in {last_name}", call.text));
            continue;
        };
        let name = probe_method_name(call.text);
        // FCS's use of a method spans its whole receiver expression
        // (`(asR x).M`), so it is found by where it ends: at the end of the
        // method's name as written. Not by its logical name, which for a call
        // spelling a compiled name would differ from the spelling.
        let written = call
            .text
            .rfind(&format!(".``{name}``"))
            .map(|dot| (dot + 1, name.len() + 4))
            .or_else(|| {
                call.text
                    .rfind(&format!(".{name}"))
                    .map(|dot| (dot + 1, name.len()))
            });
        let Some((offset, len)) = written else {
            unsound.push(format!("`{}` names no method `{name}`", call.text));
            continue;
        };
        let (line, col) = line_col(
            last_source,
            u32::from(range.start()) as usize + offset + len,
        );
        let binding = uses.iter().find(|u| {
            u["Range"]["End"]["Line"].as_u64() == Some(line)
                && u["Range"]["End"]["Col"].as_u64() == Some(col)
        });
        let ours = file.type_at(range).map(|t| t.render(&env));
        // What FCS bound the call to: the extension, another member (named
        // by its assembly), or nothing it reports. A commit is graded only
        // against a binding: one FCS reports no use for is no intrinsic.
        let fcs = match binding {
            None => {
                if ours.is_some() {
                    unsound.push(format!(
                        "`{}`: committed {ours:?}, where FCS reports no use of the method",
                        call.text
                    ));
                }
                None
            }
            Some(u) if extension(u) => {
                if ours.is_some() {
                    unsound.push(format!(
                        "`{}`: committed {ours:?}, where FCS binds the extension",
                        call.text
                    ));
                }
                Some("System.Int64".to_owned())
            }
            Some(u) => Some(u["Assembly"].as_str().unwrap_or("<no assembly>").to_owned()),
        };
        outcomes.push(CallOutcome {
            ours,
            fcs,
            census: tail[j].clone(),
            gate: borzoi_sema::test_support::extension_gate_decline(
                resolved.file(last),
                &env,
                name,
                false,
            ),
            opens_unenumerated: resolved.file(last).opens_unenumerated(),
        });
    }
    Checked {
        unsound,
        calls: if outcomes.len() == calls.len() {
            outcomes
        } else {
            Vec::new()
        },
    }
}

/// Whether a binding is a member [`PRODUCER`] declares: the extension, where
/// the producer declares nothing else a call can bind.
pub fn declared_by_producer(binding: &serde_json::Value) -> bool {
    binding["Assembly"].as_str() == Some(PRODUCER)
}

/// Whether a binding is an extension a scope-grid cell declares with a
/// producer in play: a member the producer declares; one of the
/// extension-universe fixture's, which the producer's abbreviation of a
/// fixture class (`[<Extension>] type A = ExtUniverse.Cs.CsExts`) brings in;
/// or the consumer's own, marked through what the producer declares. The
/// grid's receivers are the BCL's, so a binding into any of the three is no
/// intrinsic.
pub fn an_extension_through_the_producer(binding: &serde_json::Value) -> bool {
    matches!(
        binding["Assembly"].as_str(),
        Some(a) if a == PRODUCER || a == CONSUMER || a == "SemaExtUniverseFixture"
    )
}
