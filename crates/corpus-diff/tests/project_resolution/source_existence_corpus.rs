//! The corpus twin of `borzoi-sema`'s `source_existence_diff`: every pinned
//! project (`BORZOI_PROJECT_LIST`), loaded through the LSP's runtime path,
//! read by `borzoi_sema::source_existence` and held to FCS's reading of the
//! same project handed to a consumer from source (`fcs-dump`'s `referenced`
//! op), with exactly the reference set our side loads.
//!
//! FCS's reading is its in-memory signature, decoded with
//! `borzoi_assembly::unpickle_signature`, and the assembly-level `AutoOpen`
//! strings beside it: what a dependant reads.
//!
//! Both are graded as the existence questions read them: the facts of the
//! existence set each index builds (`test_support::existence_facts`).
//!
//! The walk is run under `MarkerRoutes::Unknown`, the only certificate a
//! caller without A's environment may give: every attribute may denote every
//! marker. It must then **cover** FCS's facts (every one of them one of
//! ours) or decline; its surplus per kind is pinned. Under `Unknown` an assembly-level attribute may be
//! `[<TypeProviderAssembly>]`, so a project with one (most: an
//! `AssemblyInfo.fs` granting `InternalsVisibleTo`) declines whole; the
//! census counts how many, and Stage 1b's certificate, built from A's own
//! resolution, is what lifts it.
//!
//! The walk is also run certified by spelling, which holds only when A's
//! references route no other name to a marker and shadow none. Nothing
//! certifies that for a real project, so that reading asserts nothing; its
//! verdict is pinned beside the other as a measurement of how much the
//! certificate will buy.
//!
//! Each project's verdicts are pinned in
//! `crates/corpus-diff/manifests/source_existence_projects.txt`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use borzoi_assembly::existence::{ExistenceIndex, ExtensionRow, PickleLayer, PickledEntityRow};
use borzoi_corpus_diff::{LoadedProject, ProjectGraphOracle, load_lsp_project};
use borzoi_oracle_harness::manifest::{Manifest, UPDATE_ENV, check};
use borzoi_oracle_harness::project_graph::{
    GraphProject, GraphRequest, PlainName, Reference, ReferencedResponse, Target,
};
use borzoi_sema::test_support::existence_facts;
use borzoi_sema::{
    CompileItem, MarkerRoutes, Producer, ProjectFile, SourceExistence, certify_by_spelling,
    source_existence,
};

/// The language versions the oracle's template checks at, by the spellings a
/// project may give it.
const ORACLE_LANG_VERSIONS: &[&str] = &["10.0", "10", "latest", "default", "latestmajor"];

/// `path` relative to the checkout holding it, prefixed with the checkout's
/// directory name: the same key on every host.
fn checkout_key(path: &Path) -> String {
    let root = path
        .ancestors()
        .find(|d| d.join(".git").exists())
        .unwrap_or_else(|| panic!("{} is not inside a checkout", path.display()));
    let name = root
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    let rel = path.strip_prefix(root).expect("an ancestor is a prefix");
    let rel: Vec<String> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    format!("{name}/{}", rel.join("/"))
}

/// Our reading of `loaded` under `routes` (or certified by spelling).
fn ours(loaded: &LoadedProject, routes: Option<&MarkerRoutes>) -> SourceExistence {
    let parsed: BTreeMap<&Path, &ProjectFile> = loaded
        .parses
        .paths
        .iter()
        .map(PathBuf::as_path)
        .zip(&loaded.parses.files)
        .collect();
    // An item the evaluation lists that the parses omit (unreadable, or no
    // root) is unread, never absent.
    let items: Vec<CompileItem<'_>> = loaded
        .compile_items
        .iter()
        .map(|p| match parsed.get(p.as_path()) {
            Some(pf) => CompileItem::Parsed(pf),
            None => CompileItem::Unreadable(p.to_str().unwrap_or("<non-UTF-8 path>")),
        })
        .collect();
    let files: Vec<&ProjectFile> = loaded.parses.files.iter().collect();
    let by_spelling = certify_by_spelling(&files);
    source_existence(Producer::Evaluated {
        items: &items,
        routes: routes.unwrap_or(&by_spelling),
    })
}

/// FCS's rows of `loaded` as a consumer reads it from source, or why there
/// are none to grade against.
fn fcs(loaded: &LoadedProject, oracle: &mut ProjectGraphOracle) -> Result<FcsRows, String> {
    if let Some(v) = &loaded.lang_version
        && !ORACLE_LANG_VERSIONS.contains(&v.to_ascii_lowercase().as_str())
    {
        return Err(format!("language version {v} is not the oracle's"));
    }
    // A type provider's design-time assembly outlives the oracle's
    // per-request clearing (#1086): a project referencing one would need the
    // process isolation of #1085. A reference whose bytes name the attribute
    // anywhere (FSharp.Core declares it, and is none) may be one.
    for dll in &loaded.fcs_extra_refs {
        let is_core = dll
            .file_name()
            .is_some_and(|n| n.eq_ignore_ascii_case("FSharp.Core.dll"));
        let bytes = std::fs::read(dll).map_err(|e| e.to_string())?;
        if !is_core
            && bytes
                .windows(b"TypeProviderAssemblyAttribute".len())
                .any(|w| w == b"TypeProviderAssemblyAttribute")
        {
            return Err("a reference may be a type provider (#1086)".to_owned());
        }
    }
    let name = |s: &str| PlainName::new(s).expect("a plain name");
    let defines: Vec<String> = loaded
        .define_constants
        .iter()
        .map(|d| d.trim().to_owned())
        .filter(|d| !d.is_empty())
        .collect();
    let dlls: Vec<Reference> = loaded
        .fcs_extra_refs
        .iter()
        .cloned()
        .map(Reference::Dll)
        .collect();
    let producer = GraphProject {
        id: name("Producer"),
        assembly_name: name("SourceExistenceProducer"),
        target: Target::Library,
        sources: loaded.compile_items.clone(),
        defines,
        references: dlls.clone(),
    };
    let consumer_dir = tempfile::tempdir().map_err(|e| e.to_string())?;
    let consumer_dir = consumer_dir
        .path()
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let consumer_source = consumer_dir.join("Consumer.fs");
    std::fs::write(
        &consumer_source,
        "module SourceExistenceConsumer.Use\nlet x = 1\n",
    )
    .map_err(|e| e.to_string())?;
    let mut consumer_refs = dlls;
    consumer_refs.push(Reference::Project(name("Producer")));
    let consumer = GraphProject {
        id: name("Consumer"),
        assembly_name: name("SourceExistenceConsumer"),
        target: Target::Library,
        sources: vec![consumer_source],
        defines: Vec::new(),
        references: consumer_refs,
    };
    let request = GraphRequest::new(vec![producer, consumer], name("Consumer"))
        .map_err(|e| format!("no graph request: {e}"))?;
    let line = request
        .referenced_line(&name("Producer"))
        .expect("the consumer references the producer");
    let response: ReferencedResponse = oracle
        .referenced(&line)
        .map_err(|e| format!("the oracle answered no rows: {e}"))?;
    // A project FCS rejects is imported, if at all, as FCS's recovery, which
    // the walk does not model; `source_existence_diff` grades that case on
    // generated input.
    let errors = response.errors().count();
    if errors > 0 {
        return Err(format!("FCS rejects it ({errors} errors)"));
    }
    assert!(
        response.imported,
        "FCS imported nothing of a project it accepts"
    );
    let streams: Vec<_> = response
        .signature
        .streams
        .iter()
        .filter(|s| s.ccu == "SourceExistenceProducer")
        .collect();
    let [s] = streams.as_slice() else {
        return Err(format!("{} signatures", streams.len()));
    };
    let primary = s.primary_bytes()?;
    let b = s.b_bytes()?;
    let ccu = borzoi_assembly::unpickle_signature(&primary, b.as_deref())
        .map_err(|e| format!("the signature does not decode: {e}"))?;
    let (entities, extensions) = borzoi_assembly::existence::pickled_rows(&ccu)?;
    Ok(FcsRows {
        entities,
        extensions,
        auto_opens: response.signature.auto_opens.clone(),
    })
}

struct FcsRows {
    entities: Vec<PickledEntityRow>,
    extensions: Vec<ExtensionRow>,
    auto_opens: Vec<String>,
}

/// Why the loader skipped a project, without the details (which name host
/// paths).
fn skip_kind(skip: &borzoi_corpus_diff::LoadSkip) -> &'static str {
    use borzoi_corpus_diff::LoadSkip;
    match skip {
        LoadSkip::ProjectEvaluationFailed => "project evaluation failed",
        LoadSkip::ItemsUncertain { .. } => "Compile items uncertain (fold refused)",
        LoadSkip::DefineConstantsUncertain { .. } => "DefineConstants uncertain (fold refused)",
        LoadSkip::TooManyFiles { .. } => "too many files",
        LoadSkip::SemanticUnavailable => "semantic load unavailable",
        LoadSkip::ReferenceSetUnstable => "reference set unstable",
    }
}

/// The verdict of `ours` against `fcs`, on the facts the existence set
/// holds of each (`test_support::existence_facts`): `Ok` a census line with
/// ours' surplus per kind, `Err` a fact FCS's holds that ours lacks.
fn grade(ours: &SourceExistence, fcs: &FcsRows) -> Result<String, String> {
    let surface = match ours {
        SourceExistence::Unread(why) => return Ok(format!("unread {why:?}")),
        SourceExistence::Read(s) => s,
    };
    let mine = existence_facts(&surface.index, &surface.assembly_auto_opens);
    let theirs = existence_facts(
        &ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(fcs.entities.clone()),
            extensions: fcs.extensions.clone(),
        },
        &fcs.auto_opens,
    );
    let lends_children: BTreeSet<Vec<String>> = mine
        .lends_children
        .union(&mine.lends_anything)
        .cloned()
        .collect();
    let paths = [
        ("prefix", &mine.prefixes, &theirs.prefixes),
        ("entity", &mine.entities, &theirs.entities),
        ("lends-children", &lends_children, &theirs.lends_children),
        (
            "lends-anything",
            &mine.lends_anything,
            &theirs.lends_anything,
        ),
        (
            "abbreviation-lender",
            &mine.abbreviation_lenders,
            &theirs.abbreviation_lenders,
        ),
        ("auto-open", &mine.auto_open_bases, &theirs.auto_open_bases),
    ];
    let mut lacking: Vec<String> = Vec::new();
    for (kind, ours, fcs) in paths {
        lacking.extend(
            fcs.difference(ours)
                .map(|p| format!("{kind} {}", p.join("."))),
        );
    }
    lacking.extend(
        theirs
            .extensions
            .difference(&mine.extensions)
            .map(|f| format!("extension {f:?}")),
    );
    if !lacking.is_empty() {
        return Err(format!("ours lacks facts FCS's holds: {lacking:?}"));
    }
    let n = |a: &BTreeSet<Vec<String>>, b: &BTreeSet<Vec<String>>| a.difference(b).count();
    let surplus = [
        ("prefix", n(&mine.prefixes, &theirs.prefixes)),
        ("entity", n(&mine.entities, &theirs.entities)),
        (
            "lends",
            n(&mine.lends_children, &theirs.lends_children)
                + n(&mine.lends_anything, &theirs.lends_anything),
        ),
        (
            "lender",
            n(&mine.abbreviation_lenders, &theirs.abbreviation_lenders),
        ),
        (
            "auto-open",
            n(&mine.auto_open_bases, &theirs.auto_open_bases),
        ),
        (
            "extension",
            mine.extensions.difference(&theirs.extensions).count(),
        ),
    ];
    let approximations: Vec<String> = surface
        .approximations
        .iter()
        .map(|a| format!("{a:?}"))
        .collect();
    if surplus.iter().all(|(_, k)| *k == 0) {
        Ok(format!("exact [{}]", approximations.join(",")))
    } else {
        let counts: Vec<String> = surplus.iter().map(|(k, c)| format!("{k} {c}")).collect();
        Ok(format!(
            "covers surplus({}) [{}]",
            counts.join(", "),
            approximations.join(",")
        ))
    }
}

#[test]
#[ignore = "walks the pinned project corpus; set BORZOI_PROJECT_LIST and run with --ignored under nix develop"]
fn source_existence_covers_fcs_over_the_pinned_projects() {
    let Some(list) = std::env::var_os("BORZOI_PROJECT_LIST") else {
        eprintln!("BORZOI_PROJECT_LIST unset; skipping. See the module docs.");
        return;
    };
    let projects: Vec<PathBuf> = std::env::split_paths(&list).collect();
    assert!(!projects.is_empty(), "BORZOI_PROJECT_LIST is empty");
    let mut oracle = ProjectGraphOracle::default();
    let mut manifest = Vec::new();
    let mut failures = Vec::new();
    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    for project in &projects {
        let key = checkout_key(project);
        let loaded = match load_lsp_project(project) {
            Ok(loaded) => loaded,
            Err(skip) => {
                let verdict = format!("not loaded: {}", skip_kind(&skip));
                *census.entry(verdict.clone()).or_default() += 1;
                manifest.push((key, verdict));
                continue;
            }
        };
        let unknown = ours(&loaded, Some(&MarkerRoutes::Unknown));
        let spelled = ours(&loaded, None);
        let verdict = match fcs(&loaded, &mut oracle) {
            Err(why) => {
                // Nothing to grade against: what we read is still pinned.
                let read = |r: &SourceExistence| match r {
                    SourceExistence::Read(_) => "read".to_owned(),
                    SourceExistence::Unread(why) => format!("unread {why:?}"),
                };
                format!(
                    "ungraded ({why}); unknown: {}; by spelling: {}",
                    read(&unknown),
                    read(&spelled)
                )
            }
            Ok(rows) => {
                let unknown = grade(&unknown, &rows);
                let spelled = grade(&spelled, &rows);
                if let Err(e) = &unknown {
                    failures.push(format!("{key}: {e}"));
                }
                let show = |g: &Result<String, String>| match g {
                    Ok(v) => v.clone(),
                    Err(_) => "lacks facts".to_owned(),
                };
                format!(
                    "unknown: {}; by spelling: {}",
                    show(&unknown),
                    show(&spelled)
                )
            }
        };
        let bucket = verdict
            .split(';')
            .next()
            .unwrap_or("")
            .split(['(', '['])
            .next()
            .unwrap_or("")
            .trim()
            .to_owned();
        *census.entry(bucket).or_default() += 1;
        manifest.push((key, verdict));
    }
    eprintln!("{} projects:", projects.len());
    for (bucket, n) in &census {
        eprintln!("  {n:>4} {bucket}");
    }
    assert!(
        failures.is_empty(),
        "{} projects not covered:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let manifest = Manifest::from_keyed(manifest).unwrap_or_else(|e| panic!("manifest: {e}"));
    check(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("manifests/source_existence_projects.txt"),
        &manifest,
        &format!(
            "{UPDATE_ENV}=1 BORZOI_PROJECT_LIST=… nix develop -c cargo test -p borzoi-corpus-diff \
             --test project_resolution source_existence_corpus:: -- --ignored"
        ),
    );
}
