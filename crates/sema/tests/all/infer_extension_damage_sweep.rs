//! The extension-scope gate on files the parser recovered from (#794).
//!
//! A recovered file may declare, in text our parser could not read, an
//! extension member FCS's own recovery keeps, or open a namespace that holds
//! one. The gate must still decline every call such a member could join.
//!
//! The seeds (`tests/fixtures/ext_damage_seeds`) declare or open extensions
//! and call them in the shapes where recovered text has been misread: a call
//! before its declaration in a `type … and …` group, a call in an earlier
//! member of the class that declares a C#-style extension, operator members
//! (`(*)` and `( .. .. )` among them), active-pattern members, `open` and
//! `open type` of a namespace with extensions, damage three declarations
//! before the extension, and records, unions and exceptions whose intrinsic
//! `with` members must not count. The `damaged_` seeds are counterexamples
//! found by an earlier run of this sweep. Each seed is perturbed three ways at
//! each of its tokens: the token deleted, a junk token ([`JUNK`]) inserted
//! before it, or its line truncated from it. FCS checks every case alone
//! (the census oracle).
//!
//! # The properties
//!
//! 1. **Soundness at the call.** Wherever FCS binds a use to an extension
//!    member (`IsExtension`), the gate declines that name, in that call
//!    shape (`IsInstance`), at the use.
//! 2. **Completeness of the declared names** (call-free). Every extension
//!    member FCS declares in the file (`IsExtension` on an augmentation's
//!    member, `IsCSharpExtension` on a C#-style method) is a name the file
//!    may declare: its tree's names or its damage's.
//! 3. **Monotonicity** (FCS-free, [`deleting_a_token_keeps_every_decline`]).
//!    Deleting one token of a clean seed, where that leaves the parser
//!    recovering, keeps the gate declining each name the clean seed declined
//!    at each place the name is written, except the deleted token's own names.
//!
//! The ordinary suite runs every seed unperturbed and a fixed sample of the
//! perturbations ([`SAMPLE`]); [`full_sweep`] (ignored, a pre-push gate) runs
//! them all.

use std::collections::{BTreeSet, HashMap, HashSet};

use borzoi_assembly::op_name::compile_op_name;
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, SyntaxNode, TextRange, TextSize};
use borzoi_oracle_harness::fcs_position::LineIndex;
use borzoi_sema::{
    ExtensionNames, ProjectFile, ResolvedProject, SourceFile, SyntaxRecovery, qualified_names,
    resolve_project_files,
};

use crate::common::{CensusUse, full_bcl_env, invoke_fcs_dump_census, parse_census_jsonl, temp_fs_tree};

/// How many perturbed cases the ordinary suite checks, about.
const SAMPLE: u64 = 300;

/// What a perturbation inserts before a token: delimiters, keywords that open
/// or close a declaration, and a comment opener.
const JUNK: [&str; 31] = [
    "(", ")", "=", ".", ",", ";", "|", "[", "]", "{", "}", "\"", "->", "<", ">", "@", "(*", "with",
    "end", "type", "member", "static", "new", "and", "let", "in", "do", "then", "else", "begin",
    "module",
];

/// The accessor spellings a member name may be called by.
const ACCESSOR_PREFIXES: [&str; 4] = ["get_", "set_", "add_", "remove_"];

/// One seed: its file stem and its text.
struct Seed {
    name: String,
    source: String,
}

fn seeds() -> Vec<Seed> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/ext_damage_seeds");
    let mut seeds: Vec<Seed> = std::fs::read_dir(dir)
        .expect("the seed directory")
        .map(|entry| entry.expect("a seed").path())
        .filter(|path| path.extension().is_some_and(|e| e == "fs"))
        .map(|path| Seed {
            name: path
                .file_stem()
                .expect("a file stem")
                .to_string_lossy()
                .into_owned(),
            source: std::fs::read_to_string(&path).expect("a seed's text"),
        })
        .collect();
    seeds.sort_by(|a, b| a.name.cmp(&b.name));
    assert!(seeds.len() >= 20, "{} seeds", seeds.len());
    seeds
}

/// One perturbation of a seed at one of its tokens.
#[derive(Debug, Clone, Copy)]
enum Perturbation {
    Delete,
    Insert(&'static str),
    Truncate,
}

impl Perturbation {
    fn all() -> impl Iterator<Item = Perturbation> {
        [Perturbation::Delete, Perturbation::Truncate]
            .into_iter()
            .chain(JUNK.into_iter().map(Perturbation::Insert))
    }

    fn apply(self, source: &str, at: TextRange) -> String {
        let (start, end) = (usize::from(at.start()), usize::from(at.end()));
        match self {
            Perturbation::Delete => format!("{}{}", &source[..start], &source[end..]),
            Perturbation::Insert(junk) => format!("{}{junk} {}", &source[..start], &source[start..]),
            Perturbation::Truncate => {
                let eol = source[start..].find('\n').map_or(source.len(), |k| start + k);
                format!("{}{}", &source[..start], &source[eol..])
            }
        }
    }
}

/// The non-trivia tokens of `source` as our parser reads it.
fn significant_tokens(source: &str) -> Vec<(TextRange, String)> {
    parse(source)
        .root
        .descendants_with_tokens()
        .filter_map(|el| el.into_token())
        .filter(|t| !t.kind().is_trivia() && !t.text_range().is_empty())
        .map(|t| (t.text_range(), t.text().to_string()))
        .collect()
}

/// One file FCS and the gate are both asked about.
struct Case {
    label: String,
    source: String,
}

/// Every seed unperturbed, and every perturbation of it (each distinct text
/// once).
fn all_cases(seeds: &[Seed]) -> Vec<Case> {
    let mut seen = HashSet::new();
    let mut cases = Vec::new();
    for seed in seeds {
        let mut push = |label: String, source: String| {
            if seen.insert(source.clone()) {
                cases.push(Case { label, source });
            }
        };
        push(format!("{}/clean", seed.name), seed.source.clone());
        for (range, _) in significant_tokens(&seed.source) {
            for p in Perturbation::all() {
                push(
                    format!("{}/{p:?}@{}", seed.name, u32::from(range.start())),
                    p.apply(&seed.source, range),
                );
            }
        }
    }
    cases
}

/// FNV-1a, for a sample that is fixed across runs and platforms.
fn fnv(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// One file resolved alone, as the gate sees it.
struct Resolved {
    root: SyntaxNode,
    project: ResolvedProject,
    recovered: bool,
}

impl Resolved {
    fn of(source: &str) -> Resolved {
        let parsed = parse(source);
        let recovered = !parsed.errors.is_empty();
        let recovery = SyntaxRecovery::of(&parsed);
        let file = ImplFile::cast(parsed.root.clone()).expect("an implementation file");
        let files = vec![SourceFile::Impl(file)];
        let project: Vec<ProjectFile> = files
            .iter()
            .cloned()
            .zip(qualified_names(&files, &["Case.fs".into()]))
            .map(|(f, q)| ProjectFile::new(f, q, recovery.clone()))
            .collect();
        Resolved {
            root: parsed.root,
            project: resolve_project_files(&project, full_bcl_env()),
            recovered,
        }
    }

    /// Whether the gate declines a call of `name` in shape `is_static` at
    /// `at`.
    fn declines(&self, name: &str, is_static: bool, at: TextSize) -> bool {
        borzoi_sema::test_support::extension_gate_decline(
            self.project.file(0),
            &self.root,
            full_bcl_env(),
            name,
            is_static,
            at,
        )
        .is_some()
    }

    /// The extension-member names the file may declare.
    fn declared(&self) -> ExtensionNames {
        borzoi_sema::test_support::declared_extension_names(self.project.file(0), &self.root)
    }
}

/// The member name `text` (the text of an FCS use's range) spells, compiled
/// as the gate is asked it, and how many bytes from the range's end it
/// starts. `None` for text that spells no single name.
fn member_name(text: &str) -> Option<(String, usize)> {
    if let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        // An operator's definition: `(*)`, `( .. .. )`, `(+.)`.
        let joined: String = inner.chars().filter(|c| !c.is_whitespace()).collect();
        let name = match joined.as_str() {
            "*" => "op_Multiply".to_string(),
            "...." => "op_RangeStep".to_string(),
            other => compile_op_name(other).into_owned(),
        };
        return Some((name, text.len()));
    }
    // The last segment after a `.` outside double backticks.
    let mut quoted = false;
    let mut last = 0;
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(b"``") {
            quoted = !quoted;
            i += 2;
            continue;
        }
        if bytes[i] == b'.' && !quoted {
            last = i + 1;
        }
        i += 1;
    }
    let spelled = &text[last..];
    let name = spelled
        .strip_prefix("``")
        .and_then(|t| t.strip_suffix("``"))
        .unwrap_or(spelled);
    if name.is_empty() || name.chars().any(char::is_whitespace) {
        return None;
    }
    Some((compile_op_name(name).into_owned(), spelled.len()))
}

/// What grading one case found.
#[derive(Default)]
struct Graded {
    violations: Vec<String>,
    calls: usize,
    declarations: usize,
}

/// Grade `case` against FCS's census `uses` of it.
fn grade(case: &Case, uses: &[CensusUse]) -> Graded {
    let resolved = Resolved::of(&case.source);
    let declared = resolved.declared();
    let index = LineIndex::new(&case.source);
    let mut graded = Graded::default();
    for u in uses.iter().filter(|u| u.is_member) {
        let (start, end) = u.use_range_bytes(&index);
        let Some(text) = case.source.get(start..end) else {
            continue;
        };
        let Some((name, spelled)) = member_name(text) else {
            continue;
        };
        if u.is_from_definition {
            if !(u.is_extension || u.is_csharp_extension) {
                continue;
            }
            // A C#-style method is declared static and called on a value.
            let is_static = !u.is_csharp_extension && !u.is_instance;
            graded.declarations += 1;
            if !declared.may_have(&name, is_static) {
                graded.violations.push(format!(
                    "{}: FCS declares extension `{name}` (static: {is_static}) at {start}, \
                     which the file's names miss\n{}",
                    case.label, case.source
                ));
            }
        } else if u.is_extension {
            let is_static = !u.is_instance;
            graded.calls += 1;
            let at = TextSize::new(u32::try_from(end - spelled).expect("a small case"));
            if !resolved.declines(&name, is_static, at) {
                graded.violations.push(format!(
                    "{}: FCS binds `{text}` at {start} to an extension `{name}` \
                     (static: {is_static}), which the gate lets stand\n{}",
                    case.label, case.source
                ));
            }
        }
    }
    graded
}

/// Grade `cases`, each checked alone by FCS, and assert properties 1 and 2
/// hold on every one; each unperturbed seed must also grade something, or
/// nothing at all for the control whose `with` members are intrinsic.
fn check(cases: &[Case]) {
    let rows: Vec<(String, &str)> = cases
        .iter()
        .enumerate()
        .map(|(k, c)| (format!("case_{k}.fs"), c.source.as_str()))
        .collect();
    let rows_ref: Vec<(&str, &str)> = rows.iter().map(|(p, s)| (p.as_str(), *s)).collect();
    let (root, written) = temp_fs_tree("ext_damage_sweep", &rows_ref);
    let paths: Vec<_> = written.iter().map(|(p, _)| p.clone()).collect();
    let census = parse_census_jsonl(&invoke_fcs_dump_census(&paths));
    let _ = std::fs::remove_dir_all(&root);
    let by_path: HashMap<String, _> = census
        .iter()
        .map(|c| {
            let name = std::path::Path::new(&c.path)
                .file_name()
                .expect("a file name")
                .to_string_lossy()
                .into_owned();
            (name, c)
        })
        .collect();

    let mut violations = Vec::new();
    let (mut calls, mut declarations, mut recovered) = (0, 0, 0);
    for (k, case) in cases.iter().enumerate() {
        let Some(file) = by_path.get(&format!("case_{k}.fs")).filter(|c| c.ok) else {
            violations.push(format!("{}: FCS did not check it", case.label));
            continue;
        };
        let graded = grade(case, &file.uses);
        if let Some(seed) = case.label.strip_suffix("/clean") {
            let control = seed == "intrinsic_with_members";
            let graded_any = graded.calls + graded.declarations > 0;
            if graded_any == control {
                violations.push(format!(
                    "{}: {} calls and {} declarations graded",
                    case.label, graded.calls, graded.declarations
                ));
            }
        }
        calls += graded.calls;
        declarations += graded.declarations;
        recovered += usize::from(!parse(&case.source).errors.is_empty());
        violations.extend(graded.violations);
    }
    eprintln!(
        "{} cases ({recovered} recovered): {calls} extension calls and {declarations} extension \
         declarations graded, {} violations",
        cases.len(),
        violations.len()
    );
    report(&violations);
}

/// Print every violation, then fail on the first few.
fn report(violations: &[String]) {
    for v in violations {
        eprintln!("{v}");
    }
    assert!(
        violations.is_empty(),
        "{} violations; the first 20:\n{}",
        violations.len(),
        violations
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn sampled_perturbations() {
    let cases = all_cases(&seeds());
    let stride = (cases.len() as u64 / SAMPLE).max(1);
    let sample: Vec<Case> = cases
        .into_iter()
        .filter(|c| c.label.ends_with("/clean") || fnv(&c.label) % stride == 0)
        .collect();
    check(&sample);
}

#[test]
#[ignore = "every perturbation of every seed: a pre-push gate"]
fn full_sweep() {
    check(&all_cases(&seeds()));
}

/// The names a token may contribute to a gate query: its text, unquoted and
/// compiled, and each accessor spelling of it.
fn token_names(text: &str) -> Vec<String> {
    let unquoted = text
        .strip_prefix("``")
        .and_then(|t| t.strip_suffix("``"))
        .unwrap_or(text);
    let mut names = vec![unquoted.to_string(), compile_op_name(text).into_owned()];
    names.extend(ACCESSOR_PREFIXES.iter().map(|p| format!("{p}{unquoted}")));
    if text == "(*)" {
        names.push("op_Multiply".into());
    }
    if text == ".." {
        names.push("op_RangeStep".into());
    }
    names
}

/// Property 3: deleting a token of a clean seed, where the parser then
/// recovers, keeps every decline the clean seed's gate made at each place its
/// name is written (the file's start included), but for the names the
/// deleted token spells itself.
#[test]
fn deleting_a_token_keeps_every_decline() {
    let mut violations = Vec::new();
    let mut checked = 0usize;
    for seed in seeds() {
        let clean = Resolved::of(&seed.source);
        if clean.recovered {
            continue;
        }
        let tokens = significant_tokens(&seed.source);
        // Each name a token spells, with where it is written.
        let mut written: HashMap<String, BTreeSet<TextSize>> = HashMap::new();
        for (range, text) in &tokens {
            for name in token_names(text) {
                let at = written.entry(name).or_default();
                at.insert(TextSize::from(0));
                at.insert(range.start());
            }
        }
        let declined: Vec<(&String, bool)> = written
            .keys()
            .flat_map(|name| [(name, false), (name, true)])
            .filter(|&(name, is_static)| clean.declines(name, is_static, TextSize::from(0)))
            .collect();
        for (range, text) in &tokens {
            let damaged = Perturbation::Delete.apply(&seed.source, *range);
            let resolved = Resolved::of(&damaged);
            if !resolved.recovered {
                // A different program, not a damaged one.
                continue;
            }
            let own: HashSet<String> = token_names(text).into_iter().collect();
            for &(name, is_static) in &declined {
                if own.contains(name) {
                    continue;
                }
                for &at in &written[name] {
                    if at == range.start() && at != TextSize::from(0) {
                        continue;
                    }
                    let moved = if at > range.start() {
                        at - range.len()
                    } else {
                        at
                    };
                    checked += 1;
                    if !resolved.declines(name, is_static, moved) {
                        violations.push(format!(
                            "{}: deleting `{text}` at {} lets `{name}` (static: {is_static}) \
                             stand at {}\n{damaged}",
                            seed.name,
                            u32::from(range.start()),
                            u32::from(moved)
                        ));
                    }
                }
            }
        }
    }
    eprintln!("{checked} declines checked, {} violations", violations.len());
    assert!(checked > 1000, "only {checked} declines checked");
    report(&violations);
}
