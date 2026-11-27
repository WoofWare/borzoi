//! Generative differential: `<ProjectReference>`s whose `Include` reads a
//! name the walk doubts, against the real MSBuild evaluator (the oracle's
//! `itemsMeta` op).
//!
//! A reference list the walk publishes as certain (neither
//! `ParsedProject::project_references_uncertain` nor
//! `project_references_incomplete`) is MSBuild's exactly: no phantom edge, and
//! no edge missing. An `Include` behind a gate the walk could not decide, or
//! one whose value it cannot compute from names it holds exactly, is an edge
//! MSBuild may have that the list lacks, so the list is incomplete (#1181);
//! an `Include` that reads a name the walk doubts (a write it refused to
//! compute, one under a gate it could not decide, a copy of either) is an
//! edge MSBuild has at a path the walk does not know, so the list is
//! uncertain (#1098).
//!
//! [`doubted_read_sweep`] generates writes of two names (hostile literals,
//! functions the walk does not compute, copies, gates reading either name or
//! one the walk cannot decide) and references reading them (directly, through
//! a member, after whitespace MSBuild trims, under gates of their own or of
//! their group), and holds every certain list to MSBuild's items: no phantom
//! edge, and no item of a reference whose `Include` reads a doubted name
//! missing. A fixed-seed sweep, so a failure reproduces exactly.

mod common;

use std::collections::{BTreeSet, HashMap};
use std::path::{Component, Path, PathBuf};

use borzoi_msbuild::PropertyRead;
use borzoi_oracle_harness::hostile::{self, Dimension, coverage, value};
use common::{Oracle, SplitMix64, parse_fsproj_with_imports};

/// A gate MSBuild evaluates to true and the walk cannot decide.
const UNSUPPORTED_TRUE: &str = " Condition=\"'É' == 'é'\"";
/// [`UNSUPPORTED_TRUE`]'s false twin.
const UNSUPPORTED_FALSE: &str = " Condition=\"'É' == 'Ê'\"";

/// What `FullPath` does to a spelling: backslashes become separators and
/// `.`/`..` collapse lexically. Case is kept on both sides.
fn lexical(path: &str) -> PathBuf {
    let path = path.replace('\\', "/");
    let mut out = PathBuf::new();
    for component in Path::new(&path).components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            other => out.push(other),
        }
    }
    out
}

/// A path the walker published, as the LSP reads it: lexically normalised
/// (`.` and `..` folded, which `workspace::lexically_normalize` does too) and
/// nothing else. A backslash stays, so a walker that publishes one where
/// MSBuild's `FullPath` has a separator fails the comparison rather than
/// being repaired by it.
fn published(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            other => out.push(other),
        }
    }
    out
}

/// A project directory under `root`, beside a referenced project, returning
/// the project's path.
fn layout(root: &Path) -> PathBuf {
    std::fs::create_dir_all(root.join("proj")).unwrap();
    std::fs::write(root.join("proj/A.fsproj"), "<Project />").unwrap();
    root.join("proj/Demo.fsproj")
}

/// The names the doubted-read sweep writes and reads.
const READ_NAMES: [&str; 2] = ["P", "Q"];

/// A function the walk does not compute, which MSBuild evaluates to `w`: a
/// write of it is one the walk refuses, so that it holds no value of the
/// name.
const REFUSED_BODY: &str = "$([System.String]::Copy('w'))";

/// The hostile values a literal of the doubted-read sweep is drawn from: a
/// name's last write, as nothing puts a value back, and none holding a NUL,
/// raw or escaped, which is in no path MSBuild gives a `FullPath`, the
/// metadatum the oracle reads an item by.
fn read_sweep_values(plain: &str) -> Vec<hostile::Entry<value::Value>> {
    value::alphabet().filtered(|entry| {
        let text = entry.value.render(plain);
        entry.value.write == value::Write::Final
            && !text.contains('\0')
            && !text.to_ascii_lowercase().contains("%00")
    })
}

/// The hostile file names a literal of the doubted-read sweep is drawn from,
/// as its value is spliced into a reference's file name
/// ([`hostile::name::as_text`], as `hostile::value` asks of a value used as a
/// name): those XML can spell, holding no NUL, raw or escaped
/// ([`read_sweep_values`]).
fn read_sweep_names(plain: &str) -> Vec<hostile::Entry<String>> {
    hostile::name::as_text(plain, "")
        .into_iter()
        .filter(|entry| {
            entry.value.chars().all(hostile::xml::representable)
                && !entry.value.contains('\0')
                && !entry.value.to_ascii_lowercase().contains("%00")
        })
        .collect()
}

/// A write's body in the doubted-read sweep: a hostile or plain literal (a
/// value, or a file name), a function the walk does not compute, or a read
/// of the other name.
fn read_sweep_body(rng: &mut SplitMix64, other: &str) -> hostile::Drawn<String> {
    match rng.below(5) {
        0 => {
            let plain = *rng.pick(&["a", "lib", "B1"]);
            match hostile::sample(&read_sweep_values(plain), rng.next()) {
                Some(entry) => hostile::Drawn::of(entry).map(|v| v.render(plain)),
                None => hostile::Drawn::plain(plain.to_owned()),
            }
        }
        4 => {
            let plain = *rng.pick(&["a", "lib", "B1"]);
            match hostile::sample(&read_sweep_names(plain), rng.next()) {
                Some(entry) => hostile::Drawn::of(entry),
                None => hostile::Drawn::plain(plain.to_owned()),
            }
        }
        1 => hostile::Drawn::plain(REFUSED_BODY.to_owned()),
        2 => hostile::Drawn::plain(format!("$({other})")),
        _ => hostile::Drawn::plain(format!("$({other}.Length)")),
    }
}

/// A write's condition in the doubted-read sweep: none, one reading the name
/// itself or the other, and one the walk cannot decide either way.
fn read_sweep_condition(rng: &mut SplitMix64, name: &str, other: &str) -> String {
    match rng.below(5) {
        0 => String::new(),
        1 => format!(" Condition=\"'$({name})' == ''\""),
        2 => format!(" Condition=\"'$({other})' == 'a'\""),
        3 => UNSUPPORTED_TRUE.to_owned(),
        _ => UNSUPPORTED_FALSE.to_owned(),
    }
}

/// One write of a doubted-read document.
struct ReadWrite {
    name: &'static str,
    condition: String,
    body: hostile::Drawn<String>,
}

/// One `<ProjectReference>` of a doubted-read document.
struct ReadReference {
    include: String,
    /// The names its `Include` reads.
    reads: Vec<&'static str>,
    /// Its own gate, and its group's (each with its leading space, or empty).
    condition: String,
    group_condition: String,
    /// Whether its group stands in a `<When>` the walk cannot decide.
    in_undecided_arm: bool,
}

/// One document of the doubted-read sweep: writes of `P` and `Q`, then
/// `<ProjectReference>`s, each with an `Origin` metadatum naming it.
struct ReadDocument {
    writes: Vec<ReadWrite>,
    references: Vec<ReadReference>,
}

/// What may stand between `$(` and a reference's receiver: nothing, and the
/// whitespace MSBuild trims there, ASCII and not (the `&#…;` reference is
/// written into the attribute as is, so that XML keeps a tab a tab).
const RECEIVER_PADDING: &[&str] = &["", "", " ", "&#9;", "&#xA0;", "&#x2003;"];

/// A reference's or its group's gate: none, one reading a name, and one the
/// walk cannot decide.
fn read_sweep_reference_condition(rng: &mut SplitMix64) -> String {
    let name = *rng.pick(&READ_NAMES);
    match rng.below(9) {
        0 => format!(" Condition=\"'$({name})' != ''\""),
        1 => UNSUPPORTED_TRUE.to_owned(),
        // A toolset name the walk holds no value of without a startup
        // directory, and a gate false whatever any name holds.
        2 => " Condition=\"'$(MSBuildStartupDirectory)' != ''\"".to_owned(),
        3 => " Condition=\"false\"".to_owned(),
        _ => String::new(),
    }
}

impl ReadDocument {
    fn generate(rng: &mut SplitMix64) -> Self {
        let writes = (0..2 + rng.below(3))
            .map(|_| {
                let at = rng.below(2);
                let (name, other) = (READ_NAMES[at], READ_NAMES[1 - at]);
                let condition = read_sweep_condition(rng, name, other);
                let body = read_sweep_body(rng, other);
                ReadWrite {
                    name,
                    condition,
                    body,
                }
            })
            .collect();
        let references = (0..1 + rng.below(3))
            .map(|i| {
                let name = *rng.pick(&READ_NAMES);
                let pad = *rng.pick(RECEIVER_PADDING);
                let trail = *rng.pick(RECEIVER_PADDING);
                // MSBuild reads a receiver past padding only before a member:
                // a bare `$( P)` or `$(P )` reads nothing (MSBuild 10.0.401).
                let bare = |reads: &[&'static str]| -> Vec<&'static str> {
                    if pad.is_empty() && trail.is_empty() {
                        reads.to_vec()
                    } else {
                        Vec::new()
                    }
                };
                let (include, reads) = match rng.below(3) {
                    0 => (format!("E{i}_$({pad}{name}{trail}).fsproj"), bare(&[name])),
                    1 => (format!("E{i}_$({pad}{name}.Length).fsproj"), vec![name]),
                    _ => {
                        let mut reads = bare(&["P"]);
                        reads.push("Q");
                        (format!("E{i}_$({pad}P{trail})_$(Q).fsproj"), reads)
                    }
                };
                ReadReference {
                    include,
                    reads,
                    condition: read_sweep_reference_condition(rng),
                    group_condition: read_sweep_reference_condition(rng),
                    in_undecided_arm: rng.below(5) == 0,
                }
            })
            .collect();
        ReadDocument { writes, references }
    }

    /// A document that writes `value` to `P`, copies it to `Q`, puts `P`
    /// back, and references `Q`: the witness of a value a later write puts
    /// back, which still reaches the reference.
    fn copied_before_reset(value: hostile::Drawn<String>) -> Self {
        let write = |name, body: hostile::Drawn<String>| ReadWrite {
            name,
            condition: String::new(),
            body,
        };
        ReadDocument {
            writes: vec![
                write("P", value),
                write("Q", hostile::Drawn::plain("$(P)".to_owned())),
                write("P", hostile::Drawn::plain("lib".to_owned())),
            ],
            references: vec![ReadReference {
                include: "E0_$(Q).fsproj".to_owned(),
                reads: vec!["Q"],
                condition: String::new(),
                group_condition: String::new(),
                in_undecided_arm: false,
            }],
        }
    }

    /// A document whose one reference reads `value`, the last write of `P`,
    /// beside a name the walk refused: the witness of `value`'s dimension.
    fn witness(value: hostile::Drawn<String>) -> Self {
        ReadDocument {
            writes: vec![
                ReadWrite {
                    name: "Q",
                    condition: String::new(),
                    body: hostile::Drawn::plain(REFUSED_BODY.to_owned()),
                },
                ReadWrite {
                    name: "P",
                    condition: String::new(),
                    body: value,
                },
            ],
            references: vec![ReadReference {
                include: "E0_$(P)_$(Q).fsproj".to_owned(),
                reads: vec!["P", "Q"],
                condition: String::new(),
                group_condition: String::new(),
                in_undecided_arm: false,
            }],
        }
    }

    fn xml(&self) -> String {
        let mut xml = String::from("<Project>\n");
        for write in &self.writes {
            let text = write
                .body
                .value
                .replace('&', "&amp;")
                .replace('<', "&lt;")
                .replace('>', "&gt;");
            xml.push_str(&format!(
                "  <PropertyGroup><{name}{condition}>{text}</{name}></PropertyGroup>\n",
                name = write.name,
                condition = write.condition
            ));
        }
        for (i, reference) in self.references.iter().enumerate() {
            let group = format!(
                "<ItemGroup{group}><ProjectReference Include=\"{include}\"{own} Origin=\"E{i}\" /></ItemGroup>",
                group = reference.group_condition,
                include = reference.include,
                own = reference.condition,
            );
            if reference.in_undecided_arm {
                xml.push_str(&format!(
                    "  <Choose><When{UNSUPPORTED_TRUE}>{group}</When></Choose>\n"
                ));
            } else {
                xml.push_str(&format!("  {group}\n"));
            }
        }
        xml.push_str("</Project>\n");
        xml
    }

    /// The hostile dimensions a reference MSBuild evaluated (`evaluated`, by
    /// reference) reads: those of each name's last write, where that write is
    /// unconditional (so MSBuild makes it) and such a reference reads its
    /// name. A write a later one replaces, or one under a gate, may reach no
    /// reference.
    ///
    /// A name's value is followed through copies (`$(Other)`,
    /// `$(Other.Length)`) to the write that made it. `None` where that is not
    /// known: a write on the way stands under a gate, which MSBuild may make
    /// or skip, so the census records nothing rather than call the read plain.
    fn read_dimensions(&self, evaluated: &[bool]) -> Option<BTreeSet<Dimension>> {
        let mut dimensions = BTreeSet::new();
        for name in READ_NAMES {
            let read = self
                .references
                .iter()
                .zip(evaluated)
                .any(|(r, evaluated)| *evaluated && r.reads.contains(&name));
            if read {
                dimensions.extend(self.provenance(name, self.writes.len())?);
            }
        }
        Some(dimensions)
    }

    /// The dimensions of the value `name` holds after the first `before`
    /// writes ([`Self::read_dimensions`]).
    fn provenance(&self, name: &str, before: usize) -> Option<BTreeSet<Dimension>> {
        let Some(at) = self.writes[..before].iter().rposition(|w| w.name == name) else {
            return Some(BTreeSet::new());
        };
        let write = &self.writes[at];
        if !write.condition.is_empty() {
            return None;
        }
        let mut dimensions: BTreeSet<Dimension> = write.body.hostile.clone();
        for other in READ_NAMES {
            if write.body.value.starts_with(&format!("$({other}")) {
                dimensions.extend(self.provenance(other, at)?);
            }
        }
        Some(dimensions)
    }

    /// Every dimension any write carries.
    fn drawn_dimensions(&self) -> BTreeSet<Dimension> {
        self.writes
            .iter()
            .flat_map(|w| w.body.hostile.iter().copied())
            .collect()
    }
}

/// What the doubted-read sweep saw.
#[derive(Debug, Default)]
struct ReadCensus {
    cases: usize,
    msbuild_rejects: usize,
    committed: usize,
    /// Cases where a reference read a name the walk doubts and MSBuild holds
    /// an item of it: the walk owes a decline, whether it kept the item or
    /// not.
    owed: usize,
}

/// The hostile values the doubted-read sweep cannot carry.
const READ_EXCLUDED: &[(Dimension, &str)] = &[(
    Dimension::NonUtf8,
    "a property value is text: no project spells bytes that are not UTF-8 (`name::as_text`)",
)];

/// How one doubted-read document went.
enum ReadOutcome {
    MsbuildRejects,
    Declined { owed: bool },
    Committed,
}

/// Grade `document` against MSBuild's items: a certain list holds no phantom
/// edge, and lacks no item of a reference that reads a name the walk doubts
/// (#1098). Each item is matched to its reference by its `Origin`
/// metadatum on MSBuild's side and by its element on the walk's, so a value
/// that splits into several items or moves the marker out of the file name
/// is graded all the same.
fn grade_read_document(oracle: &mut Oracle, document: &ReadDocument) -> (ReadOutcome, Vec<bool>) {
    let xml = document.xml();
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, &xml).unwrap();
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed XML parses");
    let Some(theirs) = oracle.items_meta(&xml, &proj, "ProjectReference", &["FullPath", "Origin"])
    else {
        return (ReadOutcome::MsbuildRejects, Vec::new());
    };
    // MSBuild's items of reference `i`, and the walk's, by full path.
    let theirs_of = |i: usize| -> Vec<PathBuf> {
        let origin = format!("E{i}");
        theirs
            .iter()
            .filter(|(_, meta)| meta.get("Origin") == Some(&origin))
            .map(|(_, meta)| lexical(&meta["FullPath"]))
            .collect()
    };
    let starts: Vec<usize> = xml
        .match_indices("<ProjectReference ")
        .map(|(at, _)| at)
        .collect();
    let ours_of = |i: usize| -> Vec<PathBuf> {
        parsed
            .project_references
            .iter()
            .filter(|item| starts.iter().position(|s| *s == item.span.start) == Some(i))
            .map(|item| published(&item.include))
            .collect()
    };
    let doubted = |name: &str| {
        !matches!(
            parsed.property(name),
            PropertyRead::Value(_) | PropertyRead::Unset
        )
    };
    // Which references MSBuild evaluated to an item: those a hostile value
    // read reaches what is graded through.
    let evaluated: Vec<bool> = (0..document.references.len())
        .map(|i| !theirs_of(i).is_empty())
        .collect();
    let owed = document
        .references
        .iter()
        .enumerate()
        .any(|(i, reference)| {
            reference.reads.iter().any(|name| doubted(name)) && !theirs_of(i).is_empty()
        });
    let claim = common::reference_claim(&parsed);
    if claim == common::ReferenceClaim::Nothing {
        return (ReadOutcome::Declined { owed }, evaluated);
    }
    // A reference MSBuild made reading a name the walk doubts may hold
    // another path in another world, even where this one's agrees (#1098). An
    // incomplete list may lack such a reference, but may not keep one: the
    // LSP follows every edge it keeps. A certain list may do neither.
    let retained_doubted = document
        .references
        .iter()
        .enumerate()
        .find(|(i, reference)| {
            reference.reads.iter().any(|name| doubted(name))
                && !theirs_of(*i).is_empty()
                && (claim == common::ReferenceClaim::Exact || !ours_of(*i).is_empty())
        });
    assert!(
        retained_doubted.is_none(),
        "#1098: the list ({claim:?}) holds reference E{}, which MSBuild made reading a name the \
         walk doubts:\n{xml}\nours: {:#?}",
        retained_doubted.map_or(0, |(i, _)| i),
        parsed.project_references
    );
    let all_ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| published(&item.include))
        .collect();
    let all_theirs: Vec<PathBuf> = theirs
        .iter()
        .map(|(_, meta)| lexical(&meta["FullPath"]))
        .collect();
    if let Err(failure) = common::check_reference_claim(claim, &all_ours, &all_theirs) {
        panic!("{failure}\n{xml}");
    }
    assert_eq!(
        parsed.project_references.len(),
        (0..document.references.len())
            .map(|i| ours_of(i).len())
            .sum::<usize>(),
        "every item the walk captured is of one reference:\n{xml}"
    );
    for (i, reference) in document.references.iter().enumerate() {
        let reads = &reference.reads;
        let (ours, mut unmatched) = (ours_of(i), theirs_of(i));
        for path in &ours {
            let Some(at) = unmatched.iter().position(|p| p == path) else {
                panic!(
                    "phantom edge {} of reference E{i}:\n{xml}\nours: {ours:#?}\ntheirs: {:#?}",
                    path.display(),
                    theirs_of(i)
                );
            };
            unmatched.remove(at);
        }
        // A certain list is MSBuild's whole list (#1181): an edge missing
        // from it is a wrong answer whatever its `Include` reads, and one
        // reading a doubted name is #1098 as well.
        assert!(
            unmatched.is_empty() || claim == common::ReferenceClaim::Within,
            "the list is certain without {unmatched:?} of reference E{i} (whose `Include` reads \
             {reads:?}, doubted: {}):\n{xml}\nours: {ours:#?}",
            reads.iter().any(|name| doubted(name))
        );
    }
    if claim == common::ReferenceClaim::Within {
        return (ReadOutcome::Declined { owed }, evaluated);
    }
    (ReadOutcome::Committed, evaluated)
}

/// #1098: a `<ProjectReference>` whose `Include` reads a name the walk
/// doubts (a write it refused to compute, one under a gate it could not
/// decide, a copy of either) is no edge a list published as certain may
/// lack. Every case is held to no phantom edge as well. Each hostile
/// dimension's witness runs first, so that every one is graded whatever the
/// seed draws.
fn doubted_read_sweep(oracle: &mut Oracle, seed: u64, cases: usize) -> ReadCensus {
    let census = coverage::open(file!(), "reference_reads", READ_EXCLUDED);
    let excluded: BTreeSet<Dimension> = READ_EXCLUDED.iter().map(|(d, _)| *d).collect();
    // A plain witness, and one of each hostile value and file name, so that
    // the census owes nothing to what the seed draws.
    let witnesses: Vec<ReadDocument> = std::iter::once(hostile::Drawn::plain("lib".to_owned()))
        .chain(
            read_sweep_values("lib")
                .iter()
                .filter(|entry| !excluded.contains(&entry.dimension))
                .map(|entry| hostile::Drawn::of(entry).map(|v| v.render("lib"))),
        )
        .chain(read_sweep_names("lib").iter().map(hostile::Drawn::of))
        .map(ReadDocument::witness)
        // A value a later write puts back reaches a reference through a copy
        // made before the reset.
        .chain(
            value::alphabet()
                .filtered(|entry| entry.value.write == value::Write::ThenPlain)
                .iter()
                .map(|entry| {
                    ReadDocument::copied_before_reset(
                        hostile::Drawn::of(entry).map(|v| v.render("lib")),
                    )
                }),
        )
        .collect();
    let mut rng = SplitMix64(seed);
    let mut tally = ReadCensus::default();
    let mut witnesses = witnesses.into_iter();
    loop {
        let (document, witness) = match witnesses.next() {
            Some(document) => (document, true),
            None if tally.cases < cases => (ReadDocument::generate(&mut rng), false),
            None => break,
        };
        if document
            .drawn_dimensions()
            .iter()
            .any(|d| excluded.contains(d))
        {
            continue;
        }
        let (outcome, evaluated) = grade_read_document(oracle, &document);
        // A project MSBuild rejects graded no reference: no value reached one.
        let verdict = match outcome {
            ReadOutcome::MsbuildRejects => None,
            ReadOutcome::Declined { .. } => Some("decline"),
            ReadOutcome::Committed => Some("commit"),
        };
        if let Some(verdict) = verdict
            && evaluated.iter().any(|e| *e)
            && let Some(read) = document.read_dimensions(&evaluated)
        {
            census.reached(&read, verdict);
        }
        if witness {
            continue;
        }
        tally.cases += 1;
        match outcome {
            ReadOutcome::MsbuildRejects => tally.msbuild_rejects += 1,
            ReadOutcome::Declined { owed } => tally.owed += usize::from(owed),
            ReadOutcome::Committed => tally.committed += 1,
        }
    }
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         fsproj_project_reference_read_diff doubted_reads",
    );
    tally
}

/// [`doubted_read_sweep`] at a fixed seed.
#[test]
fn doubted_reads_leave_no_certain_list_short() {
    let tally = doubted_read_sweep(&mut Oracle::spawn(), 0x0109_80d0_b7ed, 1_500);
    eprintln!("doubted-read sweep: {tally:?}");
    assert!(tally.owed >= 40, "{tally:?}");
    assert!(tally.committed >= 100, "{tally:?}");
}

/// The fresh-seed twin of [`doubted_reads_leave_no_certain_list_short`].
#[test]
#[ignore = "fresh-seed soak; run with --ignored"]
fn doubted_reads_soak() {
    let (seed, cases) = common::soak_parameters("doubted reads", 2000);
    doubted_read_sweep(&mut Oracle::spawn(), seed, cases);
}

/// #1098's documents, and the routes review found around its first fix, each
/// pinned against MSBuild's items: MSBuild holds the reference, and the walk,
/// which cannot compute it, publishes no certain list without it.
#[test]
fn a_reference_reading_a_refused_name_is_no_certain_omission() {
    let refused = REFUSED_BODY;
    let rows = [
        // The issue's: a refused write, then a refused write under a gate
        // reading it.
        format!(
            "<PropertyGroup><TF>{refused}</TF></PropertyGroup>\
             <PropertyGroup><TF Condition=\"'$(TF)' == ''\">{refused}</TF></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"$(TF.Length).fsproj\" /></ItemGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        // A function the walk does not model on the refused name: the
        // expansion stops at it before it reports the read.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"$(P.Substring(1)).fsproj\" /></ItemGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        // An `Exclude` reading it, which the walk drops the element for.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" Exclude=\"$(P)\" /></ItemGroup>"
        ),
        // A gate reading it, which the walk skips the reference under, on the
        // reference and on its group.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"$(P).fsproj\" Condition=\"'$(P)' != ''\" /></ItemGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <ItemGroup Condition=\"'$(P)' != ''\"><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        // An arm of a `<Choose>` the walk cannot decide.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        // A nested `<When>` that a write of the undecided branch around it
        // opens: false on the value before the `<Choose>`, true on the
        // branch's own.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>one</X></PropertyGroup>\
             <Choose><When Condition=\"'$(X)' == 'one'\">\
             <ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose></When></Choose>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        // A gate on a toolset name the walk holds no value of without a
        // startup directory.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"$(P).fsproj\" Condition=\"'$(MSBuildStartupDirectory)' != ''\" /></ItemGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
        // A no-break space before the receiver, which MSBuild trims.
        format!(
            "<PropertyGroup><P>{refused}</P></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"E_$(&#xA0;P.Length).fsproj\" /></ItemGroup>\
             <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>"
        ),
    ];
    let mut oracle = Oracle::spawn();
    for row in rows {
        let xml = format!("<Project>{row}</Project>");
        let dir = tempfile::TempDir::new().expect("tempdir");
        let root =
            borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
        let proj = layout(&root);
        std::fs::write(&proj, &xml).unwrap();
        let theirs = oracle
            .items(&xml, &proj, "ProjectReference", &[])
            .expect("MSBuild evaluates these documents");
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed XML parses");
        assert!(
            theirs.len() > parsed.project_references.len(),
            "MSBuild's list is not longer, so the row tests nothing: {xml}\n{theirs:?}"
        );
        assert!(
            parsed.project_references_uncertain,
            "MSBuild holds {theirs:?}, and the walk published {:?} as certain: {xml}",
            parsed.project_references
        );
    }
}

/// A reference whose spec reads a doubted name flags the list where the item
/// pass reaches it: an item read of `@(ProjectReference)` before it in its
/// group sees the list as it stood, as MSBuild's does, so a package list
/// built from that read keeps its exact value.
#[test]
fn a_doubted_reference_flags_the_list_where_it_stands() {
    let xml = format!(
        "<Project><PropertyGroup><U{UNSUPPORTED_TRUE}>u</U></PropertyGroup>\
         <ItemGroup><Id Include=\"X\" Exclude=\"@(ProjectReference)\" />\
         <PackageReference Include=\"@(Id)\" Version=\"1\" />\
         <ProjectReference Include=\"$(U).fsproj\" /></ItemGroup></Project>"
    );
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, &xml).unwrap();
    let theirs = Oracle::spawn()
        .items_meta(&xml, &proj, "PackageReference", &[])
        .expect("MSBuild evaluates this document");
    let theirs: Vec<&str> = theirs.iter().map(|(id, _)| id.as_str()).collect();
    assert_eq!(theirs, ["X"], "{xml}");
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed XML parses");
    assert!(parsed.project_references_uncertain, "{xml}");
    assert!(
        !parsed.package_references_uncertain,
        "{xml}\n{:#?}",
        parsed.package_reference_uncertainties
    );
    let ours: Vec<&str> = parsed
        .package_references
        .iter()
        .map(|p| p.id.as_str())
        .collect();
    assert_eq!(ours, ["X"], "{xml}");
}

/// The arms after a `<When>` that holds whatever the doubted names hold are
/// ones MSBuild never evaluates the gates of: deciding which arms are dead
/// probes none of their files, so the read set holds nothing MSBuild does
/// not consult.
#[test]
fn the_arms_after_a_taken_one_are_not_probed() {
    for xml in [
        format!(
            "<Project><Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>1</X></PropertyGroup></When>\
             <When Condition=\"true\"><PropertyGroup><Y>1</Y></PropertyGroup></When>\
             <When Condition=\"Exists('not-reached')\"><PropertyGroup><Z>1</Z></PropertyGroup></When>\
             </Choose></Project>"
        ),
        // A group with no reference in an arm the walk cannot decide: the
        // reference check probes none of its gates.
        format!(
            "<Project><PropertyGroup><G{UNSUPPORTED_TRUE}>false</G></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><ItemGroup Condition=\"$(G) And Exists('not-reached')\">\
             <None Include=\"n\" /></ItemGroup></When></Choose></Project>"
        ),
        // Arms that hold no reference: none of their gates is the check's
        // to probe.
        format!(
            "<Project><PropertyGroup><G>{REFUSED_BODY}</G></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><ItemGroup><None Include=\"a\" /></ItemGroup></When>\
             <When Condition=\"'$(G.Substring(0))' == 'yes' And Exists('not-reached')\">\
             <ItemGroup><None Include=\"b\" /></ItemGroup></When></Choose></Project>"
        ),
        // The same with a reference in the later arm: whether that arm is
        // dead is asked with no file system, as MSBuild may evaluate its gate
        // not at all.
        format!(
            "<Project><PropertyGroup><G>{REFUSED_BODY}</G></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><ItemGroup><None Include=\"a\" /></ItemGroup></When>\
             <When Condition=\"'$(G.Substring(0))' == 'yes' And Exists('not-reached')\">\
             <ItemGroup><ProjectReference Include=\"$(G).fsproj\" /></ItemGroup></When></Choose></Project>"
        ),
        // A nested `<Choose>` after hidden content (an import under a gate
        // the walk cannot decide), whose first `<When>` holds whatever any
        // name holds.
        format!(
            "<Project><Import Project=\"hidden.props\"{UNSUPPORTED_TRUE} />\
             <Choose><When{UNSUPPORTED_TRUE}><Choose>\
             <When Condition=\"true Or '$(Unknown)' != ''\"><PropertyGroup><Y>1</Y></PropertyGroup></When>\
             <When Condition=\"Exists('not-reached')\"><PropertyGroup><Z>1</Z></PropertyGroup></When>\
             </Choose></When></Choose></Project>"
        ),
    ] {
        not_probed(&xml);
    }
}

/// One document of [`the_arms_after_a_taken_one_are_not_probed`]: its read
/// set holds nothing of `not-reached`.
fn not_probed(xml: &str) {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, xml).unwrap();
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed XML parses");
    let read = format!("{:?}", parsed.read_set);
    assert!(!read.contains("not-reached"), "{read}");
}

/// A function that reads a name without naming it (`AreFeaturesEnabled`
/// reads `MSBuildDisableFeaturesFromVersion`), with that name set in the
/// environment of both MSBuild and the walk: a certain list is MSBuild's.
#[test]
fn an_implicit_read_leaves_no_certain_list_short() {
    let env = [(
        "MSBUILDDISABLEFEATURESFROMVERSION".to_owned(),
        "17.4".to_owned(),
    )];
    let xml = "<Project><ItemGroup>\
               <ProjectReference Include=\"$([MSBuild]::AreFeaturesEnabled('17.10')).fsproj\" />\
               <ProjectReference Include=\"A.fsproj\" /></ItemGroup></Project>";
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, xml).unwrap();
    let theirs: Vec<PathBuf> = Oracle::spawn_in_dir_with_env(&root, &env)
        .items(xml, &proj, "ProjectReference", &[])
        .expect("MSBuild evaluates this document")
        .iter()
        .map(|p| lexical(p))
        .collect();
    let mut environment = common::oracle_environment();
    environment.extend(env.iter().cloned());
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &environment,
        None,
        None,
    )
    .expect("well-formed XML parses");
    assert_eq!(theirs.len(), 2, "{theirs:?}");
    let ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| published(&item.include))
        .collect();
    if let Err(failure) =
        common::check_reference_claim(common::reference_claim(&parsed), &ours, &theirs)
    {
        panic!("{failure}\n{xml}");
    }
}

/// A reference behind a gate false whatever any name holds reads nothing
/// MSBuild uses, however doubted the names it reads: the list is never
/// uncertain for it. Where the walk also decides every gate and computes
/// every `Include` it keeps, the list is certain and MSBuild's exactly;
/// where it cannot, the list is incomplete, and every edge it holds is
/// MSBuild's. Each row pins which of the two it is, so a walk that learns to
/// decide a row moves it.
#[test]
fn a_dead_reference_reading_a_refused_name_costs_no_certainty() {
    use DeadRow::{Exact, Incomplete};
    let rows = [
        // False gates, on a reference in a group the walk cannot decide, and
        // on a group.
        (
            Exact,
            format!(
                "<ItemGroup{UNSUPPORTED_TRUE}>\
                 <ProjectReference Include=\"$(P).fsproj\" Condition=\"false\" /></ItemGroup>\
                 <ItemGroup Condition=\"false\"><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup>"
            ),
        ),
        // A gate on a name a refused write and then a clean one wrote: the
        // clean write decides it.
        (
            Exact,
            format!(
                "<PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
                 <PropertyGroup><Gate>false</Gate></PropertyGroup>\
                 <ItemGroup><ProjectReference Include=\"$(P).fsproj\" Condition=\"$(Gate)\" /></ItemGroup>"
            ),
        ),
        // A `<When>` after one the walk cannot decide, false on the state
        // before the `<Choose>`, which is the state MSBuild evaluates it in
        // (the undecided branch's write to `Off` never precedes it).
        (
            Exact,
            format!(
                "<PropertyGroup><Off>false</Off></PropertyGroup>\
                 <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><Off>true</Off></PropertyGroup></When>\
                 <When Condition=\"$(Off)\"><ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose>"
            ),
        ),
        // A `<When>` false on a name a refused write and then a clean one
        // wrote, after one the walk cannot decide. The walk does not decide
        // the arm (#1184).
        (
            Incomplete,
            format!(
                "<PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
                 <PropertyGroup><Gate>false</Gate></PropertyGroup>\
                 <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>1</X></PropertyGroup></When>\
                 <When Condition=\"$(Gate)\"><ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose>"
            ),
        ),
        // A padded bare read, which MSBuild expands to empty whatever `P`
        // holds. The walk does not model the padded spelling, so it drops
        // the `B.fsproj` MSBuild keeps (#1184).
        (
            Incomplete,
            "<ItemGroup><ProjectReference Include=\"B$( P).fsproj\" /></ItemGroup>".to_owned(),
        ),
        (
            Incomplete,
            "<ItemGroup><ProjectReference Include=\"B$(P ).fsproj\" /></ItemGroup>".to_owned(),
        ),
        // An `Exclude` reading it from an `Include` empty whatever any name
        // holds: it excludes nothing. The walk does not see that the
        // `Exclude` is idle (#1184).
        (
            Incomplete,
            "<ItemGroup><ProjectReference Include=\"$(OptionalProjects)\" Exclude=\"$(P)\" /></ItemGroup>"
                .to_owned(),
        ),
        // The same from an item list the walk knows to be empty.
        (
            Incomplete,
            "<ItemGroup><ProjectReference Include=\"@(OptionalProjects)\" Exclude=\"$(P)\" /></ItemGroup>"
                .to_owned(),
        ),
        // A name only a branch MSBuild cannot take writes, beside an
        // undecided one: its write never happens, so a read of it is exact.
        (
            Exact,
            format!(
                "<Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>1</X></PropertyGroup></When>\
                 <When Condition=\"false\"><PropertyGroup><OptionalProjects>B.fsproj</OptionalProjects></PropertyGroup></When></Choose>\
                 <ItemGroup><ProjectReference Include=\"$(OptionalProjects)\" /></ItemGroup>"
            ),
        ),
        // A gate false whatever a doubted name holds, which the walk cannot
        // evaluate on the value it holds (`É` against `é`).
        (
            Exact,
            format!(
                "<PropertyGroup><Gate{UNSUPPORTED_TRUE}>É</Gate></PropertyGroup>\
                 <ItemGroup><ProjectReference Include=\"$(Gate).fsproj\" Condition=\"'$(Gate)' == 'é' And false\" /></ItemGroup>"
            ),
        ),
        // A nested `<When>` a clean value decides false whatever a name the
        // enclosing undecided branch writes holds. The walk does not decide
        // it (#1184).
        (
            Incomplete,
            format!(
                "<PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
                 <PropertyGroup><Gate>false</Gate></PropertyGroup>\
                 <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>one</X></PropertyGroup>\
                 <Choose><When Condition=\"$(Gate) And '$(X)' == 'one'\">\
                 <ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose></When></Choose>"
            ),
        ),
        // A padded read of a name written under a gate the walk cannot
        // decide, as the padded rows above (#1184).
        (
            Incomplete,
            format!(
                "<PropertyGroup><G{UNSUPPORTED_TRUE}>x</G></PropertyGroup>\
                 <ItemGroup><ProjectReference Include=\"B$( G).fsproj\" /></ItemGroup>"
            ),
        ),
    ];
    let mut oracle = Oracle::spawn();
    for (expected, row) in rows {
        dead_reference_row(&mut oracle, expected, &row);
    }
}

/// What [`a_dead_reference_reading_a_refused_name_costs_no_certainty`] pins
/// of one row's list. Neither is uncertain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeadRow {
    /// Certain, and MSBuild's list exactly.
    Exact,
    /// Incomplete, and every edge it holds MSBuild's.
    Incomplete,
}

/// One row of [`a_dead_reference_reading_a_refused_name_costs_no_certainty`],
/// beside a refused `P` and a live reference.
fn dead_reference_row(oracle: &mut Oracle, expected: DeadRow, row: &str) {
    let xml = format!(
        "<Project><PropertyGroup><P>{REFUSED_BODY}</P></PropertyGroup>\
         <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>{row}</Project>"
    );
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, &xml).unwrap();
    let theirs: Vec<PathBuf> = oracle
        .items(&xml, &proj, "ProjectReference", &[])
        .expect("MSBuild evaluates this document")
        .iter()
        .map(|p| lexical(p))
        .collect();
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed XML parses");
    let ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| published(&item.include))
        .collect();
    assert!(!parsed.project_references_uncertain, "{xml}");
    let got = if parsed.project_references_incomplete {
        DeadRow::Incomplete
    } else {
        DeadRow::Exact
    };
    assert_eq!(got, expected, "{xml}\nours: {ours:?}\ntheirs: {theirs:?}");
    assert!(!ours.is_empty(), "the live reference is held: {xml}");
    if let Err(failure) =
        common::check_reference_claim(common::reference_claim(&parsed), &ours, &theirs)
    {
        panic!("{failure}\n{xml}");
    }
}

/// A reference the walk captured, whose only doubt is in a metadatum it
/// resolves (a refused write, as an attribute or a child element), is in the
/// list: the list is certain and MSBuild's. What the metadatum does to the
/// edge is the metadatum's own verdict (`ItemMetadataValue::Unknown`), not a
/// missing reference.
#[test]
fn a_doubted_metadatum_leaves_the_list_certain() {
    let mut oracle = Oracle::spawn();
    for name in [
        "PrivateAssets",
        "ReferenceOutputAssembly",
        "ExcludeAssets",
        "IncludeAssets",
    ] {
        for element in [false, true] {
            let reference = if element {
                format!(
                    "<ProjectReference Include=\"B.fsproj\"><{name}>{REFUSED_BODY}</{name}></ProjectReference>"
                )
            } else {
                format!("<ProjectReference Include=\"B.fsproj\" {name}=\"{REFUSED_BODY}\" />")
            };
            let xml = format!(
                "<Project><ItemGroup><ProjectReference Include=\"A.fsproj\" />{reference}</ItemGroup></Project>"
            );
            let dir = tempfile::TempDir::new().expect("tempdir");
            let root =
                borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
            let proj = layout(&root);
            std::fs::write(&proj, &xml).unwrap();
            let theirs: Vec<PathBuf> = oracle
                .items(&xml, &proj, "ProjectReference", &[])
                .expect("MSBuild evaluates this document")
                .iter()
                .map(|p| lexical(p))
                .collect();
            assert_eq!(theirs.len(), 2, "{theirs:?}");
            let parsed = parse_fsproj_with_imports(
                &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
                    .expect("a project path spelt as its full path"),
                &HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed XML parses");
            let ours: Vec<PathBuf> = parsed
                .project_references
                .iter()
                .map(|item| published(&item.include))
                .collect();
            assert_eq!(
                common::reference_claim(&parsed),
                common::ReferenceClaim::Exact,
                "{xml}"
            );
            if let Err(failure) =
                common::check_reference_claim(common::ReferenceClaim::Exact, &ours, &theirs)
            {
                panic!("{failure}\n{xml}");
            }
        }
    }
}

/// #1181: a live reference beside the dead one, in a group the walk cannot
/// decide, is one MSBuild keeps and the walk drops: the list is incomplete,
/// not certain, while every edge it holds is MSBuild's.
#[test]
fn a_live_reference_in_an_undecided_group_leaves_the_list_incomplete() {
    let xml = format!(
        "<Project><PropertyGroup><P>{REFUSED_BODY}</P></PropertyGroup>\
         <ItemGroup><ProjectReference Include=\"A.fsproj\" /></ItemGroup>\
         <ItemGroup{UNSUPPORTED_TRUE}><ProjectReference Include=\"B.fsproj\" />\
         <ProjectReference Include=\"$(P).fsproj\" Condition=\"false\" /></ItemGroup></Project>"
    );
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, &xml).unwrap();
    let theirs: Vec<PathBuf> = Oracle::spawn()
        .items(&xml, &proj, "ProjectReference", &[])
        .expect("MSBuild evaluates this document")
        .iter()
        .map(|p| lexical(p))
        .collect();
    assert_eq!(theirs.len(), 2, "MSBuild keeps B: {theirs:?}");
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed XML parses");
    assert!(
        parsed.project_references_incomplete && !parsed.project_references_uncertain,
        "{xml}"
    );
    let ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| published(&item.include))
        .collect();
    assert!(!ours.is_empty(), "A is held: {xml}");
    if let Err(failure) =
        common::check_reference_claim(common::reference_claim(&parsed), &ours, &theirs)
    {
        panic!("{failure}\n{xml}");
    }
}

/// A gate an `Exists` probe decides whatever a refused name beside it holds
/// is decided (#1181), so the references under it are kept; an item
/// expression whose separator argument holds a `;` among them makes no edge
/// MSBuild lacks (#1204), on either glob seam.
#[test]
fn a_gate_decided_by_exists_keeps_no_fabricated_edge() {
    let xml = format!(
        "<Project><PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
         <ItemGroup><Helper Include=\"A.fsproj\" /></ItemGroup>\
         <ItemGroup Condition=\"Exists('Demo.fsproj') Or '$(Gate)' == 'x'\">\
         <ProjectReference Include=\"@(Helper, ';Wrong.fsproj;')\" />\
         <ProjectReference Include=\"A.fsproj\" /></ItemGroup></Project>"
    );
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    std::fs::write(&proj, &xml).unwrap();
    let theirs: Vec<PathBuf> = Oracle::spawn()
        .items(&xml, &proj, "ProjectReference", &[])
        .expect("MSBuild evaluates this document")
        .iter()
        .map(|p| lexical(p))
        .collect();
    let resolver: &borzoi_msbuild::GlobResolver<'_> = &borzoi_msbuild::glob_resolver::resolve;
    for with_resolver in [false, true] {
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            with_resolver.then_some(resolver),
        )
        .expect("well-formed XML parses");
        let ours: Vec<PathBuf> = parsed
            .project_references
            .iter()
            .map(|item| published(&item.include))
            .collect();
        assert!(
            ours.contains(&root.join("proj/A.fsproj")),
            "the gate is decided, so its literal reference is kept: {ours:?}"
        );
        if let Err(failure) =
            common::check_reference_claim(common::reference_claim(&parsed), &ours, &theirs)
        {
            panic!("resolver: {with_resolver}: {failure}\n{xml}");
        }
    }
}
