//! Generative differential: `<ProjectReference>`s whose `Include` reads a
//! name the walk doubts, against the real MSBuild evaluator (the oracle's
//! `itemsMeta` op).
//!
//! The reference list's contract (`ParsedProject::project_references_uncertain`)
//! tolerates a missing edge where the walk cannot say MSBuild has one: an
//! `Include` behind a gate it could not decide, or one whose value it cannot
//! compute from names it holds exactly. An `Include` that reads a name the
//! walk doubts (a write it refused to compute, one under a gate it could not
//! decide, a copy of either) is an edge MSBuild has at a path the walk does
//! not know, so a list missing it is no certain list (#1098).
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
            .map(|item| lexical(&item.include.to_string_lossy()))
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
    if parsed.project_references_uncertain {
        return (ReadOutcome::Declined { owed }, evaluated);
    }
    // A reference MSBuild made reading a name the walk doubts may hold
    // another path in another world, even where this one's agrees.
    assert!(
        !owed,
        "#1098: the list is certain, and a reference MSBuild made reads a name the walk \
         doubts:\n{xml}\nours: {:#?}",
        parsed.project_references
    );
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
        assert!(
            unmatched.is_empty() || !reads.iter().any(|name| doubted(name)),
            "#1098: the list is certain without {unmatched:?} of reference E{i}, whose `Include` \
             reads a name the walk doubts ({reads:?}):\n{xml}\nours: {ours:#?}"
        );
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
    let mut theirs: Vec<PathBuf> = Oracle::spawn_in_dir_with_env(&root, &env)
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
    if !parsed.project_references_uncertain {
        let mut ours: Vec<PathBuf> = parsed
            .project_references
            .iter()
            .map(|item| lexical(&item.include.to_string_lossy()))
            .collect();
        ours.sort();
        theirs.sort();
        assert_eq!(ours, theirs, "a certain list is MSBuild's: {xml}");
    }
}

/// A reference behind a gate false whatever any name holds reads nothing
/// MSBuild uses, however doubted the names it reads, beside a live sibling
/// in a group the walk cannot decide: the list keeps every edge it knows,
/// certain, and MSBuild agrees with each.
#[test]
fn a_dead_reference_reading_a_refused_name_costs_no_certainty() {
    let rows = [
        // False gates, on a reference beside a live sibling in a group the
        // walk cannot decide, and on a group.
        format!(
            "<ItemGroup{UNSUPPORTED_TRUE}><ProjectReference Include=\"B.fsproj\" />\
             <ProjectReference Include=\"$(P).fsproj\" Condition=\"false\" /></ItemGroup>\
             <ItemGroup Condition=\"false\"><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup>"
        ),
        // A gate on a name a refused write and then a clean one wrote: the
        // clean write decides it.
        format!(
            "<PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
             <PropertyGroup><Gate>false</Gate></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"$(P).fsproj\" Condition=\"$(Gate)\" /></ItemGroup>"
        ),
        // A `<When>` after one the walk cannot decide, false on the state
        // before the `<Choose>`, which is the state MSBuild evaluates it in
        // (the undecided branch's write to `Off` never precedes it).
        format!(
            "<PropertyGroup><Off>false</Off></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><Off>true</Off></PropertyGroup></When>\
             <When Condition=\"$(Off)\"><ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose>"
        ),
        // A `<When>` false on a name a refused write and then a clean one
        // wrote, after one the walk cannot decide.
        format!(
            "<PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
             <PropertyGroup><Gate>false</Gate></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>1</X></PropertyGroup></When>\
             <When Condition=\"$(Gate)\"><ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose>"
        ),
        // A padded bare read, which MSBuild expands to empty whatever `P`
        // holds.
        "<ItemGroup><ProjectReference Include=\"B$( P).fsproj\" /></ItemGroup>".to_owned(),
        "<ItemGroup><ProjectReference Include=\"B$(P ).fsproj\" /></ItemGroup>".to_owned(),
        // An `Exclude` reading it from an `Include` empty whatever any name
        // holds: it excludes nothing.
        "<ItemGroup><ProjectReference Include=\"$(OptionalProjects)\" Exclude=\"$(P)\" /></ItemGroup>"
            .to_owned(),
        // The same from an item list the walk knows to be empty.
        "<ItemGroup><ProjectReference Include=\"@(OptionalProjects)\" Exclude=\"$(P)\" /></ItemGroup>"
            .to_owned(),
        // A name only a branch MSBuild cannot take writes, beside an
        // undecided one: its write never happens, so a read of it is exact.
        format!(
            "<Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>1</X></PropertyGroup></When>\
             <When Condition=\"false\"><PropertyGroup><OptionalProjects>B.fsproj</OptionalProjects></PropertyGroup></When></Choose>\
             <ItemGroup><ProjectReference Include=\"$(OptionalProjects)\" /></ItemGroup>"
        ),
        // A gate false whatever a doubted name holds, which the walk cannot
        // evaluate on the value it holds (`É` against `é`).
        format!(
            "<PropertyGroup><Gate{UNSUPPORTED_TRUE}>É</Gate></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"$(Gate).fsproj\" Condition=\"'$(Gate)' == 'é' And false\" /></ItemGroup>"
        ),
        // A nested `<When>` a clean value decides false whatever a name the
        // enclosing undecided branch writes holds.
        format!(
            "<PropertyGroup><Gate>{REFUSED_BODY}</Gate></PropertyGroup>\
             <PropertyGroup><Gate>false</Gate></PropertyGroup>\
             <Choose><When{UNSUPPORTED_TRUE}><PropertyGroup><X>one</X></PropertyGroup>\
             <Choose><When Condition=\"$(Gate) And '$(X)' == 'one'\">\
             <ItemGroup><ProjectReference Include=\"$(P).fsproj\" /></ItemGroup></When></Choose></When></Choose>"
        ),
        // The same of a name written under a gate the walk cannot decide.
        format!(
            "<PropertyGroup><G{UNSUPPORTED_TRUE}>x</G></PropertyGroup>\
             <ItemGroup><ProjectReference Include=\"B$( G).fsproj\" /></ItemGroup>"
        ),
    ];
    let mut oracle = Oracle::spawn();
    for row in rows {
        dead_reference_row(&mut oracle, &row);
    }
}

/// One row of [`a_dead_reference_reading_a_refused_name_costs_no_certainty`],
/// beside a refused `P` and a live reference.
fn dead_reference_row(oracle: &mut Oracle, row: &str) {
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
    assert!(!parsed.project_references_uncertain, "{xml}");
    let ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| lexical(&item.include.to_string_lossy()))
        .collect();
    assert!(
        !ours.is_empty() && ours.iter().all(|p| theirs.contains(p)),
        "{ours:?} {theirs:?}"
    );
}

/// A `<ProjectReference>` metadatum's own gate on a name the walk holds no
/// exact value of (a toolset name such as `MSBuildStartupDirectory`) is a gate
/// it cannot decide: MSBuild may take it either way. So the metadatum it
/// guards resolves `Unknown` where it is read by value, and counts as possibly
/// present where it is read by its presence (the significant P2P names), in
/// both polarities. The same child under a literal gate resolves as written,
/// the control.
#[test]
fn a_metadatum_gate_the_walk_cannot_decide_leaves_the_metadatum_unknown() {
    const BY_VALUE: [&str; 4] = [
        "ReferenceOutputAssembly",
        "IncludeAssets",
        "ExcludeAssets",
        "PrivateAssets",
    ];
    const BY_PRESENCE: [&str; 9] = [
        "BuildReference",
        "Targets",
        "SetConfiguration",
        "SetPlatform",
        "SetTargetFramework",
        "AdditionalProperties",
        "UndefineProperties",
        "GlobalPropertiesToRemove",
        "SkipGetTargetFrameworkProperties",
    ];
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    let item = |condition: &str, name: &str| {
        let xml = format!(
            "<Project><ItemGroup><ProjectReference Include=\"A.fsproj\">\
             <{name} Condition=\"{condition}\">false</{name}>\
             </ProjectReference></ItemGroup></Project>"
        );
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed XML parses");
        parsed
            .project_references
            .into_iter()
            .next()
            .unwrap_or_else(|| panic!("the reference is captured: {xml}"))
    };
    let value_of = |item: &borzoi_msbuild::ResolvedItem, name: &str| match name {
        "ReferenceOutputAssembly" => item.reference_output_assembly.clone(),
        "IncludeAssets" => item.include_assets.clone(),
        "ExcludeAssets" => item.exclude_assets.clone(),
        "PrivateAssets" => item.private_assets.clone(),
        other => unreachable!("{other}"),
    };
    let undecided = [
        "'$(MSBuildStartupDirectory)' != ''",
        "'$(MSBuildStartupDirectory)' == ''",
    ];
    for name in BY_VALUE {
        for gate in undecided {
            assert_eq!(
                value_of(&item(gate, name), name),
                borzoi_msbuild::ItemMetadataValue::Unknown,
                "{name} under `{gate}`"
            );
        }
        assert_eq!(
            value_of(&item("true", name), name),
            borzoi_msbuild::ItemMetadataValue::known("false"),
            "{name} under a literal true gate"
        );
        assert_eq!(
            value_of(&item("false", name), name),
            borzoi_msbuild::ItemMetadataValue::ABSENT,
            "{name} under a literal false gate"
        );
    }
    for name in BY_PRESENCE {
        for gate in undecided {
            assert!(
                item(gate, name).unmodelled_reference_metadata,
                "{name} under `{gate}`"
            );
        }
        assert!(item("true", name).unmodelled_reference_metadata, "{name}");
        assert!(!item("false", name).unmodelled_reference_metadata, "{name}");
    }
}
