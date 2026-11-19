//! The candidate channel held to MSBuild (#1009): the value a property ends
//! with in the real build is always among the walk's candidates for it, or the
//! walk says it may hold anything.
//!
//! Generated projects write a few properties from literals and from each
//! other, under gates the walk decides, gates it cannot decide, and `<Choose>`
//! branches of either kind, and import sibling files that write them too. The
//! gates the walk cannot decide read a global, `G`, through a property function
//! it does not model, and MSBuild decides them on `G`; each project is
//! evaluated under several values of `G`, so that across the runs MSBuild
//! takes both arms of every such gate. An import under such a gate is content
//! the walk cannot see, after which the values it holds are stale, and a later
//! gate that reads one is decided on a value the real build may have
//! rewritten. Under each value of `G`, the walk (handed the same globals) must
//! name MSBuild's final value of every property among its candidates.
//!
//! The channel shares one assumption with the walk's certain values: that a
//! relative path the Unix path adjustment probes names nothing in MSBuild's
//! working directory (`properties::Relative::MissForProjectText`). The
//! oracle's working directory holds none of the generated segments.

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::path::Path;

use borzoi_msbuild::test_support::{EvaluationReads, PropertyRead, ReadProbe, parse_fsproj_reads};
use common::{Oracle, SplitMix64, soak_parameters};
use tempfile::TempDir;

/// The names written and read back. `G` is the global: MSBuild ignores a
/// project's writes to it, unless a document opts it out.
const NAMES: &[&str] = &["Alpha", "Beta", "Gamma", "G"];
/// Names read back that the steps never write: `R`, which the project's
/// prelude may bind through a write the walk refuses and then overwrite
/// cleanly (a value the walk knows, which a gate's certain-inputs test still
/// counts as unknown), and the copies of `Alpha` and `G` made at the end.
const DERIVED: &[&str] = &["R", "CopyAlpha", "CopyG"];
/// The longest candidate the channel keeps, in bytes (`MAX_CANDIDATE_BYTES`).
const MAX_CANDIDATE_BYTES: usize = 4096;
/// A value past it.
const LONG: &str = "LONG";
/// The file that opts `G` out of global protection. MSBuild keeps the opt-out
/// past the import; the walk does not (#1041), so after this import the walk
/// may commit a wrong value of `G`, and the channel must not name one.
const OPT_OUT: &str = "optout.props";
/// Names read back but never written: the current file's, whose value is the
/// file's while the evaluation expands it, and none once it has finished.
const READ_ONLY: &[&str] = &[
    "MSBuildThisFile",
    "MSBuildThisFileDirectory",
    "MSBuildThisFileFullPath",
];
const GLOBALS: &[&str] = &["x", "y", "z"];
/// The sibling files a project may import.
const SIDES: &[&str] = &["side0.props", "side1.props"];

fn value(rng: &mut SplitMix64) -> String {
    rng.pick(&[
        "",
        "a",
        "b",
        "$(Alpha)",
        "$(Beta)",
        "$(Alpha)$(Beta)",
        "x$(Gamma)",
        "$(Alpha)y",
        "a;b",
        "%61%3B",
        "a\\b",
        "$(Alpha)\\c",
        "$(G)",
        "$(Alpha.Trim())",
        "$([MSBuild]::ValueOrDefault('$(Beta)', 'd'))",
        "$(Gamma.ToUpperInvariant())",
        LONG,
        "$(Alpha)$(Alpha)",
    ])
    .replace(LONG, &"x".repeat(MAX_CANDIDATE_BYTES + 1))
}

/// A gate: none, decided either way, decided by MSBuild on `G` through a
/// function the walk does not model, or reading a generated name, which the
/// walk decides on the value it holds, certain of it or not.
fn gate(rng: &mut SplitMix64) -> String {
    rng.pick(&[
        "",
        " Condition=\"'$(Alpha)' == 'a'\"",
        " Condition=\"'$(Beta)' != ''\"",
        " Condition=\"'$(Gamma)' == ''\"",
        " Condition=\"'$(Alpha)$(Beta)' == 'ab'\"",
        " Condition=\"'k' == 'k'\"",
        " Condition=\"'k' == 'j'\"",
        " Condition=\"'$(G.ToUpperInvariant())' == 'X'\"",
        " Condition=\"'$(G.ToUpperInvariant())' != 'X'\"",
        " Condition=\"'$(G.ToUpperInvariant())' == 'Y'\"",
        " Condition=\"'$(R)' == 'w'\"",
        " Condition=\"'$(R)' != 'w'\"",
        // An `Exists` the walk's own evaluation short-circuits past.
        " Condition=\"'$(R)' == 'w' And Exists('marker')\"",
        " Condition=\"'$(Alpha)' == 'zz' And Exists('marker')\"",
    ])
    .to_string()
}

fn writes(rng: &mut SplitMix64, out: &mut String) {
    for _ in 0..1 + rng.below(2) {
        let name = rng.pick(NAMES);
        let own = if rng.below(3) == 0 {
            gate(rng)
        } else {
            String::new()
        };
        let _ = write!(out, "<{name}{own}>{}</{name}>", value(rng));
    }
}

/// A property group, a `<Choose>`, or (where `imports`) an import of a
/// sibling file or of [`OPT_OUT`].
fn step(rng: &mut SplitMix64, imports: bool, out: &mut String) {
    // Rarely: past it the channel names nothing, so the case grades little
    // else.
    if imports && rng.below(40) == 0 {
        let _ = write!(out, "<Import Project=\"{OPT_OUT}\" />");
        return;
    }
    match rng.below(if imports { 5 } else { 4 }) {
        0 => {
            out.push_str("<Choose>");
            for _ in 0..1 + rng.below(2) {
                let mut when = gate(rng);
                if when.is_empty() {
                    when = " Condition=\"'k' == 'k'\"".to_owned();
                }
                let _ = write!(out, "<When{when}><PropertyGroup>");
                writes(rng, out);
                out.push_str("</PropertyGroup></When>");
            }
            if rng.below(2) == 0 {
                out.push_str("<Otherwise><PropertyGroup>");
                writes(rng, out);
                out.push_str("</PropertyGroup></Otherwise>");
            }
            out.push_str("</Choose>");
        }
        4 => {
            let _ = write!(
                out,
                "<Import Project=\"{}\"{} />",
                rng.pick(SIDES),
                gate(rng)
            );
        }
        _ => {
            let _ = write!(out, "<PropertyGroup{}>", gate(rng));
            writes(rng, out);
            out.push_str("</PropertyGroup>");
        }
    }
}

/// A project and its sibling files.
fn project(rng: &mut SplitMix64) -> (String, Vec<String>) {
    let sides = SIDES
        .iter()
        .map(|_| {
            let mut body = String::new();
            if rng.below(2) == 0 {
                step(rng, false, &mut body);
            } else {
                // Plain literals, which flip the gates that read the names.
                body.push_str("<PropertyGroup>");
                for _ in 0..1 + rng.below(2) {
                    let name = rng.pick(NAMES);
                    let _ = write!(body, "<{name}>{}</{name}>", rng.pick(&["", "a", "b"]));
                }
                body.push_str("</PropertyGroup>");
            }
            format!("<Project>{body}</Project>")
        })
        .collect();
    let mut body = String::new();
    if rng.below(2) == 0 {
        body.push_str("<PropertyGroup><R>$(G.ToUpperInvariant())</R><R>v</R></PropertyGroup>");
    }
    for _ in 0..3 + rng.below(5) {
        step(rng, true, &mut body);
    }
    body.push_str(
        "<PropertyGroup><CopyAlpha>$(Alpha)</CopyAlpha><CopyG>$(G)</CopyG></PropertyGroup>",
    );
    (format!("<Project>{body}</Project>"), sides)
}

#[derive(Debug, Default)]
struct Census {
    cases: usize,
    /// Reads where the walk named more than one candidate.
    several: usize,
    /// `(case, name, candidates)` triples under which MSBuild ended with two
    /// or more of the candidates across the runs: a gate the walk could not
    /// decide went both ways.
    both_arms: usize,
    /// Reads where the walk said a name may hold anything.
    anything: usize,
    /// Evaluations past an imported opt-out of `G`, where the channel names
    /// nothing (#1041).
    withdrawn: usize,
}

/// MSBuild's table, and the walk's reads.
type Evaluated = (HashMap<String, String>, EvaluationReads);

fn evaluate(
    oracle: &mut Oracle,
    xml: &str,
    path: &Path,
    probe: &ReadProbe,
    g: &str,
) -> Option<Evaluated> {
    let globals = vec![("G".to_owned(), g.to_owned())];
    let theirs = oracle.project(xml, &probe.properties, Some(path), &globals)?;
    let extra: HashMap<String, String> = globals.into_iter().collect();
    let parse = |probe: &ReadProbe| {
        parse_fsproj_reads(
            xml,
            path,
            &extra,
            &common::oracle_environment(),
            None,
            None,
            None,
            probe,
        )
        .expect("well-formed")
    };
    let (probed, reads) = parse(probe);
    // The probe changes nothing about the walk: tracking candidates leaves
    // what it publishes, its read set included, as it is without them.
    let (unprobed, _) = parse(&ReadProbe::default());
    assert_eq!(
        probed, unprobed,
        "the walk publishes something else when the probe reads candidates\n{xml}"
    );
    Some((theirs, reads))
}

/// The properties the channel holds whatever MSBuild does: a value the walk
/// commits is its only candidate (an unset one, the empty string), and no
/// candidate is past the byte budget. `skip` names reads exempt from the first.
fn assert_channel_consistent(
    name: &str,
    read: &PropertyRead,
    candidates: Option<&BTreeSet<String>>,
    skip: bool,
    context: &dyn Fn() -> String,
) {
    if let Some(candidates) = candidates {
        for candidate in candidates {
            assert!(
                candidate.len() <= MAX_CANDIDATE_BYTES,
                "a candidate of {name} is {} bytes, past the budget\n{}",
                candidate.len(),
                context()
            );
        }
    }
    if skip {
        return;
    }
    let committed = match read {
        PropertyRead::Value(value) => Some(value.as_str()),
        PropertyRead::Unset => Some(""),
        PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
    };
    // One past the budget is one the channel keeps none of. The budget counts
    // escaped bytes, which number at least the decoded value's and at most
    // three times them (`%XX`), so between those the channel may keep either.
    if let Some(committed) = committed {
        let singleton = BTreeSet::from([committed.to_owned()]);
        let ok = match candidates {
            Some(candidates) => *candidates == singleton && committed.len() <= MAX_CANDIDATE_BYTES,
            None => committed.len() * 3 > MAX_CANDIDATE_BYTES,
        };
        assert!(
            ok,
            "the walk commits {name} = {committed:?}, so that is its only candidate, not \
             {candidates:?}\n{}",
            context()
        );
    }
}

fn sweep(oracle: &mut Oracle, rng: &mut SplitMix64, cases: usize) -> Census {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let probe = ReadProbe {
        properties: NAMES
            .iter()
            .chain(DERIVED)
            .chain(READ_ONLY)
            .map(|n| (*n).to_owned())
            .collect(),
        ..ReadProbe::default()
    };
    let mut census = Census::default();
    for _ in 0..cases {
        let (xml, sides) = project(rng);
        std::fs::write(&path, &xml).unwrap();
        for (name, side) in SIDES.iter().zip(&sides) {
            std::fs::write(dir.join(name), side).unwrap();
        }
        std::fs::write(
            dir.join(OPT_OUT),
            "<Project TreatAsLocalProperty=\"G\"><PropertyGroup><G>fresh</G></PropertyGroup></Project>",
        )
        .unwrap();
        let context = || format!("{xml}\n{}", sides.join("\n"));
        census.cases += 1;
        let mut taken: BTreeMap<(&str, Vec<String>), BTreeSet<String>> = BTreeMap::new();
        for g in GLOBALS {
            let Some((theirs, reads)) = evaluate(oracle, &xml, &path, &probe, g) else {
                continue;
            };
            let candidates = &reads.candidates;
            census.withdrawn += usize::from(reads.candidates_withdrawn);
            for name in &probe.properties {
                let real = theirs.get(name).cloned().unwrap_or_default();
                // The current file's names read at the end of the walk are a
                // probe-boundary question of their own (#1043). After an
                // imported opt-out of `G` the walk may commit a wrong value of
                // it and of what reads it (#1041), and the channel names none.
                let skip = READ_ONLY.contains(&name.as_str()) || reads.candidates_withdrawn;
                assert_channel_consistent(
                    name,
                    &reads.properties[name],
                    candidates[name].as_ref(),
                    skip,
                    &context,
                );
                match &candidates[name] {
                    None => census.anything += 1,
                    Some(candidates) => {
                        assert!(
                            candidates.contains(&real),
                            "MSBuild ends with {name} = {real:?} under G={g}, which is not \
                             among the walk's candidates {candidates:?}\n{}",
                            context()
                        );
                        if candidates.len() > 1 {
                            census.several += 1;
                            taken
                                .entry((name, candidates.iter().cloned().collect()))
                                .or_default()
                                .insert(real);
                        }
                    }
                }
            }
        }
        census.both_arms += taken.values().filter(|values| values.len() > 1).count();
    }
    census
}

/// [`sweep`] at a fixed seed.
#[test]
fn candidates_contain_what_msbuild_ends_with() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x0c4a_d1da_7e55);
    let census = sweep(&mut oracle, &mut rng, 300);
    eprintln!("candidates: {census:?}");
    // Anti-vacuity: the channel names several candidates, and MSBuild takes
    // more than one of the same set across the runs.
    assert!(census.several >= 100, "{census:?}");
    assert!(census.both_arms >= 30, "{census:?}");
    assert!(census.withdrawn >= 10, "{census:?}");
}

/// Fresh-seed twin of [`candidates_contain_what_msbuild_ends_with`].
#[test]
#[ignore = "fresh-seed soak; run it when touching the candidate channel"]
fn candidates_soak() {
    let (seed, cases) = soak_parameters("candidates", 3_000);
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let census = sweep(&mut oracle, &mut rng, cases);
    eprintln!("candidates soak: {census:?}");
}

/// A value that doubles itself on every write keeps two candidates, one of
/// which doubles too. The channel gives up on it once it outgrows its byte
/// budget rather than carry it: the walk's own value stays short.
#[test]
fn a_candidate_that_doubles_gives_up_rather_than_grow() {
    let mut xml = String::from(
        "<Project><PropertyGroup>\
         <Alpha Condition=\"'$(G.ToUpperInvariant())' == 'X'\">ab</Alpha>",
    );
    for _ in 0..24 {
        xml.push_str("<Alpha>$(Alpha)$(Alpha)</Alpha>");
    }
    xml.push_str("</PropertyGroup></Project>");
    let tmp = TempDir::new().unwrap();
    let path = tmp.path().join("Demo.fsproj");
    std::fs::write(&path, &xml).unwrap();
    let probe = ReadProbe {
        properties: vec!["Alpha".to_owned()],
        ..ReadProbe::default()
    };
    let (_, reads) = parse_fsproj_reads(
        &xml,
        &path,
        &HashMap::from([("G".to_owned(), "y".to_owned())]),
        &common::oracle_environment(),
        None,
        None,
        None,
        &probe,
    )
    .expect("well-formed");
    assert_eq!(reads.candidates["Alpha"], None);
}

/// A gate decided on a value bound before content the walk could not see
/// (here, an import under a gate it cannot decide) may have been decided on a
/// value that content rewrote: the write it skips may run, whether the gate is
/// the write's own (`A`), its group's (`B`), or a `<Choose>` branch's, before
/// no gate the walk could not decide at all (`C`) or before one (`D`).
/// The candidates of `name` in `xml`, evaluated without MSBuild.
fn candidates_alone(xml: &str, name: &str) -> Option<BTreeSet<String>> {
    let tmp = TempDir::new().unwrap();
    let path = tmp.path().join("Demo.fsproj");
    std::fs::write(&path, xml).unwrap();
    let probe = ReadProbe {
        properties: vec![name.to_owned()],
        ..ReadProbe::default()
    };
    let (_, reads) = parse_fsproj_reads(
        xml,
        &path,
        &HashMap::from([("G".to_owned(), "y".to_owned())]),
        &common::oracle_environment(),
        None,
        None,
        None,
        &probe,
    )
    .expect("well-formed");
    reads.candidates[name].clone()
}

/// A first write that may not run, appending to its own name: the name the
/// walk knows is undefined reads as the empty string in either case.
#[test]
fn an_optional_first_append_names_both_values() {
    let xml = "<Project><PropertyGroup>\
               <A Condition=\"'$(G.ToUpperInvariant())' == 'X'\">$(A)suffix</A>\
               </PropertyGroup></Project>";
    assert_eq!(
        candidates_alone(xml, "A"),
        Some(BTreeSet::from(["".to_owned(), "suffix".to_owned()]))
    );
}

/// An imported document that opts the caller's global `G` out of protection
/// leaves the walk holding values of `G`, and of what reads it, that MSBuild
/// need not (#1041): the channel names no value of any name past it.
#[test]
fn an_imported_opt_out_of_a_global_withdraws_the_channel() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let xml = format!(
        "<Project><PropertyGroup><Alpha>a</Alpha></PropertyGroup>\
         <Import Project=\"{OPT_OUT}\" />\
         <PropertyGroup><G>other</G><CopyG>$(G)</CopyG><Beta>b</Beta></PropertyGroup></Project>"
    );
    std::fs::write(&path, &xml).unwrap();
    std::fs::write(
        dir.join(OPT_OUT),
        "<Project TreatAsLocalProperty=\"G\"><PropertyGroup><G>fresh</G></PropertyGroup></Project>",
    )
    .unwrap();
    let probe = ReadProbe {
        properties: ["G", "CopyG", "Alpha", "Beta"].map(str::to_owned).to_vec(),
        ..ReadProbe::default()
    };
    let mut oracle = Oracle::spawn();
    let (theirs, reads) =
        evaluate(&mut oracle, &xml, &path, &probe, "x").expect("MSBuild evaluates it");
    assert!(reads.candidates_withdrawn);
    let candidates = reads.candidates;
    assert_eq!(
        theirs.get("CopyG").map(String::as_str),
        Some("other"),
        "MSBuild applies the entry project's write past the opted-out import"
    );
    for name in &probe.properties {
        assert_eq!(candidates[name], None, "{name}");
    }
}

/// An imported document whose `TreatAsLocalProperty` names the global `G`
/// through a property withdraws the channel too: MSBuild expands the list.
#[test]
fn a_computed_opt_out_of_a_global_withdraws_the_channel() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let xml = "<Project><PropertyGroup><L>G</L></PropertyGroup>\
               <Import Project=\"computed.props\" />\
               <PropertyGroup><CopyG>$(G)</CopyG></PropertyGroup></Project>";
    std::fs::write(&path, xml).unwrap();
    std::fs::write(
        dir.join("computed.props"),
        "<Project TreatAsLocalProperty=\"$(L)\"><PropertyGroup><G>override</G></PropertyGroup></Project>",
    )
    .unwrap();
    let probe = ReadProbe {
        properties: ["G", "CopyG"].map(str::to_owned).to_vec(),
        ..ReadProbe::default()
    };
    let mut oracle = Oracle::spawn();
    let (theirs, reads) =
        evaluate(&mut oracle, xml, &path, &probe, "x").expect("MSBuild evaluates it");
    assert_eq!(
        theirs.get("G").map(String::as_str),
        Some("override"),
        "MSBuild expands the opt-out and applies the import's write"
    );
    assert!(reads.candidates_withdrawn);
    for name in &probe.properties {
        assert_eq!(reads.candidates[name], None, "{name}");
    }
}

/// A group skipped on a gate that reads a name the walk unpinned widens what
/// it writes once: an optional append to `x` names `x` and `xy`.
#[test]
fn a_skipped_group_widens_once() {
    let xml = "<Project><PropertyGroup><A>x</A>\
               <P Condition=\"'$(G.ToUpperInvariant())' == 'X'\">p</P></PropertyGroup>\
               <PropertyGroup Condition=\"'$(P)' == 'q'\"><A>$(A)y</A></PropertyGroup></Project>";
    assert_eq!(
        candidates_alone(xml, "A"),
        Some(BTreeSet::from(["x".to_owned(), "xy".to_owned()]))
    );
}

/// `MSBuildAllProjects` holds, once the evaluation has finished, what MSBuild
/// adds to it then: the walk's value at its end is no claim about it.
#[test]
fn the_final_msbuild_all_projects_is_no_claim() {
    let xml = "<Project><PropertyGroup><MSBuildAllProjects>abc</MSBuildAllProjects>\
               </PropertyGroup></Project>";
    assert_eq!(candidates_alone(xml, "MSBuildAllProjects"), None);
}

/// A copy of a value as long as the budget allows keeps its candidates: the
/// bound counts the bytes outside the references, not their spelling.
#[test]
fn a_copy_at_the_budget_keeps_its_candidates() {
    let long = "x".repeat(MAX_CANDIDATE_BYTES);
    let xml = format!(
        "<Project><PropertyGroup>\
         <A Condition=\"'$(G.ToUpperInvariant())' == 'X'\">{long}</A><B>$(A)</B>\
         </PropertyGroup></Project>"
    );
    assert_eq!(
        candidates_alone(&xml, "B"),
        Some(BTreeSet::from([String::new(), long]))
    );
}

/// A value expanded only to name candidates asks the file system nothing: the
/// evaluation's read set, which decides when it is stale, holds no path a
/// skipped write's Unix path adjustment would probe.
#[test]
fn a_speculative_expansion_probes_nothing() {
    let tmp = TempDir::new().unwrap();
    let path = tmp.path().join("Demo.fsproj");
    let xml = "<Project><PropertyGroup>\
               <P Condition=\"'$(G.ToUpperInvariant())' == 'X'\">/probe-only-path\\foo</P>\
               </PropertyGroup></Project>";
    std::fs::write(&path, xml).unwrap();
    let (parsed, _) = parse_fsproj_reads(
        xml,
        &path,
        &HashMap::from([("G".to_owned(), "y".to_owned())]),
        &common::oracle_environment(),
        None,
        None,
        None,
        &ReadProbe::default(),
    )
    .expect("well-formed");
    let reads = format!("{:?}", parsed.read_set);
    assert!(!reads.contains("probe-only-path"), "{reads}");
}

/// [`a_speculative_expansion_probes_nothing`] with the channel tracking:
/// the walk that reads `P`'s candidates publishes what the unprobed one does.
#[test]
fn a_tracked_speculative_expansion_probes_nothing() {
    let tmp = TempDir::new().unwrap();
    let path = tmp.path().join("Demo.fsproj");
    let xml = "<Project><PropertyGroup><R>$(G.ToUpperInvariant())</R><R>v</R>\
               <P Condition=\"'$(G.ToUpperInvariant())' == 'X'\">/probe-only-path\\foo</P>\
               </PropertyGroup><PropertyGroup Condition=\"'$(R)' == 'w'\">\
               <P Condition=\"'$(Q)' == 'w' And Exists('marker')\">/probe-only-path\\bar</P>\
               </PropertyGroup></Project>";
    std::fs::write(&path, xml).unwrap();
    let parse = |properties: Vec<String>| {
        parse_fsproj_reads(
            xml,
            &path,
            &HashMap::from([("G".to_owned(), "y".to_owned())]),
            &common::oracle_environment(),
            None,
            None,
            None,
            &ReadProbe {
                properties,
                ..ReadProbe::default()
            },
        )
        .expect("well-formed")
        .0
    };
    assert_eq!(parse(vec!["P".to_owned()]), parse(Vec::new()));
}

/// A child of a widened group whose own gate fails on every input cannot
/// write: the name keeps the candidates it had.
#[test]
fn a_widened_group_skips_a_child_that_cannot_write() {
    let xml = "<Project><PropertyGroup><R>$(G.ToUpperInvariant())</R><R>v</R>\
               <P Condition=\"'$(G.ToUpperInvariant())' == 'X'\">p</P></PropertyGroup>\
               <PropertyGroup Condition=\"'$(R)' == 'w'\">\
               <P Condition=\"'k' == 'j'\">$(G.ToUpperInvariant())</P></PropertyGroup></Project>";
    assert_eq!(
        candidates_alone(xml, "P"),
        Some(BTreeSet::from([String::new(), "p".to_owned()]))
    );
}

/// An import followed on a stale path is one MSBuild may not have made, so a
/// later literal import of the same file may be MSBuild's first (#1046): the
/// channel must not name a value written between the two. The walk follows
/// the first as a doubted import today, and so declines past the second.
#[test]
fn a_value_written_before_a_possible_first_import_is_not_named() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let xml = "<Project><PropertyGroup><Side>side_a.props</Side></PropertyGroup>\
               <Import Project=\"hidden.props\" Condition=\"'$(G.ToUpperInvariant())' == 'X'\" />\
               <Import Project=\"$(Side)\" />\
               <PropertyGroup><X>between</X></PropertyGroup>\
               <Import Project=\"side_a.props\" /></Project>";
    std::fs::write(&path, xml).unwrap();
    std::fs::write(
        dir.join("hidden.props"),
        "<Project><PropertyGroup><Side>side_b.props</Side></PropertyGroup></Project>",
    )
    .unwrap();
    std::fs::write(
        dir.join("side_a.props"),
        "<Project><PropertyGroup><X>from-a</X></PropertyGroup></Project>",
    )
    .unwrap();
    std::fs::write(dir.join("side_b.props"), "<Project />").unwrap();
    let probe = ReadProbe {
        properties: vec!["X".to_owned()],
        ..ReadProbe::default()
    };
    let mut oracle = Oracle::spawn();
    let (theirs, reads) =
        evaluate(&mut oracle, xml, &path, &probe, "x").expect("MSBuild evaluates it");
    assert_eq!(
        theirs.get("X").map(String::as_str),
        Some("from-a"),
        "MSBuild imports side_a.props for the first time at the literal import"
    );
    if let Some(candidates) = &reads.candidates["X"] {
        assert!(candidates.contains("from-a"), "{candidates:?}");
    }
}

/// An SDK the walk cannot resolve imports `Sdk.targets` after the body, unseen,
/// and that may rewrite what the body wrote (here `OutputPath`, which the
/// common targets extend with the target framework): the channel names nothing.
/// The walk's own read of it is the subject of #1048.
#[test]
fn an_unresolved_sdk_withdraws_the_channel() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let xml = "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
               <TargetFramework>net8.0</TargetFramework><OutputPath>base</OutputPath>\
               </PropertyGroup></Project>";
    std::fs::write(&path, xml).unwrap();
    let probe = ReadProbe {
        properties: vec!["OutputPath".to_owned()],
        ..ReadProbe::default()
    };
    let mut oracle = Oracle::spawn();
    let (theirs, reads) =
        evaluate(&mut oracle, xml, &path, &probe, "x").expect("MSBuild evaluates it");
    assert_ne!(
        theirs.get("OutputPath").map(String::as_str),
        Some("base"),
        "the SDK's targets rewrite the body's OutputPath"
    );
    assert!(reads.candidates_withdrawn);
    assert_eq!(reads.candidates["OutputPath"], None);
}

/// Each `<Choose>` the walk cannot decide widens what its branches write
/// once: four optional appends name the five strings they can make.
#[test]
fn each_undecided_choose_widens_once() {
    let choose = "<Choose><When Condition=\"'$(G.ToUpperInvariant())' == 'X'\">\
                  <PropertyGroup><A>$(A)y</A></PropertyGroup></When></Choose>";
    let xml = format!(
        "<Project><PropertyGroup><A></A></PropertyGroup>{}</Project>",
        choose.repeat(4)
    );
    let expected: BTreeSet<String> = (0..5).map(|n| "y".repeat(n)).collect();
    assert_eq!(candidates_alone(&xml, "A"), Some(expected));
}

#[test]
fn a_gate_reading_a_stale_value_may_take_the_write_it_skips() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let xml = "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup>\
        <Import Project=\"side0.props\" Condition=\"'$(G.ToUpperInvariant())' == 'X'\" />\
        <PropertyGroup><A>initial</A><B>initial</B><C>initial</C><D>initial</D></PropertyGroup>\
        <PropertyGroup Condition=\"'$(G.ToUpperInvariant())' == 'X'\"><A>known</A><B>known</B><C>known</C><D>known</D></PropertyGroup>\
        <PropertyGroup><A Condition=\"'$(Gate)' == 'yes'\">other</A></PropertyGroup>\
        <PropertyGroup Condition=\"'$(Gate)' == 'yes'\"><B>other</B></PropertyGroup>\
        <Choose><When Condition=\"'$(Gate)' == 'yes'\"><PropertyGroup><C>other</C></PropertyGroup></When></Choose>\
        <Choose><When Condition=\"'$(Gate)' == 'yes'\"><PropertyGroup><D>other</D></PropertyGroup></When>\
        <When Condition=\"'$(G.ToUpperInvariant())' == 'Z'\"><PropertyGroup><D>z</D></PropertyGroup></When></Choose>\
        </Project>";
    std::fs::write(&path, xml).unwrap();
    std::fs::write(
        dir.join("side0.props"),
        "<Project><PropertyGroup><Gate>yes</Gate></PropertyGroup></Project>",
    )
    .unwrap();
    let probe = ReadProbe {
        properties: ["A", "B", "C", "D", "Gate"].map(str::to_owned).to_vec(),
        ..ReadProbe::default()
    };
    let mut oracle = Oracle::spawn();
    let mut values = BTreeSet::new();
    for g in GLOBALS {
        let (theirs, reads) = evaluate(&mut oracle, xml, &path, &probe, g).expect("evaluates");
        let ours = reads.candidates;
        for name in &probe.properties {
            let real = theirs.get(name).cloned().unwrap_or_default();
            if let Some(candidates) = &ours[name] {
                assert!(
                    candidates.contains(&real),
                    "MSBuild ends with {name} = {real:?} under G={g}, not among {candidates:?}"
                );
            }
            values.insert((name.clone(), real));
        }
    }
    // MSBuild takes the write the walk skips under one of the globals.
    for name in ["A", "B", "C", "D"] {
        assert!(
            values.contains(&(name.to_owned(), "other".to_owned())),
            "{values:?}"
        );
    }
}
