//! Generative differential: `<ProjectReference>` lists shaped by `Remove`,
//! helper item lists built from `@(ProjectReference)`, and the `->Exists()`
//! item function, against the real MSBuild evaluator (the oracle's `items` op).
//!
//! ## Why this exists
//!
//! A `Remove` strips a reference by *path*, not by spelling: MSBuild normalises
//! both sides against the project directory and compares them ignoring case,
//! so `./../a/A.FSPROJ` removes `../A/A.fsproj`, and `../Nope/../A/A.fsproj`
//! names the same file lexically while `->Exists()` (which hands the raw
//! spelling to the OS) says it is missing. A helper list derived from the
//! reference list is only as complete as that list: an `Include` we could not
//! evaluate may hide a missing project whose removal takes a matching reference
//! with it. Each of those is a phantom edge if we get it wrong, and none is
//! visible to the type system.
//!
//! ## The asserted property
//!
//! The reference list's contract (`ParsedProject::project_references_uncertain`)
//! is *no phantom edges*: when the flag is clear, every reference we report is
//! one MSBuild reports, as a multiset of full paths. When, in addition, the
//! parse raised no diagnostic, the lists must be equal, order included. A
//! decline makes no claim, so the harness also counts the cases that committed
//! *through* a `Remove` that removed something, and floors that count — a model
//! that declined every `Remove` would otherwise pass vacuously.
//!
//! The filesystem is laid down for every case, because `->Exists()` probes it:
//! `A/A.fsproj` and `B/B.fsproj` exist, `Dir/` is a directory, `M/M.fsproj` is
//! missing. `../a/a.fsproj` exists on a case-insensitive filesystem and not on
//! a case-sensitive one; both sides probe the same disk, so the harness is
//! meaningful on either.
//!
//! Inputs are a fixed-seed sweep, so a failure reproduces exactly.
//!
//! ## References that read a name the walk doubts
//!
//! A missing edge is tolerated where the walk cannot say MSBuild has one. An
//! `Include` that reads a name the walk doubts (a write it refused to compute,
//! one under a gate it could not decide, a copy of either) is an edge MSBuild
//! has at a path the walk does not know, so a list missing it is no certain
//! list (#1098). [`doubted_read_sweep`] generates such writes and reads, with
//! hostile literals, and holds every certain list to MSBuild's items.

mod common;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::{
    GlobResolver, ParsedProject, PropertyRead, SdkResolver, glob_resolver, resolve_sdk, workloads,
};
use borzoi_oracle_harness::hostile::{self, Dimension, coverage, value};
use common::{Oracle, SplitMix64};
use std::collections::{BTreeSet, HashMap};
use std::path::{Component, Path, PathBuf};

/// `ProjectReference` include specs. Each names something in the layout, by a
/// spelling chosen to separate MSBuild's path comparison from string
/// comparison, and its `->Exists()` probe from both.
const REFERENCES: &[&str] = &[
    "../A/A.fsproj",
    "../B/B.fsproj",
    "../M/M.fsproj",
    // A case variant: the same file under case-insensitive comparison.
    "../a/a.fsproj",
    // Lexically the same as `../A/A.fsproj`, though `Nope/` does not exist.
    "../Nope/../A/A.fsproj",
    "./../A/./A.fsproj",
    // A directory: `->Exists()` is file-or-directory.
    "../Dir",
    // Symlinks at the leaf: one to `A/A.fsproj`, one to nothing.
    "../Linked.fsproj",
    "../Dangling.fsproj",
    // Windows spellings. MSBuild respells an `Include`'s backslashes when its
    // first segment is a directory under MSBuild's working directory, which
    // `.` and `..` always are; `->Exists()` then probes the respelled path.
    // The whole spec is respelled by its first segment, so `Sub\M.fsproj`
    // follows `..`.
    "..\\B\\B.fsproj",
    "..\\M\\M.fsproj",
    ".\\..\\A\\.\\A.fsproj",
    "..\\\\B\\B.fsproj",
    "..\\A\\A.fsproj;Sub\\M.fsproj",
    // ... and two it does not settle: a first segment only MSBuild's working
    // directory decides, and an escaped backslash, which is data.
    "A\\..\\..\\B\\B.fsproj",
    "..\\B\\B%5cx.fsproj",
    // An escaped space, naming a missing file.
    "../M/M%20x.fsproj",
    // A two-item list.
    "../A/A.fsproj;../M/M.fsproj",
    // Property splices, and an absolute spelling.
    "$(MissingRef)",
    "$(MSBuildProjectDirectory)/../B/B.fsproj",
    // A wildcard: a hidden include without a resolver, an identity-less item
    // with one.
    "../*/A.fsproj",
];

/// `Remove` (and helper `Exclude`) specs.
const REMOVES: &[&str] = &[
    "../A/A.fsproj",
    "./../X/../a/./A.FSPROJ",
    "../M/M.fsproj",
    "../Dir/",
    "../Linked.fsproj",
    "@(ProjectReference)",
    "@(projectreference)",
    "@(ProjectReference->Exists())",
    "@(H1)",
    "@(h2)",
    "@(H1->Exists())",
    "@(H1);../B/B.fsproj",
    "$(MissingRef)",
    // An item expression arriving through a property.
    "$(RemoveSpec)",
    // A transform: not modelled.
    "@(H1->'%(Identity)')",
];

/// Gates on an element or a group: none, exactly true, exactly false, outside
/// the condition grammar (one false in MSBuild, one true — the true one is what
/// puts a hidden include in MSBuild's list), and decided by a property written
/// under a gate we cannot evaluate (untrusted).
const GATES: &[&str] = &[
    "",
    " Condition=\"'$(NoSuchProperty)' == ''\"",
    " Condition=\"'$(NoSuchProperty)' != ''\"",
    UNSUPPORTED_FALSE,
    UNSUPPORTED_TRUE,
    " Condition=\"'$(Unpinned)' == ''\"",
];

const UNSUPPORTED_FALSE: &str = " Condition=\"'É' == 'Ê'\"";
const UNSUPPORTED_TRUE: &str = " Condition=\"'É' == 'é'\"";

/// The gates every evaluation decides exactly.
const EXACT_GATES: &[&str] = &[
    "",
    " Condition=\"'$(NoSuchProperty)' == ''\"",
    " Condition=\"'$(NoSuchProperty)' != ''\"",
];

/// Which part of the space a case is drawn from. A `Clean` case uses only
/// constructs the model decides exactly — exact gates, decided groups, and
/// spellings inside the identity domain — so it must commit; that obligation,
/// per case, is what keeps the sweep from passing by declining. An `Any` case
/// may hold anything, and is held only to no phantom edges.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Space {
    Clean,
    Any,
}

impl Space {
    fn gate(self, rng: &mut SplitMix64) -> &'static str {
        if rng.below(3) != 0 {
            return "";
        }
        match self {
            Space::Clean => rng.pick(EXACT_GATES),
            Space::Any => rng.pick(GATES),
        }
    }

    fn reference(self, rng: &mut SplitMix64) -> &'static str {
        loop {
            let spec = *rng.pick(REFERENCES);
            // Outside the domain: a backslash MSBuild's working directory or
            // an escape decides, a wildcard (hidden without a resolver,
            // identity-less with one), and a dangling symlink `->Exists()`
            // cannot read.
            let settled_spelling =
                !spec.contains('\\') || (spec.starts_with('.') && !spec.contains("%5c"));
            let clean = settled_spelling && !spec.contains('*') && !spec.contains("Dangling");
            if self == Space::Any || clean {
                return spec;
            }
        }
    }

    fn remove(self, rng: &mut SplitMix64) -> &'static str {
        loop {
            let spec = *rng.pick(REMOVES);
            // A transform is not modelled, and the property pass flags a
            // property whose body holds an item reference, so a read of one
            // declines.
            let clean = !spec.contains("->'") && spec != "$(RemoveSpec)";
            if self == Space::Any || clean {
                return spec;
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Op {
    Include {
        spec: &'static str,
        gate: &'static str,
    },
    /// The idiom: `<H Include="@(ProjectReference)" Exclude="@(ProjectReference->Exists())" />`.
    NonExistentHelper {
        helper: &'static str,
        gate: &'static str,
    },
    /// `<H Include="@(ProjectReference->Exists())" />`.
    ExistentHelper {
        helper: &'static str,
        gate: &'static str,
    },
    /// `<H Include="spec" Exclude="exclude" Tag="…" />` from the reference
    /// alphabet.
    LiteralHelper {
        helper: &'static str,
        spec: &'static str,
        exclude: Option<&'static str>,
        tag: Option<&'static str>,
    },
    /// `<H Remove="spec" />`.
    HelperRemove {
        helper: &'static str,
        spec: &'static str,
        gate: &'static str,
    },
    /// `<ProjectReference Remove="spec" />`.
    Remove {
        spec: &'static str,
        gate: &'static str,
    },
    /// `<target Remove="spec" MatchOnMetadata="Tag" />`: matched by metadata
    /// value, not by path. MSBuild requires every fragment to be an item
    /// reference.
    MetadataRemove {
        target: &'static str,
        spec: &'static str,
    },
}

impl Op {
    fn generate(rng: &mut SplitMix64, space: Space) -> Op {
        let helper = *rng.pick(&["H1", "H2", "h1"]);
        match rng.below(9) {
            0..=2 => Op::Include {
                spec: space.reference(rng),
                gate: space.gate(rng),
            },
            3 => Op::NonExistentHelper {
                helper,
                gate: space.gate(rng),
            },
            4 => Op::ExistentHelper {
                helper,
                gate: space.gate(rng),
            },
            5 => Op::LiteralHelper {
                helper,
                spec: space.reference(rng),
                exclude: (rng.below(2) == 0).then(|| space.remove(rng)),
                tag: (rng.below(2) == 0).then(|| *rng.pick(&["x", "y"])),
            },
            6 => Op::HelperRemove {
                helper,
                spec: space.remove(rng),
                gate: space.gate(rng),
            },
            7 if space == Space::Any => Op::MetadataRemove {
                target: rng.pick(&["H1", "h2", "ProjectReference"]),
                spec: rng.pick(&["@(H1)", "@(h2)", "@(ProjectReference)"]),
            },
            _ => Op::Remove {
                spec: space.remove(rng),
                gate: space.gate(rng),
            },
        }
    }

    fn xml(&self) -> String {
        let reference = "ProjectReference";
        match self {
            Op::Include { spec, gate } => format!("<{reference} Include=\"{spec}\"{gate} />"),
            Op::NonExistentHelper { helper, gate } => format!(
                "<{helper} Include=\"@(ProjectReference)\" Exclude=\"@(ProjectReference->Exists())\"{gate} />"
            ),
            Op::ExistentHelper { helper, gate } => {
                format!("<{helper} Include=\"@(ProjectReference->Exists())\"{gate} />")
            }
            Op::LiteralHelper {
                helper,
                spec,
                exclude,
                tag,
            } => {
                let exclude = exclude.map_or(String::new(), |e| format!(" Exclude=\"{e}\""));
                let tag = tag.map_or(String::new(), |t| format!(" Tag=\"{t}\""));
                format!("<{helper} Include=\"{spec}\"{exclude}{tag} />")
            }
            Op::HelperRemove { helper, spec, gate } => {
                format!("<{helper} Remove=\"{spec}\"{gate} />")
            }
            Op::Remove { spec, gate } => format!("<{reference} Remove=\"{spec}\"{gate} />"),
            Op::MetadataRemove { target, spec } => {
                format!("<{target} Remove=\"{spec}\" MatchOnMetadata=\"Tag\" />")
            }
        }
    }

    fn is_reference_remove(&self) -> bool {
        match self {
            Op::Remove { .. } => true,
            Op::MetadataRemove { target, .. } => target.eq_ignore_ascii_case("ProjectReference"),
            _ => false,
        }
    }
}

/// A run of operations: an `<ItemGroup>` under a gate, or the `<ItemGroup>` of
/// a `<Choose>` branch whose `<When>` we cannot decide. `runs` says whether
/// MSBuild takes that branch: only a branch it takes puts items in its lists,
/// so only that one can show an undecided branch's items missing from ours.
#[derive(Debug, Clone)]
enum Block {
    Group { gate: &'static str, ops: Vec<Op> },
    UndecidedChoose { runs: bool, ops: Vec<Op> },
}

impl Block {
    fn generate(rng: &mut SplitMix64, space: Space) -> Block {
        let ops = (0..1 + rng.below(3))
            .map(|_| Op::generate(rng, space))
            .collect();
        match (rng.below(8), space) {
            (0, Space::Any) => Block::UndecidedChoose {
                runs: rng.below(2) == 0,
                ops,
            },
            (1, _) => Block::Group {
                gate: space.gate(rng),
                ops,
            },
            _ => Block::Group { gate: "", ops },
        }
    }

    fn ops(&self) -> &[Op] {
        match self {
            Block::Group { ops, .. } | Block::UndecidedChoose { ops, .. } => ops,
        }
    }

    fn without_reference_removes(&self) -> Block {
        let keep = |ops: &[Op]| {
            ops.iter()
                .filter(|op| !op.is_reference_remove())
                .cloned()
                .collect()
        };
        match self {
            Block::Group { gate, ops } => Block::Group {
                gate,
                ops: keep(ops),
            },
            Block::UndecidedChoose { runs, ops } => Block::UndecidedChoose {
                runs: *runs,
                ops: keep(ops),
            },
        }
    }

    fn xml(&self, out: &mut String) {
        let body = |out: &mut String, indent: &str, ops: &[Op]| {
            for op in ops {
                out.push_str(&format!("{indent}{}\n", op.xml()));
            }
        };
        match self {
            Block::Group { gate, ops } => {
                out.push_str(&format!("  <ItemGroup{gate}>\n"));
                body(out, "    ", ops);
                out.push_str("  </ItemGroup>\n");
            }
            Block::UndecidedChoose { runs, ops } => {
                let gate = if *runs {
                    UNSUPPORTED_TRUE
                } else {
                    UNSUPPORTED_FALSE
                };
                out.push_str(&format!(
                    "  <Choose>\n    <When{gate}>\n      <ItemGroup>\n"
                ));
                body(out, "        ", ops);
                out.push_str("      </ItemGroup>\n    </When>\n  </Choose>\n");
            }
        }
    }
}

fn project_xml(blocks: &[Block]) -> String {
    let mut s = String::from("<Project>\n  <PropertyGroup>\n");
    s.push_str("    <MissingRef>../M/M.fsproj</MissingRef>\n");
    s.push_str("    <RemoveSpec>@(H1)</RemoveSpec>\n");
    s.push_str("    <Unpinned Condition=\"'É' == 'Ê'\">set</Unpinned>\n");
    s.push_str("  </PropertyGroup>\n");
    for block in blocks {
        block.xml(&mut s);
    }
    s.push_str("</Project>\n");
    s
}

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

struct Outcome {
    committed: bool,
    /// Committed, and a `Remove` changed the list on MSBuild's side — the case
    /// that only a modelled `Remove` can commit.
    committed_through_a_remove: bool,
}

/// Lay down the layout every case probes, returning the project path.
fn layout(root: &Path) -> PathBuf {
    for file in ["A/A.fsproj", "B/B.fsproj"] {
        let path = root.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, "<Project />").unwrap();
    }
    std::fs::create_dir_all(root.join("Dir")).unwrap();
    std::fs::create_dir_all(root.join("proj")).unwrap();
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(root.join("A/A.fsproj"), root.join("Linked.fsproj")).unwrap();
        std::os::unix::fs::symlink(root.join("Gone.fsproj"), root.join("Dangling.fsproj")).unwrap();
    }
    root.join("proj/Demo.fsproj")
}

/// `with_resolver` selects the seam: without one a wildcard `Include` is a
/// hidden include; with the shipped resolver it expands to items that carry no
/// identity, which a `Remove` cannot match.
fn check(oracle: &mut Oracle, blocks: &[Block], with_resolver: bool) -> Outcome {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    let xml = project_xml(blocks);
    std::fs::write(&proj, &xml).unwrap();

    let resolver: &GlobResolver<'_> = &glob_resolver::resolve;
    let parsed: ParsedProject = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        with_resolver.then_some(resolver),
    )
    .expect("well-formed XML parses");
    let theirs: Vec<PathBuf> = oracle
        .items(&xml, &proj, "ProjectReference", &[])
        .expect("MSBuild evaluates these documents")
        .iter()
        .map(|p| lexical(p))
        .collect();

    if parsed.project_references_uncertain {
        return Outcome {
            committed: false,
            committed_through_a_remove: false,
        };
    }
    let ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| lexical(&item.include.to_string_lossy()))
        .collect();
    let mut unmatched = theirs.clone();
    for path in &ours {
        let Some(at) = unmatched.iter().position(|p| p == path) else {
            panic!(
                "phantom edge: {} is not in MSBuild's list.\nproject:\n{xml}\nours:   {ours:#?}\ntheirs: {theirs:#?}\ndiags: {:#?}",
                path.display(),
                parsed.diagnostics
            );
        };
        unmatched.remove(at);
    }
    if parsed.diagnostics.is_empty() {
        assert_eq!(
            ours, theirs,
            "a diagnostic-free parse must match exactly.\nproject:\n{xml}"
        );
    }
    let removed_something = blocks
        .iter()
        .any(|block| block.ops().iter().any(Op::is_reference_remove))
        && theirs.len() < included_count(blocks, oracle, &proj);
    Outcome {
        committed: true,
        committed_through_a_remove: removed_something,
    }
}

/// How many references MSBuild holds with every reference `Remove` deleted.
fn included_count(blocks: &[Block], oracle: &mut Oracle, proj: &Path) -> usize {
    let kept: Vec<Block> = blocks
        .iter()
        .map(Block::without_reference_removes)
        .collect();
    let xml = project_xml(&kept);
    std::fs::write(proj, &xml).unwrap();
    oracle
        .items(&xml, proj, "ProjectReference", &[])
        .expect("MSBuild evaluates these documents")
        .len()
}

/// Hand-picked corners, each pinned against the real evaluator, and each of
/// which must commit on both seams: the idiom over a complete checkout, over a
/// missing reference, the path-normalising literal `Remove`, the self-reference
/// clear, and an `->Exists()` filter driving the `Remove` directly.
#[test]
fn hand_picked_corners_commit_and_agree() {
    let mut oracle = Oracle::spawn();
    let include = |spec| Op::Include { spec, gate: "" };
    let remove = |spec| Op::Remove { spec, gate: "" };
    let idiom = [
        Op::NonExistentHelper {
            helper: "H1",
            gate: "",
        },
        remove("@(H1)"),
    ];
    let cases: Vec<Vec<Op>> = vec![
        [
            vec![include("../A/A.fsproj"), include("../B/B.fsproj")],
            idiom.to_vec(),
        ]
        .concat(),
        [
            vec![include("../A/A.fsproj"), include("../M/M.fsproj")],
            idiom.to_vec(),
        ]
        .concat(),
        [vec![include("../Nope/../A/A.fsproj")], idiom.to_vec()].concat(),
        vec![
            include("../A/A.fsproj"),
            include("../B/B.fsproj"),
            remove("./../X/../a/./A.FSPROJ"),
        ],
        vec![include("../A/A.fsproj"), remove("@(ProjectReference)")],
        vec![
            include("../A/A.fsproj"),
            include("../M/M.fsproj"),
            remove("@(ProjectReference->Exists())"),
        ],
        // Windows spellings, which `->Exists()` sees respelled: `..\B\B.fsproj`
        // exists, and so `Sub\M.fsproj` is probed under the project.
        [
            vec![
                include("..\\B\\B.fsproj"),
                include("..\\M\\M.fsproj"),
                include("..\\A\\A.fsproj;Sub\\M.fsproj"),
            ],
            idiom.to_vec(),
        ]
        .concat(),
    ];
    for ops in cases {
        let blocks = [Block::Group { gate: "", ops }];
        for with_resolver in [false, true] {
            let outcome = check(&mut oracle, &blocks, with_resolver);
            assert!(
                outcome.committed,
                "a corner the model must commit declined (resolver: {with_resolver}):\n{}",
                project_xml(&blocks)
            );
        }
    }
}

/// The phantom a hidden include makes possible. MSBuild includes
/// `../A/A.fsproj` behind a gate we cannot evaluate, beside a visible
/// `../a/a.fsproj`. On a case-sensitive filesystem only the hidden one exists,
/// so `@(ProjectReference->Exists())` holds it alone — and the `Remove` then
/// takes `../a/a.fsproj` too, since the two compare equal ignoring case. Our
/// helper, built from a list without the hidden item, is empty; only the
/// hidden-include guard stops us keeping `../a/a.fsproj`. On a case-insensitive
/// filesystem the shape is harmless and the check still holds.
///
/// (The non-existent idiom itself cannot be broken this way: its `Exclude`
/// also compares ignoring case, so a missing reference that matches an existing
/// one never reaches the helper, and the `Remove` never takes an existing
/// reference.)
///
/// The hidden include arrives two ways: under an element gate we cannot
/// evaluate, and in a `<Choose>` branch MSBuild takes but we cannot decide.
#[test]
fn a_hidden_include_cannot_hide_a_removal() {
    let mut oracle = Oracle::spawn();
    let visible_then_remove = [
        Op::Include {
            spec: "../a/a.fsproj",
            gate: "",
        },
        Op::ExistentHelper {
            helper: "H1",
            gate: "",
        },
        Op::Remove {
            spec: "@(H1)",
            gate: "",
        },
    ];
    let hidden = Op::Include {
        spec: "../A/A.fsproj",
        gate: "",
    };
    let shapes = [
        vec![Block::Group {
            gate: "",
            ops: [
                vec![Op::Include {
                    spec: "../A/A.fsproj",
                    gate: UNSUPPORTED_TRUE,
                }],
                visible_then_remove.to_vec(),
            ]
            .concat(),
        }],
        vec![
            Block::UndecidedChoose {
                runs: true,
                ops: vec![hidden],
            },
            Block::Group {
                gate: "",
                ops: visible_then_remove.to_vec(),
            },
        ],
    ];
    for blocks in shapes {
        for with_resolver in [false, true] {
            check(&mut oracle, &blocks, with_resolver);
        }
    }
}

/// An undecided `<Choose>` whose branch holds only items the idiom never reads
/// — a helper of another type, whichever way MSBuild decides the branch — must
/// leave the idiom committing: such a branch can change neither the reference
/// list nor the helper derived from it.
#[test]
fn an_undecided_choose_over_unrelated_items_commits() {
    let mut oracle = Oracle::spawn();
    for runs in [false, true] {
        let blocks = [
            Block::UndecidedChoose {
                runs,
                ops: vec![Op::LiteralHelper {
                    helper: "H2",
                    spec: "../M/M.fsproj",
                    exclude: None,
                    tag: None,
                }],
            },
            Block::Group {
                gate: "",
                ops: vec![
                    Op::Include {
                        spec: "../A/A.fsproj",
                        gate: "",
                    },
                    Op::Include {
                        spec: "../M/M.fsproj",
                        gate: "",
                    },
                    Op::NonExistentHelper {
                        helper: "H1",
                        gate: "",
                    },
                    Op::Remove {
                        spec: "@(H1)",
                        gate: "",
                    },
                ],
            },
        ];
        for with_resolver in [false, true] {
            let outcome = check(&mut oracle, &blocks, with_resolver);
            assert!(
                outcome.committed && outcome.committed_through_a_remove,
                "an unrelated undecided branch (runs: {runs}) declined the idiom \
                 (resolver: {with_resolver}):\n{}",
                project_xml(&blocks)
            );
        }
    }
}

/// A `MatchOnMetadata` remove matches by metadata value: `@(ProjectReference)`
/// carries no `Tag`, so it removes the untagged helper items whatever their
/// path, and keeps none of them by path. Matching it by identity instead keeps
/// `../A/A.fsproj` in the helper but drops `../M/M.fsproj` — the opposite split —
/// and the reference `Remove` driven by the helper then keeps `../M/M.fsproj`,
/// which MSBuild removes. (Found by the soak.)
#[test]
fn a_metadata_matched_remove_is_not_a_path_match() {
    let mut oracle = Oracle::spawn();
    let blocks = [Block::Group {
        gate: "",
        ops: vec![
            Op::Include {
                spec: "../M/M.fsproj",
                gate: "",
            },
            Op::LiteralHelper {
                helper: "H1",
                spec: "../A/A.fsproj;../M/M.fsproj",
                exclude: None,
                tag: None,
            },
            Op::MetadataRemove {
                target: "H1",
                spec: "@(ProjectReference)",
            },
            Op::Remove {
                spec: "@(H1)",
                gate: "",
            },
        ],
    }];
    for with_resolver in [false, true] {
        check(&mut oracle, &blocks, with_resolver);
    }
}

/// The idiom inside a real `Microsoft.NET.Sdk` project, where it was found:
/// the SDK chain must not make the walk opaque or poison the reference list,
/// or the `Remove` never commits where it matters.
#[test]
fn the_non_existent_idiom_commits_on_the_real_sdk() {
    let mut oracle = Oracle::spawn();
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let proj = layout(&root);
    let xml = r#"<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
  </PropertyGroup>
  <ItemGroup>
    <ProjectReference Include="../A/A.fsproj" />
    <ProjectReference Include="../M/M.fsproj" />
  </ItemGroup>
  <ItemGroup Condition="'$(DeclaredReferencesOnly)' != 'true'">
    <ProjectReferenceNonExistent Include="@(ProjectReference)" Exclude="@(ProjectReference->Exists())" />
    <ProjectReference Remove="@(ProjectReferenceNonExistent)" />
  </ItemGroup>
</Project>
"#;
    std::fs::write(&proj, xml).unwrap();
    let dotnet_root = common::dotnet_root_from_env();
    let (user_dotnet_root, overrides_present) = common::workload_env_from_process();
    let sdk = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
        resolve_sdk(
            &dotnet_root,
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: user_dotnet_root.as_deref(),
                overrides_present,
                global_json: Default::default(),
                process_architecture: None,
            },
            observer,
        )
    };
    let resolver: &GlobResolver<'_> = &glob_resolver::resolve;
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        Some(&sdk as &SdkResolver<'_>),
        Some(resolver),
    )
    .expect("well-formed XML parses");
    let theirs: Vec<PathBuf> = oracle
        .items(xml, &proj, "ProjectReference", &[])
        .expect("MSBuild evaluates the project")
        .iter()
        .map(|p| lexical(p))
        .collect();
    assert_eq!(
        theirs,
        vec![root.join("A/A.fsproj")],
        "MSBuild drops the missing reference"
    );
    assert!(
        !parsed.project_references_uncertain,
        "the idiom must commit on the real SDK; diagnostics: {:#?}",
        parsed.diagnostics
    );
    let ours: Vec<PathBuf> = parsed
        .project_references
        .iter()
        .map(|item| lexical(&item.include.to_string_lossy()))
        .collect();
    assert_eq!(ours, theirs);
}

/// Half the cases are drawn from the clean space and must commit; every case
/// is held to no phantom edges.
fn sweep(oracle: &mut Oracle, seed: u64, cases: usize) {
    let mut rng = SplitMix64(seed);
    let mut committed = 0usize;
    let mut through_a_remove = 0usize;
    for case in 0..cases {
        let space = if case % 2 == 0 {
            Space::Clean
        } else {
            Space::Any
        };
        let blocks: Vec<Block> = (0..1 + rng.below(3))
            .map(|_| Block::generate(&mut rng, space))
            .collect();
        for with_resolver in [false, true] {
            let outcome = check(oracle, &blocks, with_resolver);
            assert!(
                outcome.committed || space == Space::Any,
                "a clean case declined (resolver: {with_resolver}):\n{}",
                project_xml(&blocks)
            );
            committed += usize::from(outcome.committed);
            through_a_remove += usize::from(outcome.committed_through_a_remove);
        }
    }
    let total = cases * 2;
    eprintln!(
        "project-reference removes: {committed}/{total} committed, \
         {through_a_remove} through a Remove that removed something"
    );
    // The clean obligation above already rules out a decline-everything model;
    // this rules out a generator that has stopped producing effective removes.
    assert!(
        through_a_remove * 40 >= total,
        "only {through_a_remove}/{total} checks committed through an effective Remove \
         — the generator has drifted away from the operation under test"
    );
}

/// The sweep, at a fixed seed. Every case that commits is checked against
/// MSBuild; the floor keeps a decline-every-`Remove` model from passing
/// vacuously.
#[test]
fn generated_reference_lists_have_no_phantom_edges() {
    sweep(&mut Oracle::spawn(), 0x0550_7e40_5eed, 150);
}

/// The fresh-seed twin of [`generated_reference_lists_have_no_phantom_edges`].
#[test]
#[ignore = "fresh-seed soak; run with --ignored"]
fn soak() {
    let (seed, cases) = common::soak_parameters("project-reference remove", 1000);
    sweep(&mut Oracle::spawn(), seed, cases);
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

/// A write's body in the doubted-read sweep: a hostile or plain literal, a
/// function the walk does not compute, or a read of the other name.
fn read_sweep_body(rng: &mut SplitMix64, other: &str) -> hostile::Drawn<String> {
    match rng.below(4) {
        0 => {
            let plain = *rng.pick(&["a", "lib", "B1"]);
            match hostile::sample(&read_sweep_values(plain), rng.next()) {
                Some(entry) => hostile::Drawn::of(entry).map(|v| v.render(plain)),
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

/// One document of the doubted-read sweep: writes of `P` and `Q`, then
/// unconditional `<ProjectReference>`s, each with an `Origin` metadatum
/// naming it and an `Include` of the names it reads.
struct ReadDocument {
    writes: Vec<ReadWrite>,
    /// Each reference's `Include`, and the names it reads.
    references: Vec<(String, Vec<&'static str>)>,
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
                match rng.below(3) {
                    0 => (format!("E{i}_$({name}).fsproj"), vec![name]),
                    1 => (format!("E{i}_$({name}.Length).fsproj"), vec![name]),
                    _ => (format!("E{i}_$(P)_$(Q).fsproj"), vec!["P", "Q"]),
                }
            })
            .collect();
        ReadDocument { writes, references }
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
            references: vec![("E0_$(P)_$(Q).fsproj".to_owned(), vec!["P", "Q"])],
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
        for (i, (include, _)) in self.references.iter().enumerate() {
            xml.push_str(&format!(
                "  <ItemGroup><ProjectReference Include=\"{include}\" Origin=\"E{i}\" /></ItemGroup>\n"
            ));
        }
        xml.push_str("</Project>\n");
        xml
    }

    /// The hostile dimensions a reference reads: those of each name's last
    /// write, where that write is unconditional (so MSBuild makes it) and a
    /// reference reads its name. A write a later one replaces, or one under
    /// a gate, may reach no reference.
    fn read_dimensions(&self) -> BTreeSet<Dimension> {
        let mut dimensions = BTreeSet::new();
        for name in READ_NAMES {
            let read = self
                .references
                .iter()
                .any(|(_, reads)| reads.contains(&name));
            if let Some(last) = self.writes.iter().rev().find(|w| w.name == name)
                && read
                && last.condition.is_empty()
            {
                dimensions.extend(last.body.hostile.iter().copied());
            }
        }
        dimensions
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
    Dimension::OverwrittenLater,
    "a value a reference reads is its name's last write here, which nothing puts back",
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
fn grade_read_document(oracle: &mut Oracle, document: &ReadDocument) -> ReadOutcome {
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
        return ReadOutcome::MsbuildRejects;
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
    let owed = document
        .references
        .iter()
        .enumerate()
        .any(|(i, (_, reads))| reads.iter().any(|name| doubted(name)) && !theirs_of(i).is_empty());
    if parsed.project_references_uncertain {
        return ReadOutcome::Declined { owed };
    }
    assert_eq!(
        parsed.project_references.len(),
        (0..document.references.len())
            .map(|i| ours_of(i).len())
            .sum::<usize>(),
        "every item the walk captured is of one reference:\n{xml}"
    );
    for (i, (_, reads)) in document.references.iter().enumerate() {
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
    ReadOutcome::Committed
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
    let witnesses: Vec<ReadDocument> = read_sweep_values("lib")
        .iter()
        .filter(|entry| !excluded.contains(&entry.dimension))
        .map(|entry| ReadDocument::witness(hostile::Drawn::of(entry).map(|v| v.render("lib"))))
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
        let read = document.read_dimensions();
        let outcome = grade_read_document(oracle, &document);
        census.reached(
            &read,
            match outcome {
                ReadOutcome::MsbuildRejects => "msbuild-rejects",
                ReadOutcome::Declined { .. } => "decline",
                ReadOutcome::Committed => "commit",
            },
        );
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
         fsproj_project_reference_remove_diff doubted_reads",
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
