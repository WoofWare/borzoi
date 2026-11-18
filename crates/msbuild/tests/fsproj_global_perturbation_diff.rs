//! Differential test: the walker's evaluated properties and items vs the real
//! MSBuild evaluator, **under a swept set of global properties**.
//!
//! ## Why the existing differentials cannot see this
//!
//! Every other harness in this crate — `condition_diff`, `property_expr_diff`,
//! `fsproj_property_table_diff`, `fsproj_msbuild_diff` — evaluates both sides
//! under the *same* globals (in practice, none). That makes them structurally
//! blind to one whole defect class: a value whose evaluation **depends on a
//! global the caller supplied**, through a route our walker does not model.
//! Under a fixed global set the two sides agree exactly, so certain-implies-
//! exact passes; the wrongness only appears when the global changes and one
//! side moves while the other does not.
//!
//! It is not a hypothetical. The LSP injects `Configuration=Debug,
//! Platform=AnyCPU` into every evaluation (`workspace::default_build_properties`
//! — a guess, since it cannot know what the user last built), and then publishes
//! what comes back — define constants, the Compile order, project references —
//! as though it were a fixed fact about the project. Any of those may in truth
//! be "the value under the globals the editor picked".
//!
//! It also seeds `TargetFramework` on every multi-targeted project, to serve the
//! first-declared inner build (`lsp::tfm_policy`, fsproj plan E1/E2/E7). That
//! one is not a guess — it is the policy — but it is the same structural
//! exposure, and it moves far more of the SDK chain than `Configuration` does
//! because the whole TFM inference runs under it. So the sweep carries an
//! inner-build global set: what the LSP evaluates a real user's multi-targeted
//! `.fsproj` under is checked exactly, not assumed.
//!
//! ## The contract
//!
//! Unchanged from the crate's other harnesses, with the global set as a new
//! axis quantified over rather than fixed:
//!
//! - We **commit** `N = V` under globals `G` ⟹ MSBuild evaluating the same
//!   document at the same path **with global properties `G`** gives exactly `V`.
//! - We **decline** (a diagnostic, an untrusted provenance, `items_uncertain`)
//!   ⟹ no claim.
//! - MSBuild **rejects** the document under `G` ⟹ we must not have committed
//!   anything for it.
//!
//! Note what this subsumes. If we commit the same `V` under two global sets but
//! MSBuild moves between them, one of the two per-set checks must fail — so the
//! blindness this file exists to catch *is* a certain-implies-exact violation,
//! once the axis is swept. No new contract was needed; only a harness that
//! varies the thing the others hold fixed.
//!
//! ## The census
//!
//! Soundness is one-sided, so a walker that declined every global-dependent
//! value would pass silently. The tests therefore also print, and floor, a
//! **movement census**: which `(document, name)` pairs MSBuild moves across the
//! sweep, and for each, what we did — tracked it (committed two or more distinct
//! values, so the exactness check above was genuinely exercised on this axis),
//! declined it as untrusted, or never reached it at all. The floors are on
//! *tracked*, since that is the only one of the three that proves anything was
//! checked — and over the names the *document derives*, never over
//! `Configuration`/`Platform` themselves, which move because they are what the
//! sweep varies (see [`swept_global_names`]).
//!
//! Each case additionally **pins** what MSBuild must evaluate its names to under
//! the LSP's own globals. Without that, a case's comment is a claim nothing
//! checks: the sweep asserts only that we agree with MSBuild, which a fixture
//! demonstrating the exact opposite of its stated route satisfies perfectly.
//!
//! That census is the measurement. It says how much of the evaluator's committed
//! surface is actually global-dependent, and — more usefully — where the
//! evaluator currently pays for its soundness in silence rather than in
//! wrongness, which is the input to deciding whether the provenance model needs
//! a "depends on a caller-supplied global" dimension at all.
//!
//! ## The startup directory
//!
//! MSBuild also reads the directory its process started in, as
//! `MSBuildStartupDirectory`, and our walk takes it as an input only where it
//! models a process the caller launches (`test_support::parse_fsproj_reads`'s
//! `startup_directory`, the restore cone's A₁ path). So every point of the
//! sweep is evaluated by MSBuild started from each of [`startups`]'s
//! directories, one oracle child each, and by our walk in both of its modes:
//!
//! - **Served** (no startup directory, as every evaluation the LSP serves
//!   runs): what we commit must equal MSBuild's value from *every* directory,
//!   so nothing the startup directory moves may be committed.
//! - **Supplied** (`Some(d)`): what we commit must equal MSBuild's value when
//!   started from `d`.
//!
//! The census counts the `(case, name, globals)` points where the startup
//! directory moves MSBuild's value, how many of them the supplied mode tracks
//! (commits two or more distinct values for), and how the served mode declines
//! each (untrusted, or never reached).
//!
//! ## The candidate channel
//!
//! At every point the walk run with a startup directory also names the values
//! each read-back name may hold (`EvaluationReads::candidates`, #1009), and
//! MSBuild's value must be among them unless the walk says the name may hold
//! anything. `fsproj_candidates_diff` holds the channel to generated gates; this
//! sweep holds it to the routes and the real SDK chain.
//!
//! ## The evaluation graded
//!
//! MSBuild is the oracle's `project` and `items` ops, which evaluate as a build
//! does (a `ProjectInstance`). That is what lets the sweep vary toolset names
//! as globals (`MSBuildSDKsPath`, `MSBuildExtensionsPath`,
//! `MSBuildUserExtensionsPath`): the editable `Project` a design-time host
//! loads refuses a global `MSBuildSDKsPath` in the oracle's process, where
//! `-p:` on a build sets it.
//!
//! ## What it does not reach
//!
//! Unlike a self-perturbation oracle, this one has a reference that reads
//! everything, so it has no *structural* blind spot — but it is still a finite
//! sweep, and a green run means only what it covers.
//!
//! - **Two output channels**: the evaluated property table, over the names in
//!   [`READ_NAMES`] / the SDK test's own list, and the `Compile` item set. The
//!   other things the LSP publishes off the same evaluation —
//!   `define_constants`, `project_references`, `package_references`, the TFM
//!   selection — are their own surfaces with their own uncertainty flags, and a
//!   global-dependence bug in one of those would not be seen here.
//! - **The routes in [`CASES`], the generator's grammar, and five SDK
//!   projects.** A route none of them takes is untested. Widening means adding
//!   a case; the anti-vacuity floors refuse one that measures nothing.
//! - **Whatever the global sweep in [`global_sets`] does not vary.** A value
//!   that depends on, say, `RuntimeIdentifier` is a fixed fact as far as this
//!   file is concerned.
//! - **The three startup directories.** Their spellings are plain; the value
//!   domain (a space, `;`, `%20`, `$`) is `startup_directory_diff`'s.

#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::test_support::{EvaluationReads, PropertyRead, ReadProbe, parse_fsproj_reads};
use borzoi_msbuild::{ParsedProject, resolve_sdk, workloads};
use common::{Oracle, SplitMix64};
use tempfile::TempDir;

/// Property names read back from both sides. `Configuration` and `Platform` are
/// in the list deliberately: a global of that name is *itself* a value the
/// document may try to overwrite, and whether the write wins is the whole
/// `TreatAsLocalProperty` question.
const READ_NAMES: &[&str] = &["Out", "Helper", "Configuration", "Platform"];

/// One document, with any sidecar files it imports or probes for.
struct Case {
    /// Unique — it names the case's own directory, so no case can see another's
    /// `Exists()` probes or `*.props`.
    name: &'static str,
    xml: &'static str,
    files: &'static [(&'static str, &'static str)],
    /// What **MSBuild** must evaluate these names to under [`PIN_GLOBALS`].
    ///
    /// Without this, a case's comment is a claim nothing checks: the sweep only
    /// asserts that *we* agree with MSBuild, which a fixture demonstrating the
    /// opposite of its stated route satisfies perfectly. (That is not
    /// hypothetical — `treat-as-local-in-import` was written asserting the
    /// import's opt-out was inert, and passed, because MSBuild honours it and so
    /// do we.) The pins are asserted against the oracle, never against our side:
    /// an expectation I reasoned out is exactly as untrustworthy as the code I
    /// reasoned out.
    pins: &'static [(&'static str, &'static str)],
    /// Names **MSBuild** must move between [`startups`]'s directories under
    /// [`PIN_GLOBALS`]: the case's claim to take a route from the startup
    /// directory, checked like [`Case::pins`].
    startup_moves: &'static [&'static str],
}

/// The global set the [`Case::pins`] are stated under: what the LSP injects.
/// The pins are read from MSBuild started in the first of [`startups`]'s
/// directories.
const PIN_GLOBALS: &[(&str, &str)] = &[("Configuration", "Debug"), ("Platform", "AnyCPU")];

const IMPORT_SETS_OUT: &str =
    r#"<Project><PropertyGroup><Out>from-import</Out></PropertyGroup></Project>"#;

/// The routes by which a global reaches a committed value. Each is a shape the
/// design notes for the output-directory work found leaking, written down as an
/// input rather than as a thing to remember.
const CASES: &[Case] = &[
    // The direct read.
    Case {
        name: "direct",
        xml: "<Project>\n  <PropertyGroup>\n    <Out>$(Configuration)</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "Debug")],
        startup_moves: &[],
    },
    // The SDK's own idiom, written against a name the sweep actually supplies
    // (`<Configuration Condition="'$(Configuration)' == ''">…`). This is the
    // *read-only defaulting* rule, and it splits the sweep three ways where a
    // gate on an unsupplied name could not split it at all: with no
    // `Configuration` global the write fires; with `Configuration=Debug` MSBuild
    // discards the write unevaluated and the global stands; and with
    // `Configuration=""` the global is **empty but still read-only**, so the
    // write is discarded there too and the value stays empty — the one row that
    // distinguishes "absent" from "supplied empty".
    Case {
        name: "default-write",
        xml: "<Project>\n  <PropertyGroup>\n    <Configuration Condition=\"'$(Configuration)' == ''\">DefaultedInDocument</Configuration>\n    <Out>[$(Configuration)]-[$(Platform)]</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "[Debug]-[AnyCPU]"), ("Configuration", "Debug")],
        startup_moves: &[],
    },
    // A gate on the *group*, so the walk must decide whether to visit the writes
    // at all — the shape a property-walk that only inspects visited groups gets
    // wrong.
    Case {
        name: "group-condition",
        xml: "<Project>\n  <PropertyGroup Condition=\"'$(Configuration)' == 'Release'\">\n    <Out>optimised</Out>\n  </PropertyGroup>\n  <PropertyGroup Condition=\"'$(Configuration)' != 'Release'\">\n    <Out>plain</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "plain")],
        startup_moves: &[],
    },
    // A gate on the individual write.
    Case {
        name: "property-condition",
        xml: "<Project>\n  <PropertyGroup>\n    <Out Condition=\"'$(Platform)' == 'x64'\">wide</Out>\n    <Out Condition=\"'$(Platform)' != 'x64'\">narrow</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "narrow")],
        startup_moves: &[],
    },
    // `<Choose>`: the unselected arm is never walked, so a value can depend on a
    // global through a branch the property walk does not visit.
    Case {
        name: "choose",
        xml: "<Project>\n  <Choose>\n    <When Condition=\"'$(Platform)' == 'x64'\">\n      <PropertyGroup><Out>wide</Out></PropertyGroup>\n    </When>\n    <Otherwise>\n      <PropertyGroup><Out>narrow</Out></PropertyGroup>\n    </Otherwise>\n  </Choose>\n</Project>\n",
        files: &[],
        pins: &[("Out", "narrow")],
        startup_moves: &[],
    },
    // Nested arms, and a `When` whose selection depends on a *different* global
    // from the outer one.
    Case {
        name: "choose-nested",
        xml: "<Project>\n  <Choose>\n    <When Condition=\"'$(Configuration)' == 'Release'\">\n      <Choose>\n        <When Condition=\"'$(Platform)' == 'x64'\">\n          <PropertyGroup><Out>rel-x64</Out></PropertyGroup>\n        </When>\n        <Otherwise>\n          <PropertyGroup><Out>rel-other</Out></PropertyGroup>\n        </Otherwise>\n      </Choose>\n    </When>\n    <Otherwise>\n      <PropertyGroup><Out>dbg</Out></PropertyGroup>\n    </Otherwise>\n  </Choose>\n</Project>\n",
        files: &[],
        pins: &[("Out", "dbg")],
        startup_moves: &[],
    },
    // A `When` with no `Otherwise`, so with the arm unselected the later
    // default-write decides.
    Case {
        name: "choose-no-otherwise",
        xml: "<Project>\n  <Choose>\n    <When Condition=\"'$(Platform)' == 'x64'\">\n      <PropertyGroup><Out>wide</Out></PropertyGroup>\n    </When>\n  </Choose>\n  <PropertyGroup>\n    <Out Condition=\"'$(Out)' == ''\">narrow</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "narrow")],
        startup_moves: &[],
    },
    // A global outranks a document write of the same name. Committing
    // `FromDocument` here would be a wrong commit under every non-empty
    // `Configuration` global.
    Case {
        name: "global-beats-write",
        xml: "<Project>\n  <PropertyGroup>\n    <Configuration>FromDocument</Configuration>\n    <Out>$(Configuration)</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "Debug"), ("Configuration", "Debug")],
        startup_moves: &[],
    },
    // …unless the entry project opts out, which flips the answer.
    Case {
        name: "treat-as-local",
        xml: "<Project TreatAsLocalProperty=\"Configuration\">\n  <PropertyGroup>\n    <Configuration>FromDocument</Configuration>\n    <Out>$(Configuration)</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "FromDocument"), ("Configuration", "FromDocument")],
        startup_moves: &[],
    },
    // `TreatAsLocalProperty` on an *imported* root also opts the name out — the
    // unprotection is not confined to the entry project, so a write in the
    // imported file beats the global, and everything downstream of it reads the
    // imported value. Pinned, because it is the opposite of what this case was
    // first written to claim.
    Case {
        name: "treat-as-local-in-import",
        xml: "<Project>\n  <Import Project=\"local.props\" />\n  <PropertyGroup>\n    <Out>$(Configuration)</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[(
            "local.props",
            "<Project TreatAsLocalProperty=\"Configuration\">\n  <PropertyGroup><Configuration>FromImport</Configuration></PropertyGroup>\n</Project>\n",
        )],
        pins: &[("Out", "FromImport"), ("Configuration", "FromImport")],
        startup_moves: &[],
    },
    // A gated import: which *document* arrives depends on a global.
    Case {
        name: "import-condition",
        xml: "<Project>\n  <Import Project=\"rel.props\" Condition=\"'$(Configuration)' == 'Release'\" />\n  <PropertyGroup>\n    <Out Condition=\"'$(Out)' == ''\">default</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[("rel.props", IMPORT_SETS_OUT)],
        pins: &[("Out", "default")],
        startup_moves: &[],
    },
    // A *property-selected* import: the same, but through the `Project`
    // attribute's expansion rather than a `Condition`.
    Case {
        name: "import-selected-by-property",
        xml: "<Project>\n  <Import Project=\"$(Configuration).props\" Condition=\"Exists('$(Configuration).props')\" />\n  <PropertyGroup>\n    <Out Condition=\"'$(Out)' == ''\">none</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[
            (
                "Debug.props",
                "<Project><PropertyGroup><Out>debug-import</Out></PropertyGroup></Project>\n",
            ),
            (
                "Release.props",
                "<Project><PropertyGroup><Out>release-import</Out></PropertyGroup></Project>\n",
            ),
        ],
        pins: &[("Out", "debug-import")],
        startup_moves: &[],
    },
    // Laundered through a helper property, so the dependence is one hop away
    // from the read.
    Case {
        name: "indirect-helper",
        xml: "<Project>\n  <PropertyGroup>\n    <Helper>$(Configuration)-x</Helper>\n    <Out>[$(Helper)]</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "[Debug-x]"), ("Helper", "Debug-x")],
        startup_moves: &[],
    },
    // The dependence runs through a property *function* on the global, not a
    // comparison. The `!= ''` guard is load-bearing: a method call on an unset
    // property is an evaluation error, and this case is about the gate, not
    // about the reject branch (which `MSBuild rejects ⟹ we commit nothing`
    // covers wherever it does fire).
    Case {
        name: "condition-via-function",
        xml: "<Project>\n  <PropertyGroup>\n    <Out Condition=\"'$(Configuration)' != '' AND $(Configuration.StartsWith('Rel'))\">release-ish</Out>\n    <Out Condition=\"'$(Out)' == ''\">other</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "other")],
        startup_moves: &[],
    },
    // A global the entry document never names — only a file it imports does. So
    // "which globals can move this project's answers" is not readable off the
    // entry document's own `$(...)` references, which is exactly how the SDK's
    // props consume the caller-settable knobs.
    //
    // (MSBuild has no property-*name* indirection to test instead: `$($(Helper))`
    // is rejected outright with MSB4184, so an import is the real shape.)
    Case {
        name: "unmentioned-global",
        xml: "<Project>\n  <Import Project=\"probe.props\" />\n</Project>\n",
        files: &[(
            "probe.props",
            "<Project><PropertyGroup><Out>[$(BorzoiProbe)]</Out></PropertyGroup></Project>\n",
        )],
        pins: &[("Out", "[]")],
        startup_moves: &[],
    },
    // The startup directory gating a write, alone and beside a global. Only
    // `start-b` and `start-c` (through `start-link`) hold a `startup.props`.
    Case {
        name: "startup-gate",
        xml: "<Project>\n  <PropertyGroup>\n    <Out Condition=\"Exists('$(MSBuildStartupDirectory)/startup.props') and '$(Configuration)' == 'Release'\">beside-props-release</Out>\n    <Out Condition=\"'$(Out)' == '' and Exists('$(MSBuildStartupDirectory)/startup.props')\">beside-props</Out>\n    <Out Condition=\"'$(Out)' == ''\">elsewhere</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "elsewhere")],
        startup_moves: &["Out"],
    },
    // A `<Choose>` arm selected by the startup directory, through a property
    // function on it and through `Exists`, one arm reading a global.
    Case {
        name: "startup-choose",
        xml: "<Project>\n  <Choose>\n    <When Condition=\"$(MSBuildStartupDirectory.EndsWith('start-b'))\">\n      <PropertyGroup><Out>chose-b</Out></PropertyGroup>\n    </When>\n    <When Condition=\"Exists('$(MSBuildStartupDirectory)/startup.props')\">\n      <PropertyGroup><Out>chose-props-$(Platform)</Out></PropertyGroup>\n    </When>\n    <Otherwise>\n      <PropertyGroup><Out>chose-none</Out></PropertyGroup>\n    </Otherwise>\n  </Choose>\n</Project>\n",
        files: &[],
        pins: &[("Out", "chose-none")],
        startup_moves: &["Out"],
    },
    // An import whose path is built from the startup directory: which
    // document arrives depends on where MSBuild started. What it writes is
    // read directly.
    Case {
        name: "startup-selected-import",
        xml: "<Project>\n  <Import Project=\"$(MSBuildStartupDirectory)/startup.props\" Condition=\"Exists('$(MSBuildStartupDirectory)/startup.props')\" />\n  <PropertyGroup>\n    <Helper>[$(Out)]|$(Configuration)</Helper>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", ""), ("Helper", "[]|Debug")],
        startup_moves: &["Out", "Helper"],
    },
    // The same import, then the self-default idiom over the name it writes. A
    // served evaluation has no startup directory, so it cannot know whether
    // the import ran and the default with it: `Out`'s absence is no fact.
    Case {
        name: "startup-selected-self-default",
        xml: "<Project>\n  <Import Project=\"$(MSBuildStartupDirectory)/startup.props\" Condition=\"Exists('$(MSBuildStartupDirectory)/startup.props')\" />\n  <PropertyGroup>\n    <Out Condition=\"'$(Out)' == ''\">default</Out>\n    <Helper>[$(Out)]|$(Configuration)</Helper>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "default"), ("Helper", "[default]|Debug")],
        startup_moves: &["Out", "Helper"],
    },
    // The startup directory read directly, laundered through a helper beside a
    // global.
    Case {
        name: "startup-read",
        xml: "<Project>\n  <PropertyGroup>\n    <Helper>$(MSBuildStartupDirectory)</Helper>\n    <Out>[$(Helper)]-$(Configuration)</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[],
        startup_moves: &["Out", "Helper"],
    },
    // Toolset names a caller may set as globals: read directly, and steering
    // an import through `MSBuildUserExtensionsPath`, whose swept value holds a
    // `borzoi.props` ([`global_sets`]).
    Case {
        name: "toolset-global-read",
        xml: "<Project>\n  <PropertyGroup>\n    <Out>[$(MSBuildSDKsPath)]</Out>\n    <Helper>[$(MSBuildExtensionsPath)]</Helper>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[],
        startup_moves: &[],
    },
    // `MSBuildUserExtensionsPath` read into bodies. Unset, it is the host's
    // computed value, stored with the `\` of `Microsoft\MSBuild`, which
    // MSBuild's Unix path adjustment rewrites as each body reads it (its
    // first segment is a directory under the root); the `\x` the second body
    // adds is rewritten only with the whole value.
    Case {
        name: "toolset-user-extensions-read",
        xml: "<Project>\n  <PropertyGroup>\n    <Out>[$(MSBuildUserExtensionsPath)]</Out>\n    <Helper>$(MSBuildUserExtensionsPath)\\x</Helper>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[],
        startup_moves: &[],
    },
    Case {
        name: "toolset-global-import",
        xml: "<Project>\n  <Import Project=\"$(MSBuildUserExtensionsPath)/borzoi.props\" Condition=\"Exists('$(MSBuildUserExtensionsPath)/borzoi.props')\" />\n  <PropertyGroup>\n    <Out Condition=\"'$(Out)' == ''\">no-user-extension</Out>\n  </PropertyGroup>\n</Project>\n",
        files: &[],
        pins: &[("Out", "no-user-extension")],
        startup_moves: &[],
    },
];

/// What `start-b`'s and `start-c`'s `startup.props` write.
const STARTUP_PROPS: &[(&str, &str)] = &[
    (
        "start-b",
        "<Project><PropertyGroup><Out>from-start-b</Out></PropertyGroup></Project>\n",
    ),
    (
        "start-c",
        "<Project><PropertyGroup><Out>from-start-c</Out></PropertyGroup></Project>\n",
    ),
];

/// One directory MSBuild is started from, and the oracle child running there.
struct Startup {
    /// Names the directory in failure messages.
    label: &'static str,
    /// The child's working directory, and our side's `startup_directory`.
    /// `start-link` is a symlink, which both sides resolve.
    dir: PathBuf,
    oracle: Oracle,
}

/// The startup directories, under `root` (the canonical parent of every
/// case's directory), each with an oracle child started in it: `root` itself,
/// `start-b`, and `start-link`, a symlink to `start-c`. MSBuild fixes the
/// value once per process, so one child per directory serves the whole test.
fn startups(root: &Path) -> Vec<Startup> {
    for (name, contents) in STARTUP_PROPS {
        let dir = root.join(name);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("startup.props"), contents).unwrap();
    }
    let link = root.join("start-link");
    std::os::unix::fs::symlink(root.join("start-c"), &link).unwrap();
    [
        ("root", root.to_path_buf()),
        ("start-b", root.join("start-b")),
        ("start-link", link),
    ]
    .into_iter()
    .map(|(label, dir)| Startup {
        label,
        oracle: Oracle::spawn_in_dir(&dir),
        dir,
    })
    .collect()
}

/// A fresh, canonical root for one test's cases and startup directories:
/// MSBuild reports the physical directory it started in, so every path both
/// sides compare must be the physical one.
fn canonical_root(tmp: &TempDir) -> PathBuf {
    host_fs::canonicalize(tmp.path()).unwrap()
}

/// The `MSBuildUserExtensionsPath` [`global_sets`] supplies, holding a
/// `borzoi.props` that writes `Out`, and the `ImportBefore` file an SDK
/// project's `Microsoft.Common.props` imports from it.
fn write_user_extensions(root: &Path) {
    let dir = root.join("user-extensions");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("borzoi.props"),
        "<Project><PropertyGroup><Out>from-user-extensions</Out></PropertyGroup></Project>\n",
    )
    .unwrap();
    let before = dir.join("Current/Imports/Microsoft.Common.props/ImportBefore");
    std::fs::create_dir_all(&before).unwrap();
    std::fs::write(
        before.join("borzoi.props"),
        "<Project><PropertyGroup><SeenUserExtension>yes</SeenUserExtension></PropertyGroup></Project>\n",
    )
    .unwrap();
}

/// The global sets swept. Every set is a plausible caller: `dotnet build -c
/// Release`, an IDE's guess, a `-p:` override.
///
/// The empty set and the LSP's own injection are both present because the
/// difference between them is exactly the risk being measured — everything else
/// in this crate only ever evaluates the first.
///
/// `root` is the test's canonical root: the toolset sets name directories
/// under it.
fn global_sets(root: &Path) -> Vec<Vec<(String, String)>> {
    let g = |pairs: &[(&str, &str)]| -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
            .collect()
    };
    let under = |name: &str| root.join(name).to_str().unwrap().to_owned();
    vec![
        // No globals: the baseline every other harness in this crate uses.
        g(&[]),
        // What the LSP actually injects.
        g(&[("Configuration", "Debug"), ("Platform", "AnyCPU")]),
        // What the user may last have built.
        g(&[("Configuration", "Release"), ("Platform", "x64")]),
        // One axis at a time, so a case that depends on only one of them still
        // moves.
        g(&[("Configuration", "Release")]),
        g(&[("Platform", "x64")]),
        // An *empty* global. Distinct from "absent": it is still read-only, so a
        // `Condition="'$(X)' == ''"` default-write fires while the document's own
        // write of `X` is still suppressed.
        g(&[("Configuration", "")]),
        // A global the document does not mention.
        g(&[("BorzoiProbe", "probed")]),
        // An inner build. The LSP seeds this on every multi-targeted project
        // (`tfm_policy`, fsproj plan E1/E2), so it is not a hypothetical
        // perturbation but the evaluation a real user's `.fsproj` diagnostics
        // and defines come from — and it moves far more of the SDK chain than
        // `Configuration` does, because the whole TFM inference runs under it.
        g(&[
            ("Configuration", "Debug"),
            ("Platform", "AnyCPU"),
            ("TargetFramework", "net10.0"),
        ]),
        // Toolset names as globals, which `-p:` on a build sets over the
        // toolset's own values. `MSBuildSDKsPath` and `MSBuildExtensionsPath`
        // name directories that do not exist, so an SDK project's own imports
        // through them fail; `MSBuildUserExtensionsPath` names one holding an
        // `ImportBefore` file ([`write_user_extensions`]).
        vec![("MSBuildSDKsPath".to_owned(), under("no-sdks"))],
        vec![("MSBuildExtensionsPath".to_owned(), under("no-extensions"))],
        vec![(
            "MSBuildUserExtensionsPath".to_owned(),
            under("user-extensions"),
        )],
    ]
}

/// One point of the sweep: a document under one global set, evaluated by our
/// walk served (no startup directory) and supplied with each of the
/// [`startups`], and by MSBuild started from each — `None` where MSBuild
/// rejects the document, which the contract turns into "we must have committed
/// nothing".
struct Point {
    served: OurSide,
    /// Per startup directory, in [`startups`]'s order.
    supplied: Vec<OurSide>,
    /// Per startup directory, in [`startups`]'s order.
    theirs: Vec<Option<HashMap<String, String>>>,
}

/// Assert certain-implies-exact for one of our evaluations against one of
/// MSBuild's.
fn assert_exact(
    ours: &OurSide,
    theirs: Option<&HashMap<String, String>>,
    what: &str,
    globals: &[(String, String)],
    xml: &str,
) {
    let Some(theirs) = theirs else {
        assert!(
            ours.committed.is_empty(),
            "certain-implies-exact violated: MSBuild {what} rejects this project under \
             globals {globals:?}, but we committed {:?}\n--- xml ---\n{xml}",
            ours.committed
        );
        return;
    };
    for (name, our_value) in &ours.committed {
        let their_value = theirs
            .get(name)
            .expect("oracle answers for every requested name");
        assert_eq!(
            our_value, their_value,
            "certain-implies-exact violated for ${{{name}}} under globals {globals:?}, \
             MSBuild {what}: we evaluate it to {our_value:?}, MSBuild to \
             {their_value:?}\n--- xml ---\n{xml}"
        );
    }
}

/// Assert that every value MSBuild ends with is among the walk's candidates
/// for it (#1009), or that the walk says it may hold anything.
fn assert_among_candidates(
    reads: &EvaluationReads,
    theirs: Option<&HashMap<String, String>>,
    what: &str,
    globals: &[(String, String)],
    xml: &str,
) {
    // A value the walk commits is its only candidate, whatever MSBuild does,
    // unless the channel is withdrawn (#1041).
    for (name, candidates) in reads
        .candidates
        .iter()
        .filter(|_| !reads.candidates_withdrawn)
    {
        let committed = match &reads.properties[name] {
            PropertyRead::Value(value) => Some(value.clone()),
            PropertyRead::Unset => Some(String::new()),
            PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
        };
        // Past the channel's byte budget (4096 escaped bytes, which number
        // between one and three per decoded byte) it may keep none.
        if let Some(committed) = committed {
            let ok = match candidates {
                Some(candidates) => *candidates == BTreeSet::from([committed.clone()]),
                None => committed.len() * 3 > 4096,
            };
            assert!(
                ok,
                "{what}: we commit ${{{name}}} = {committed:?} under globals {globals:?}, so \
                 that is its only candidate, not {candidates:?}\n--- xml ---\n{xml}"
            );
        }
    }
    let Some(theirs) = theirs else {
        return;
    };
    for (name, candidates) in &reads.candidates {
        let Some(candidates) = candidates else {
            continue;
        };
        let their_value = theirs
            .get(name)
            .expect("oracle answers for every requested name");
        assert!(
            candidates.contains(their_value),
            "MSBuild {what} ends with ${{{name}}} = {their_value:?} under globals \
             {globals:?}, which is not among our candidates {candidates:?}\n--- xml ---\n{xml}"
        );
    }
}

/// Evaluate `dir/Demo.fsproj` under `globals`, both sides, in every mode, and
/// assert the contract at each pairing.
fn evaluate_both(
    startups: &mut [Startup],
    dir: &Path,
    xml: &str,
    globals: &[(String, String)],
    read_names: &[&str],
    with_sdk: bool,
) -> Point {
    let project_path = dir.join("Demo.fsproj");
    let extra: HashMap<String, String> = globals.iter().cloned().collect();

    let dotnet_root = with_sdk.then(common::dotnet_root_from_env);
    let workload = with_sdk.then(common::workload_env_from_process);
    let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
        let (user_dotnet_root, overrides_present) =
            workload.as_ref().expect("only called when with_sdk");
        resolve_sdk(
            dotnet_root.as_ref().expect("only called when with_sdk"),
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: user_dotnet_root.as_deref(),
                overrides_present: *overrides_present,
                // The fixture tempdir has no global.json above it.
                global_json: Default::default(),
                process_architecture: None,
            },
            observer,
        )
    };
    let sdk_resolver = with_sdk.then_some(&resolver as &borzoi_msbuild::SdkResolver<'_>);

    // `parse_fsproj_with_imports` rather than `parse_fsproj`: it is the entry
    // point the LSP itself calls, and half the routes above run through an
    // `<Import>`.
    let served = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project_path, xml)
            .expect("a project path spelt as its full path"),
        &extra,
        &common::oracle_environment(),
        sdk_resolver,
        None,
    )
    .expect("well-formed XML parses");
    let served = our_side(&served, read_names);

    let names: Vec<String> = read_names.iter().map(|n| (*n).to_string()).collect();
    let mut supplied = Vec::new();
    let mut theirs = Vec::new();
    for startup in startups.iter_mut() {
        let (parsed, reads) = parse_fsproj_reads(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, xml)
                .expect("a project path spelt as its full path"),
            &extra,
            &common::oracle_environment(),
            sdk_resolver,
            None,
            Some(&startup.dir),
            &ReadProbe {
                properties: names.clone(),
                ..ReadProbe::default()
            },
        )
        .expect("well-formed XML parses");
        let ours = our_side(&parsed, read_names);
        let answer = startup
            .oracle
            .project(xml, &names, Some(&project_path), globals);
        let what = format!("started in {}", startup.label);
        assert_among_candidates(&reads, answer.as_ref(), &what, globals, xml);
        assert_exact(
            &served,
            answer.as_ref(),
            &format!("{what} (ours served, with no startup directory)"),
            globals,
            xml,
        );
        assert_exact(
            &ours,
            answer.as_ref(),
            &format!("{what} (ours supplied with it)"),
            globals,
            xml,
        );
        supplied.push(ours);
        theirs.push(answer);
    }
    Point {
        served,
        supplied,
        theirs,
    }
}

/// Our side of one evaluation, per read-back name.
///
/// Per name, as in `fsproj_property_table_diff`: an untrusted provenance
/// withdraws that name's claim without withdrawing its neighbours'.
fn our_side(parsed: &ParsedProject, read_names: &[&str]) -> OurSide {
    let mut ours = OurSide::default();
    for name in read_names {
        match parsed.properties.get(*name) {
            None => {
                ours.absent.insert((*name).to_string());
            }
            Some(_) if parsed.property(name).untrusted_cause().is_some() => {
                ours.untrusted.insert((*name).to_string());
            }
            Some(value) => {
                ours.committed.insert((*name).to_string(), value.clone());
            }
        }
    }
    ours
}

/// One evaluation's outcome on our side, split three ways.
///
/// The split matters to the census, not to soundness: `untrusted` and `absent`
/// both make no claim, but they are different states of knowledge. "The walker
/// evaluated this name and marked the result untrustworthy" is a modelled
/// decline; "the name is not in the table at all" means the walk never reached
/// the write. Reporting them as one number would read as more discipline than
/// the evaluator actually exercises.
#[derive(Default)]
struct OurSide {
    committed: BTreeMap<String, String>,
    untrusted: BTreeSet<String>,
    absent: BTreeSet<String>,
}

/// What one case did across the whole sweep, for the census.
///
/// There is deliberately no "frozen" row — a name we committed the *same* value
/// for under two global sets that MSBuild disagreed about. That is the defect
/// this file exists to catch, and it cannot reach the census: the per-set
/// exactness assertion in [`evaluate_both`] fires on the second set first.
#[derive(Default)]
struct CaseCensus {
    /// `(name, globals index)` pairs we committed a value for, served.
    committed: usize,
    /// Global sets under which MSBuild, started in the first startup
    /// directory, evaluates the document rather than rejecting it.
    evaluated_sets: usize,
    /// The global names of each set it rejects the document under.
    rejected_under: Vec<String>,
    /// Per name: how many global sets we committed under, and how many distinct
    /// values each side produced across the sweep.
    by_name: BTreeMap<String, NameCensus>,
}

/// One name's behaviour across the sweep.
///
/// The global-axis fields compare our served evaluation with MSBuild started
/// in the first startup directory; the `startup_` fields hold the global set
/// fixed and vary the startup directory.
struct NameCensus {
    /// Global sets we committed a value under, of [`global_sets`]'s length.
    committed_sets: usize,
    /// Global sets where the name was in our table but its provenance was
    /// untrusted — a modelled decline.
    untrusted_sets: usize,
    /// Global sets where the name never entered our table at all. Distinguished
    /// from `untrusted_sets` because they are different states of knowledge; see
    /// [`OurSide`].
    absent_sets: usize,
    /// Distinct values we committed. `0` when we never committed; `1` means we
    /// answered the same thing every time we answered at all.
    our_values: usize,
    /// Distinct values MSBuild produced. `>= 2` is what "this name depends on a
    /// caller-supplied global" means, stated by the reference rather than by us.
    their_values: usize,
    /// Global sets under which MSBuild's value moves between the startup
    /// directories: the `(name, globals)` points that depend on the startup
    /// directory.
    startup_moving_sets: usize,
    /// Of those, the sets where our supplied evaluations committed two or more
    /// distinct values: tracked, so the exactness check was exercised on the
    /// startup axis.
    startup_tracked_sets: usize,
    /// Of those, the sets where our served evaluation held the name untrusted.
    startup_served_untrusted_sets: usize,
    /// Of those, the sets where our served evaluation never reached the name.
    /// With `startup_served_untrusted_sets` it covers every moving set: a
    /// served commit there fails [`evaluate_both`]'s exactness check against
    /// one of the directories.
    startup_served_absent_sets: usize,
}

/// The property names some global set in [`global_sets`] assigns.
///
/// These move across the sweep **by construction** — they are the input being
/// varied. Counting them as evidence that a document derives anything from a
/// global is circular, so every anti-vacuity floor here is computed over the
/// complement. (Left in the census's *report*, though: whether a document write
/// of one of these names wins is precisely the `TreatAsLocalProperty` question.)
fn swept_global_names() -> BTreeSet<String> {
    global_sets(Path::new("/"))
        .into_iter()
        .flatten()
        .map(|(name, _)| name)
        .collect()
}

/// The startup axis's census, summed over cases.
#[derive(Default, Debug)]
struct StartupCensus {
    /// `(case, name, globals)` points where the startup directory moves
    /// MSBuild's value.
    moving: usize,
    /// Of those, the points our supplied evaluations track.
    tracked: usize,
    /// Of those, the points our served evaluation declines as untrusted.
    served_untrusted: usize,
    /// Of those, the points our served evaluation never reaches.
    served_absent: usize,
}

impl StartupCensus {
    fn add(&mut self, case: &CaseCensus) {
        for c in case.by_name.values() {
            self.moving += c.startup_moving_sets;
            self.tracked += c.startup_tracked_sets;
            self.served_untrusted += c.startup_served_untrusted_sets;
            self.served_absent += c.startup_served_absent_sets;
        }
    }

    fn report(&self, what: &str) {
        eprintln!(
            "{what}, startup axis: {} (case, name, globals) points move between the {} \
             startup directories; supplied, we track {} and decline {}; served, we \
             decline all of them ({} untrusted, {} never reached)",
            self.moving,
            STARTUP_DIRECTORIES,
            self.tracked,
            self.moving - self.tracked,
            self.served_untrusted,
            self.served_absent,
        );
        assert_eq!(
            self.served_untrusted + self.served_absent,
            self.moving,
            "a served commit of a startup-dependent value passed the exactness check"
        );
    }
}

/// How many directories [`startups`] lays out.
const STARTUP_DIRECTORIES: usize = 3;

/// The startup-axis floors: points the supplied mode must track in the corner
/// list and in the generated sweep.
const STARTUP_TRACKED_FLOOR_ROUTES: usize = 60;
const STARTUP_TRACKED_FLOOR_SWEEP: usize = 250;

impl CaseCensus {
    /// Names MSBuild moves across the global sweep — the global-dependent ones.
    fn moving_in_msbuild(&self) -> impl Iterator<Item = (&String, &NameCensus)> {
        self.by_name.iter().filter(|(_, c)| c.their_values >= 2)
    }

    /// [`Self::moving_in_msbuild`] minus the swept inputs themselves: names the
    /// *document* derives from a global. The floors are on these.
    fn derived_moving(&self) -> usize {
        let swept = swept_global_names();
        self.moving_in_msbuild()
            .filter(|(name, _)| !swept.contains(*name))
            .count()
    }

    /// [`Self::tracked`] minus the swept inputs themselves.
    fn derived_tracked(&self) -> usize {
        let swept = swept_global_names();
        self.tracked().filter(|name| !swept.contains(*name)).count()
    }

    /// Moving names we committed at least two distinct values for: we tracked
    /// the dependence rather than declining. This is the number the anti-vacuity
    /// floors are on — a moving name we never commit exercises nothing, whereas
    /// one we commit two different values for is a name where the exactness
    /// assertion was genuinely tested against the global axis.
    fn tracked(&self) -> impl Iterator<Item = &String> {
        self.moving_in_msbuild()
            .filter(|(_, c)| c.our_values >= 2)
            .map(|(name, _)| name)
    }

    /// The rest: sound (nothing wrong was published), but the dependence cost us
    /// a value. This is the number that says what a "depends on a caller-supplied
    /// global" provenance dimension would buy.
    ///
    /// Over the **derived** domain, like its two siblings. Counting the swept
    /// names here would inflate it with something that is not a decline at all: a
    /// caller global is deliberately absent from `ParsedProject::properties`
    /// unless the document writes it, so `Configuration` and `Platform` would
    /// read as declined in almost every case and the census would report more
    /// pairs declined than moving.
    fn declined(&self) -> usize {
        self.derived_moving() - self.derived_tracked()
    }

    /// One entry per name that depends on a global or on the startup
    /// directory, for the report: how many distinct values MSBuild produced
    /// across the global sweep, and what we did — committed (with how many
    /// distinct values, over how many global sets), declined as untrusted, or
    /// never reached at all — and, where the startup directory moves it, in how
    /// many global sets it does, how many of those our supplied evaluations
    /// track, and how our served one declines it.
    fn render(&self) -> String {
        self.by_name
            .iter()
            .filter(|(_, c)| c.their_values >= 2 || c.startup_moving_sets > 0)
            .map(|(name, c)| {
                let mut entry = format!(
                    "{name}(theirs {}; ours {} val in {} set, {} untrusted, {} absent",
                    c.their_values, c.our_values, c.committed_sets, c.untrusted_sets, c.absent_sets
                );
                if c.startup_moving_sets > 0 {
                    entry.push_str(&format!(
                        "; startup moves it in {} set, supplied tracks {}, served {} \
                         untrusted {} absent",
                        c.startup_moving_sets,
                        c.startup_tracked_sets,
                        c.startup_served_untrusted_sets,
                        c.startup_served_absent_sets
                    ));
                }
                entry.push(')');
                entry
            })
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// Run one case over the whole global sweep and every startup directory,
/// asserting the contract at every point and returning its census row.
#[allow(clippy::too_many_arguments)]
fn sweep_case(
    startups: &mut [Startup],
    root: &Path,
    dir: &Path,
    xml: &str,
    read_names: &[&str],
    pins: &[(&str, &str)],
    startup_moves: &[&str],
    with_sdk: bool,
) -> CaseCensus {
    let project_path = dir.join("Demo.fsproj");
    std::fs::write(&project_path, xml).expect("write project");

    let sets = global_sets(root);
    let points: Vec<Point> = sets
        .iter()
        .map(|globals| evaluate_both(startups, dir, xml, globals, read_names, with_sdk))
        .collect();

    // The case's own claims about what it demonstrates, checked against MSBuild
    // under the globals the LSP injects. `PIN_GLOBALS` is one of the swept sets,
    // so this costs no extra evaluation — it reads the answers already collected.
    let pin_index = sets
        .iter()
        .position(|set| {
            set.iter()
                .map(|(k, v)| (k.as_str(), v.as_str()))
                .eq(PIN_GLOBALS.iter().copied())
        })
        .expect("PIN_GLOBALS is one of the swept global sets");
    let pinned = &points[pin_index];
    if !pins.is_empty() {
        let theirs = pinned.theirs[0]
            .as_ref()
            .expect("MSBuild evaluates a pinned case under the LSP's own globals");
        for (name, want) in pins {
            assert_eq!(
                theirs.get(*name).map(String::as_str),
                Some(*want),
                "the pinned MSBuild value for ${{{name}}} under {PIN_GLOBALS:?}, started in \
                 {}, is wrong — this case does not demonstrate the route its comment \
                 claims\n--- xml ---\n{xml}",
                startups[0].label
            );
        }
    }
    for name in startup_moves {
        let seen: BTreeSet<Option<&String>> = pinned
            .theirs
            .iter()
            .map(|t| {
                t.as_ref()
                    .expect("MSBuild evaluates a startup-routed case from every directory")
                    .get(*name)
            })
            .collect();
        assert!(
            seen.len() >= 2,
            "MSBuild reads ${{{name}}} the same from every startup directory under \
             {PIN_GLOBALS:?} — this case does not take the route from the startup \
             directory its comment claims\n--- xml ---\n{xml}"
        );
    }

    let mut census = CaseCensus::default();
    for (globals, point) in sets.iter().zip(&points) {
        census.committed += point.served.committed.len();
        if point.theirs[0].is_some() {
            census.evaluated_sets += 1;
        } else {
            let names: Vec<&str> = globals.iter().map(|(name, _)| name.as_str()).collect();
            census
                .rejected_under
                .push(format!("{{{}}}", names.join(",")));
        }
    }
    for name in read_names {
        let their_values: BTreeSet<&String> = points
            .iter()
            .filter_map(|p| p.theirs[0].as_ref())
            .filter_map(|t| t.get(*name))
            .collect();
        let our_values: BTreeSet<&String> = points
            .iter()
            .filter_map(|p| p.served.committed.get(*name))
            .collect();
        let mut startup = (0, 0, 0, 0);
        for point in &points {
            let across: BTreeSet<&String> = point
                .theirs
                .iter()
                .flatten()
                .filter_map(|t| t.get(*name))
                .collect();
            if across.len() < 2 {
                continue;
            }
            startup.0 += 1;
            let ours: BTreeSet<&String> = point
                .supplied
                .iter()
                .filter_map(|o| o.committed.get(*name))
                .collect();
            startup.1 += usize::from(ours.len() >= 2);
            startup.2 += usize::from(point.served.untrusted.contains(*name));
            startup.3 += usize::from(point.served.absent.contains(*name));
        }
        census.by_name.insert(
            (*name).to_string(),
            NameCensus {
                committed_sets: points
                    .iter()
                    .filter(|p| p.served.committed.contains_key(*name))
                    .count(),
                untrusted_sets: points
                    .iter()
                    .filter(|p| p.served.untrusted.contains(*name))
                    .count(),
                absent_sets: points
                    .iter()
                    .filter(|p| p.served.absent.contains(*name))
                    .count(),
                our_values: our_values.len(),
                their_values: their_values.len(),
                startup_moving_sets: startup.0,
                startup_tracked_sets: startup.1,
                startup_served_untrusted_sets: startup.2,
                startup_served_absent_sets: startup.3,
            },
        );
    }
    census
}

/// The hand-written route list: every way a global was found to reach a
/// committed value while the output-directory work was being attempted, and
/// the routes from the startup directory.
#[test]
fn every_route_from_a_global_is_exact_or_declined() {
    let tmp = TempDir::new().unwrap();
    let root = canonical_root(&tmp);
    write_user_extensions(&root);
    let mut startups = startups(&root);

    let mut committed = 0usize;
    let mut moving = 0usize;
    let mut tracked = 0usize;
    let mut declined = 0usize;
    let mut startup = StartupCensus::default();
    for case in CASES {
        let dir = root.join(case.name);
        std::fs::create_dir_all(&dir).unwrap();
        for (name, contents) in case.files {
            std::fs::write(dir.join(name), contents).unwrap();
        }
        let census = sweep_case(
            &mut startups,
            &root,
            &dir,
            case.xml,
            READ_NAMES,
            case.pins,
            case.startup_moves,
            false,
        );
        eprintln!(
            "  {:<28} committed {:>3}, MSBuild rejects under [{}]  {}",
            case.name,
            census.committed,
            census.rejected_under.join(" "),
            census.render()
        );
        // A body reading the host's `MSBuildUserExtensionsPath` is decided
        // under every global set: the adjustment its `\` meets probes a
        // directory under the root.
        if case.name == "toolset-user-extensions-read" {
            for name in ["Out", "Helper"] {
                let committed_sets = census.by_name.get(name).map_or(0, |n| n.committed_sets);
                assert_eq!(
                    committed_sets, census.evaluated_sets,
                    "{}: `{name}` committed under only {committed_sets} of the {} global sets \
                     MSBuild evaluates it under",
                    case.name, census.evaluated_sets
                );
            }
        }
        committed += census.committed;
        moving += census.derived_moving();
        tracked += census.derived_tracked();
        declined += census.declined();
        startup.add(&census);
    }

    eprintln!(
        "global-perturbation routes: {} cases × {} global sets — {committed} committed \
         (name, globals) pairs; {moving} (case, name) pairs move in MSBuild, of which \
         we track {tracked} and decline {declined}",
        CASES.len(),
        global_sets(&root).len(),
    );
    startup.report("global-perturbation routes");

    // Anti-vacuity. A harness that declined everything would satisfy the
    // one-sided contract while measuring nothing, and so would one whose globals
    // never changed an answer.
    assert!(
        committed >= 100,
        "too few committed (name, globals) pairs ({committed}) — the walker may \
         have started declining everything, which passes vacuously"
    );
    // The floor that matters is on `tracked`, not on `moving`: a name MSBuild
    // moves but we never commit exercises nothing, whereas one we commit *two
    // different values* for is a name where the exactness assertion above was
    // genuinely tested against the global axis. `moving` alone would stay
    // satisfied by a walker that declined every one of them.
    assert!(
        tracked >= 10,
        "only {tracked} (case, name) pairs were both committed and global-dependent \
         — the exactness check is no longer being exercised on the global axis, so \
         this harness is passing vacuously"
    );
    // The same floor on the startup axis: points where the supplied directory
    // was committed under two or more distinct values.
    assert!(
        startup.tracked >= STARTUP_TRACKED_FLOOR_ROUTES,
        "only {} (case, name, globals) points were both committed and \
         startup-dependent — the exactness check is no longer being exercised on \
         the startup axis",
        startup.tracked
    );
}

/// The item side. The Compile order is what the semantic layer folds over, so a
/// global-gated `<Compile>` is a route from an editor-guessed global straight
/// into which files exist as far as the LSP is concerned, and a gate on the
/// startup directory is one from where the process started.
#[test]
fn compile_items_are_exact_or_declined_under_every_global_set() {
    let tmp = TempDir::new().unwrap();
    let root = canonical_root(&tmp);
    write_user_extensions(&root);
    let mut startups = startups(&root);

    // Literal includes only — globbing is a separate seam with its own
    // differential, and a resolver is not wired here.
    let documents: &[(&str, &str)] = &[
        (
            "item-condition",
            "<Project>\n  <ItemGroup>\n    <Compile Include=\"Always.fs\" />\n    <Compile Include=\"DebugOnly.fs\" Condition=\"'$(Configuration)' == 'Debug'\" />\n  </ItemGroup>\n</Project>\n",
        ),
        (
            "group-condition",
            "<Project>\n  <ItemGroup Condition=\"'$(Platform)' == 'x64'\">\n    <Compile Include=\"Wide.fs\" />\n  </ItemGroup>\n  <ItemGroup>\n    <Compile Include=\"Always.fs\" />\n  </ItemGroup>\n</Project>\n",
        ),
        (
            "include-interpolates-global",
            "<Project>\n  <ItemGroup>\n    <Compile Include=\"$(Configuration).fs\" />\n    <Compile Include=\"Always.fs\" />\n  </ItemGroup>\n</Project>\n",
        ),
        (
            "remove-gated-on-global",
            "<Project>\n  <ItemGroup>\n    <Compile Include=\"Always.fs\" />\n    <Compile Include=\"DebugOnly.fs\" />\n    <Compile Remove=\"DebugOnly.fs\" Condition=\"'$(Configuration)' == 'Release'\" />\n  </ItemGroup>\n</Project>\n",
        ),
        (
            "startup-gated",
            "<Project>\n  <ItemGroup>\n    <Compile Include=\"Started.fs\" Condition=\"Exists('$(MSBuildStartupDirectory)/startup.props')\" />\n    <Compile Include=\"Always.fs\" />\n    <Compile Include=\"ReleaseOnly.fs\" Condition=\"'$(Configuration)' == 'Release'\" />\n  </ItemGroup>\n</Project>\n",
        ),
    ];
    /// The documents whose Compile order must move between the startup
    /// directories.
    const STARTUP_ROUTED: &[&str] = &["startup-gated"];

    // The walker yields each include joined onto the project's directory and
    // MSBuild its `FullPath`, so compare the file names they resolve to.
    let file_names = |paths: &mut dyn Iterator<Item = &Path>| -> Vec<String> {
        paths
            .map(|p| {
                p.file_name()
                    .expect("an item resolves to a file name")
                    .to_string_lossy()
                    .into_owned()
            })
            .collect()
    };
    // `None` when a diagnostic or an uncertain item set withdraws the claim.
    let ours = |parsed: &ParsedProject| -> Option<Vec<String>> {
        (parsed.diagnostics.is_empty() && !parsed.items_uncertain)
            .then(|| file_names(&mut parsed.items.iter().map(|i| i.include.as_path())))
    };

    let sets = global_sets(&root);
    let mut committed = 0usize;
    let mut moving = 0usize;
    let mut startup_moving = 0usize;
    let mut startup_tracked = 0usize;
    for (name, xml) in documents {
        let dir = root.join(name);
        std::fs::create_dir_all(&dir).unwrap();
        let project_path = dir.join("Demo.fsproj");
        std::fs::write(&project_path, xml).unwrap();

        let mut theirs_by_set: BTreeSet<Vec<String>> = BTreeSet::new();
        let mut moves_with_startup = false;
        for globals in &sets {
            let extra: HashMap<String, String> = globals.iter().cloned().collect();
            let parsed = parse_fsproj_with_imports(
                &borzoi_msbuild::ProjectFile::buffer(&project_path, *xml)
                    .expect("a project path spelt as its full path"),
                &extra,
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed XML parses");
            let served = ours(&parsed);
            committed += usize::from(served.is_some());

            let mut theirs_by_startup: BTreeSet<Vec<String>> = BTreeSet::new();
            let mut supplied_by_startup: BTreeSet<Vec<String>> = BTreeSet::new();
            for (index, startup) in startups.iter_mut().enumerate() {
                let theirs = file_names(
                    &mut startup
                        .oracle
                        .items(xml, &project_path, "Compile", globals)
                        .expect("MSBuild evaluates these documents")
                        .iter()
                        .map(Path::new),
                );
                if index == 0 {
                    theirs_by_set.insert(theirs.clone());
                }
                theirs_by_startup.insert(theirs.clone());
                if let Some(served) = &served {
                    assert_eq!(
                        served, &theirs,
                        "certain-implies-exact violated for the Compile order under globals \
                         {globals:?}, served with no startup directory, against MSBuild \
                         started in {}\n--- xml ---\n{xml}",
                        startup.label
                    );
                }
                let (parsed, _) = parse_fsproj_reads(
                    &borzoi_msbuild::ProjectFile::buffer(&project_path, *xml)
                        .expect("a project path spelt as its full path"),
                    &extra,
                    &common::oracle_environment(),
                    None,
                    None,
                    Some(&startup.dir),
                    &ReadProbe::default(),
                )
                .expect("well-formed XML parses");
                if let Some(supplied) = ours(&parsed) {
                    assert_eq!(
                        supplied, theirs,
                        "certain-implies-exact violated for the Compile order under globals \
                         {globals:?}, started in {}\n--- xml ---\n{xml}",
                        startup.label
                    );
                    supplied_by_startup.insert(supplied);
                }
            }
            if theirs_by_startup.len() >= 2 {
                moves_with_startup = true;
                startup_moving += 1;
                startup_tracked += usize::from(supplied_by_startup.len() >= 2);
            }
        }
        eprintln!(
            "  {name:<28} MSBuild produces {} distinct Compile orders across {} global sets{}",
            theirs_by_set.len(),
            sets.len(),
            if moves_with_startup {
                ", and moves it between the startup directories"
            } else {
                ""
            }
        );
        if theirs_by_set.len() >= 2 {
            moving += 1;
        }
        assert_eq!(
            moves_with_startup,
            STARTUP_ROUTED.contains(name),
            "{name}: whether MSBuild's Compile order moves between the startup \
             directories is not what the document is written for"
        );
    }

    eprintln!(
        "global-perturbation items: {committed} committed (document, globals) pairs; \
         {moving} of {} documents change Compile order across the sweep; the startup \
         directory moves it at {startup_moving} (document, globals) points, of which \
         we track {startup_tracked} with a directory supplied",
        documents.len()
    );
    assert!(
        committed >= 10,
        "too few committed (document, globals) pairs ({committed})"
    );
    assert_eq!(
        moving,
        documents.len(),
        "every item document here is written to depend on a global, so all of them \
         must move across the sweep — if one stopped, it is no longer testing the \
         axis"
    );
    assert_eq!(
        startup_tracked, startup_moving,
        "a Compile order the startup directory moves was declined with the directory \
         supplied"
    );
}

/// Fixed-seed sweep over generated documents that compose the routes above:
/// several gated writes, reading each other, with the gates drawn from a pool of
/// global-dependent and global-independent conditions.
///
/// The corner list pins the routes someone already thought of. This is the part
/// that can find one nobody did — which is the whole reason the design note asks
/// for a machine here rather than another review round.
#[test]
fn fixed_seed_composed_documents_are_exact_or_declined() {
    let tmp = TempDir::new().unwrap();
    let root = canonical_root(&tmp);
    write_user_extensions(&root);
    let mut startups = startups(&root);
    let mut rng = SplitMix64(0x91ba_10c0_ffee);
    // The startup and toolset draws come from their own stream, and only for
    // the documents after the first `CASES_N`, so the global population is
    // the same with them as without.
    let mut startup_rng = SplitMix64(0x57a7_0d1c);
    // The imports likewise, so the gates and bodies are the same with them as
    // without.
    let mut import_rng = SplitMix64(0x1a0b_e988);

    // Gates: some depend on a global, some do not, so a generated document may
    // be genuinely invariant — a sweep of only-dependent documents would never
    // exercise the "we correctly committed the same value" path.
    const GATES: &[&str] = &[
        "",
        "'$(Configuration)' == 'Release'",
        "'$(Configuration)' != 'Release'",
        "'$(Platform)' == 'x64'",
        "'$(Configuration)' == ''",
        "'$(Out)' == ''",
        "'$(Helper)' != ''",
        "'x' == 'x'",
        "Exists('rel.props')",
        "'$(Configuration)$(Platform)' == 'Releasex64'",
    ];
    const BODIES: &[&str] = &[
        "literal",
        "$(Configuration)",
        "$(Platform)",
        "$(Configuration)/$(Platform)",
        "$(Helper)",
        "[$(Out)]",
        "$(BorzoiProbe)",
        "$(Configuration.Length)",
    ];
    // Gates and bodies on the startup directory and the toolset names a global
    // set supplies, which a document of the second population draws in place
    // of a write's own gate half the time and its body a third of it.
    // `MSBuildUserExtensionsPath` unset is the host's value, whose `\`
    // MSBuild's Unix path adjustment rewrites when a body reads it.
    const STARTUP_GATES: &[&str] = &[
        "Exists('$(MSBuildStartupDirectory)/startup.props')",
        "!Exists('$(MSBuildStartupDirectory)/startup.props')",
        "$(MSBuildStartupDirectory.EndsWith('start-b'))",
        "Exists('$(MSBuildStartupDirectory)/startup.props') and '$(Configuration)' == 'Release'",
        "Exists('$(MSBuildUserExtensionsPath)/borzoi.props')",
    ];
    const STARTUP_BODIES: &[&str] = &[
        "$(MSBuildStartupDirectory)",
        "$(MSBuildStartupDirectory)|$(Platform)",
        "[$(MSBuildExtensionsPath)]",
        "[$(MSBuildUserExtensionsPath)]",
    ];
    const WRITTEN: &[&str] = &["Out", "Helper", "Configuration", "Platform"];
    // An import a document of the second population draws before its writes,
    // selected by the startup directory or by a toolset name a global set
    // supplies. Each writes `Out` where it exists, so a later write's
    // `'$(Out)' == ''` gate is the self-default idiom after an import a served
    // evaluation cannot decide.
    const IMPORTS: &[&str] = &[
        "",
        "  <Import Project=\"$(MSBuildStartupDirectory)/startup.props\" Condition=\"Exists('$(MSBuildStartupDirectory)/startup.props')\" />\n",
        "  <Import Project=\"$(MSBuildUserExtensionsPath)/borzoi.props\" Condition=\"Exists('$(MSBuildUserExtensionsPath)/borzoi.props')\" />\n",
    ];

    /// Documents of the global grammar alone.
    const CASES_N: usize = 250;
    /// Documents after them that mix in the startup and toolset draws.
    const STARTUP_CASES_N: usize = 150;
    let mut committed = 0usize;
    let mut moving = 0usize;
    let mut tracked = 0usize;
    let mut startup = StartupCensus::default();
    for case in 0..CASES_N + STARTUP_CASES_N {
        let mixed = case >= CASES_N;
        let writes = 1 + rng.below(4);
        let mut xml = String::from("<Project>\n");
        if mixed {
            xml.push_str(import_rng.pick(IMPORTS));
        }
        xml.push_str("  <PropertyGroup>\n");
        for _ in 0..writes {
            let name = rng.pick(WRITTEN);
            let mut gate = *rng.pick(GATES);
            let mut body = *rng.pick(BODIES);
            if mixed && startup_rng.below(2) == 0 {
                gate = *startup_rng.pick(STARTUP_GATES);
            }
            if mixed && startup_rng.below(3) == 0 {
                body = *startup_rng.pick(STARTUP_BODIES);
            }
            if gate.is_empty() {
                xml.push_str(&format!("    <{name}>{body}</{name}>\n"));
            } else {
                // `&` first, or the ampersand of a just-inserted `&lt;` would be
                // escaped again.
                let gate = gate.replace('&', "&amp;").replace('<', "&lt;");
                xml.push_str(&format!(
                    "    <{name} Condition=\"{gate}\">{body}</{name}>\n"
                ));
            }
        }
        xml.push_str("  </PropertyGroup>\n</Project>\n");

        let dir = root.join(format!("case{case}"));
        std::fs::create_dir_all(&dir).unwrap();
        // Some gates probe for it; half the cases have it, so `Exists(...)`
        // splits the population rather than being constant.
        if case % 2 == 0 {
            std::fs::write(dir.join("rel.props"), IMPORT_SETS_OUT).unwrap();
        }

        let census = sweep_case(
            &mut startups,
            &root,
            &dir,
            &xml,
            READ_NAMES,
            &[],
            &[],
            false,
        );
        committed += census.committed;
        moving += census.derived_moving();
        tracked += census.derived_tracked();
        startup.add(&census);
    }

    eprintln!(
        "global-perturbation sweep: {} generated documents × {} global sets — \
         {committed} committed (name, globals) pairs, {moving} (case, name) pairs \
         move in MSBuild, of which we track {tracked}",
        CASES_N + STARTUP_CASES_N,
        global_sets(&root).len()
    );
    startup.report("global-perturbation sweep");
    assert!(
        committed >= 1000,
        "too few committed (name, globals) pairs ({committed}) over {} documents",
        CASES_N + STARTUP_CASES_N
    );
    assert!(
        tracked >= 100,
        "only {tracked} generated (case, name) pairs were both committed and \
         global-dependent — the generator has drifted away from the axis this sweep \
         exists to test"
    );
    assert!(
        startup.tracked >= STARTUP_TRACKED_FLOOR_SWEEP,
        "only {} generated (case, name, globals) points were both committed and \
         startup-dependent — the generator has drifted away from the startup axis",
        startup.tracked
    );
}

/// Unset-property reads in import gates (#824), every combination of:
///
/// - the name read: `TargetFramework`, and `BorzoiProbe`, which no document
///   writes. A [`global_sets`] entry supplies each (the inner build and the
///   probe), and the rest leave it unset;
/// - the gate: the name empty, non-empty, equal to its global's value, or a
///   derived property written under `'$(Plural)' != '' and '$(N)' == ''` (the
///   shape of `IsCrossTargetingBuild`);
/// - a later document write of the name, after the import, or none;
/// - earlier content the walk cannot see: none, a hidden import that writes
///   the name, or a hidden import that writes nothing.
///
/// Every read is graded, an unset one included: a trusted value must be
/// MSBuild's, and an exact `Unset` must be MSBuild's empty. A document with no
/// hidden content must commit `Out` under every global set: an unset name read
/// before any write is MSBuild's empty, which the walk can know.
///
/// After hidden content the gate is undecided: the walk follows the import on
/// one side, and what the followed file writes is a write MSBuild may not
/// make, so the walk must decline it.
#[test]
fn unset_reads_in_import_gates_are_exact_or_declined() {
    use borzoi_msbuild::PropertyRead;

    const NAMES: &[(&str, &str)] = &[("TargetFramework", "net10.0"), ("BorzoiProbe", "probed")];
    const GATES: &[&str] = &["empty", "nonempty", "equals", "derived"];
    const HIDDEN: &[&str] = &["none", "writes", "silent"];
    const READ: &[&str] = &["Out", "Derived"];

    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let sets = global_sets(tmp.path());
    let mut must_commit_misses = Vec::new();
    let mut census: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut case = 0usize;
    for (name, value) in NAMES {
        for gate in GATES {
            for late in [false, true] {
                for hidden in HIDDEN {
                    case += 1;
                    let dir = tmp.path().join(format!("unset{case}"));
                    std::fs::create_dir_all(&dir).unwrap();
                    std::fs::write(
                        dir.join("gated.props"),
                        "<Project><PropertyGroup><Out>from-import</Out></PropertyGroup></Project>",
                    )
                    .unwrap();
                    let hidden_body = match *hidden {
                        "writes" => format!(
                            "<Project><PropertyGroup><{name}>{value}</{name}></PropertyGroup></Project>"
                        ),
                        _ => "<Project><PropertyGroup><Unrelated>x</Unrelated></PropertyGroup></Project>"
                            .to_owned(),
                    };
                    std::fs::write(dir.join("hidden.props"), hidden_body).unwrap();
                    let mut xml = String::from(
                        "<Project>\n  <PropertyGroup><Plural>a;b</Plural><UndecidedX>abc</UndecidedX></PropertyGroup>\n",
                    );
                    if *hidden != "none" {
                        xml.push_str(
                            "  <Import Project=\"hidden.props\" Condition=\"'$(UndecidedX.Substring(0,1))' == 'a'\" />\n",
                        );
                    }
                    let condition = match *gate {
                        "empty" => format!("'$({name})' == ''"),
                        "nonempty" => format!("'$({name})' != ''"),
                        "equals" => format!("'$({name})' == '{value}'"),
                        _ => {
                            xml.push_str(&format!(
                                "  <PropertyGroup><Derived Condition=\"'$(Plural)' != '' and '$({name})' == ''\">true</Derived></PropertyGroup>\n"
                            ));
                            "'$(Derived)' == 'true'".to_owned()
                        }
                    };
                    xml.push_str(&format!(
                        "  <Import Project=\"gated.props\" Condition=\"{condition}\" />\n"
                    ));
                    if late {
                        xml.push_str(&format!(
                            "  <PropertyGroup><{name}>late</{name}></PropertyGroup>\n"
                        ));
                    }
                    xml.push_str("</Project>\n");
                    let project_path = dir.join("Demo.fsproj");
                    std::fs::write(&project_path, &xml).unwrap();

                    for globals in &sets {
                        let parsed = parse_fsproj_with_imports(
                            &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
                                .expect("a project path spelt as its full path"),
                            &globals.iter().cloned().collect(),
                            &common::oracle_environment(),
                            None,
                            None,
                        )
                        .expect("well-formed XML parses");
                        let names: Vec<String> = READ.iter().map(|n| (*n).to_string()).collect();
                        let theirs = oracle.project(&xml, &names, Some(&project_path), globals);
                        let supplied = globals.iter().any(|(k, _)| k == name);
                        for read_name in READ {
                            let claim = match parsed.property(read_name) {
                                PropertyRead::Value(v) => Some(v),
                                PropertyRead::Unset => Some(String::new()),
                                _ => None,
                            };
                            if *read_name == "Out" {
                                let key = format!(
                                    "name={name} gate={gate} late={late} hidden={hidden} global={supplied}"
                                );
                                let row = census.entry(key).or_default();
                                row.0 += 1;
                                row.1 += usize::from(claim.is_some());
                                if *hidden == "none" && claim.is_none() {
                                    must_commit_misses.push(format!(
                                        "{read_name} declined under {globals:?}: {:?}\n{xml}",
                                        parsed.property(read_name)
                                    ));
                                }
                            }
                            let Some(claim) = claim else { continue };
                            let theirs = theirs.as_ref().unwrap_or_else(|| {
                                panic!(
                                    "MSBuild rejects this project under {globals:?}, but we \
                                     committed {read_name} = {claim:?}\n{xml}"
                                )
                            });
                            assert_eq!(
                                Some(&claim),
                                theirs.get(*read_name),
                                "certain-implies-exact violated for ${{{read_name}}} under \
                                 {globals:?}\n--- xml ---\n{xml}"
                            );
                        }
                    }
                }
            }
        }
    }
    for (key, (cases, committed)) in &census {
        eprintln!("  {key:<70} {committed}/{cases} committed");
    }
    // Hidden content may write the name, so those cases owe nothing; the rest
    // must each reach a commit somewhere, or the grading above is vacuous.
    let vacuous: Vec<&String> = census
        .iter()
        .filter(|(key, (_, committed))| key.contains("hidden=none") && *committed == 0)
        .map(|(key, _)| key)
        .collect();
    assert!(
        vacuous.is_empty(),
        "dimension values never committed: {vacuous:?}"
    );
    assert!(
        must_commit_misses.is_empty(),
        "{} reads with no hidden content before them declined; the first:\n{}",
        must_commit_misses.len(),
        must_commit_misses[0]
    );
}

/// The **real SDK chain**, swept over the same globals.
///
/// This is the part that matters most, and the part no synthetic document can
/// stand in for. Every route the output-directory work found leaking lived in
/// the SDK's own props, not in the user's project: `Microsoft.Common.props`
/// writes `OutputPath` from `$(Configuration)` and `$(Platform)` and then
/// `OutDir` from `OutputPath`, `DefineConstants` picks up `DEBUG`/`TRACE` from
/// the configuration, and hook-point imports are gated on properties a caller
/// can set. Those are the values the LSP publishes; whether they are fixed facts
/// or artefacts of the globals it guessed is exactly the question here.
///
/// Both sides resolve the same installed SDK — ours through [`resolve_sdk`] over
/// `DOTNET_ROOT`, MSBuild's through its own resolver under MSBuildLocator — so a
/// divergence is about the walk, not about which chain was walked.
#[test]
fn sdk_chain_properties_are_exact_or_declined_under_every_global_set() {
    // The names an SDK project derives from `Configuration`/`Platform`, plus the
    // ones the blocked output-directory feature would have had to commit.
    const SDK_NAMES: &[&str] = &[
        "OutDir",
        "OutputPath",
        "BaseOutputPath",
        "IntermediateOutputPath",
        "DefineConstants",
        "AssemblyName",
        "TargetFramework",
        "Configuration",
        "Platform",
        "PlatformTarget",
        "Optimize",
        "DebugSymbols",
        // Names the ASP.NET SDKs' import gates read. `VisualStudioVersion` is a
        // toolset value no document writes, so it reaches the table (which
        // lists written names only) through the `sdk-visual-studio-version`
        // case's copy.
        "SeenVisualStudioVersion",
        "PublishProfileName",
        // What the swept `MSBuildUserExtensionsPath`'s `ImportBefore` file
        // writes, through `Microsoft.Common.props`'s wildcard import.
        "SeenUserExtension",
    ];

    let tmp = TempDir::new().unwrap();
    let root = canonical_root(&tmp);
    write_user_extensions(&root);
    let mut startups = startups(&root);

    let cases: &[Case] = &[
        // The plain project: everything below comes from the SDK, not the
        // document.
        Case {
            name: "sdk-plain",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[],
            startup_moves: &[],
        },
        // The user redirects output through `OutputPath`, interpolating the
        // configuration — the shape the blocked feature had to answer for.
        Case {
            name: "sdk-outputpath",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n    <OutputPath>artifacts/$(Configuration)/</OutputPath>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[],
            startup_moves: &[],
        },
        // …and through `BaseOutputPath`, which the SDK then composes with the
        // configuration itself.
        Case {
            name: "sdk-baseoutputpath",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n    <BaseOutputPath>build/</BaseOutputPath>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[],
            startup_moves: &[],
        },
        // A `Directory.Build.props` above the project, itself gated on a global:
        // the file the walker must find *and* condition correctly.
        Case {
            name: "sdk-directory-build-props",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n  </PropertyGroup>\n</Project>\n",
            files: &[(
                "Directory.Build.props",
                "<Project>\n  <PropertyGroup Condition=\"'$(Configuration)' == 'Release'\">\n    <BaseOutputPath>shipping/</BaseOutputPath>\n  </PropertyGroup>\n</Project>\n",
            )],
            // The SDK's derived paths are installation- and separator-dependent,
            // so nothing here is pinned to a literal. That the sidecar file is
            // genuinely reached is asserted instead by the `BaseOutputPath`
            // movement floor below, which only this case can satisfy.
            pins: &[],
            startup_moves: &[],
        },
        // The ASP.NET SDKs layer the Web, Razor and Publish SDKs over the
        // plain one. Their props read `TargetFramework` before the body defines
        // it (`GetTargetPlatformIdentifier($(TargetFramework))`), gate an import
        // on `$(VisualStudioVersion)` and derive `PublishProfileName` through
        // `Path.GetFileNameWithoutExtension`.
        Case {
            name: "sdk-web",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk.Web\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[("PublishProfileName", "Default")],
            startup_moves: &[],
        },
        Case {
            name: "sdk-worker",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk.Worker\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[("PublishProfileName", "Default")],
            startup_moves: &[],
        },
        // The toolset's `VisualStudioVersion`, copied into a written property
        // so the table reports it.
        Case {
            name: "sdk-visual-studio-version",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n    <SeenVisualStudioVersion>$(VisualStudioVersion)</SeenVisualStudioVersion>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[],
            startup_moves: &[],
        },
        // `DefineConstants` is a value the LSP feeds straight into the lexer's
        // `#if` handling, and the SDK derives it from the configuration.
        Case {
            name: "sdk-define-constants",
            xml: "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>net10.0</TargetFramework>\n    <DefineConstants>$(DefineConstants);MINE</DefineConstants>\n  </PropertyGroup>\n</Project>\n",
            files: &[],
            pins: &[],
            startup_moves: &[],
        },
    ];

    let mut committed = 0usize;
    let mut moving = 0usize;
    let mut tracked = 0usize;
    let mut sidecar_route_live = false;
    let mut startup = StartupCensus::default();
    for case in cases {
        let dir = root.join(case.name);
        std::fs::create_dir_all(&dir).unwrap();
        for (name, contents) in case.files {
            std::fs::write(dir.join(name), contents).unwrap();
        }
        let census = sweep_case(
            &mut startups,
            &root,
            &dir,
            case.xml,
            SDK_NAMES,
            case.pins,
            case.startup_moves,
            true,
        );
        eprintln!(
            "  {:<28} committed {:>3}, MSBuild rejects under [{}]  {}",
            case.name,
            census.committed,
            census.rejected_under.join(" "),
            census.render()
        );
        committed += census.committed;
        moving += census.derived_moving();
        tracked += census.derived_tracked();
        startup.add(&census);
        // `BaseOutputPath` moves only where a `Directory.Build.props` gated on
        // the configuration wrote it, so this is the named proof that the sidecar
        // was found and conditioned — the one SDK route whose liveness a
        // literal pin cannot state.
        // The ASP.NET import gates read these, so a decline anywhere in the
        // sweep leaves the project's import set undecided: each must commit
        // under every global set MSBuild evaluates the project under
        // (certain-implies-exact already holds the values to MSBuild, and
        // forbids a commit where it rejects the project).
        let must_commit: &[&str] = match case.name {
            "sdk-web" | "sdk-worker" => &["PublishProfileName"],
            "sdk-visual-studio-version" => &["SeenVisualStudioVersion"],
            _ => &[],
        };
        {
            for &name in must_commit {
                let committed_sets = census.by_name.get(name).map_or(0, |n| n.committed_sets);
                assert_eq!(
                    committed_sets, census.evaluated_sets,
                    "{}: `{name}` committed under only {committed_sets} of the {} global \
                     sets MSBuild evaluates the project under",
                    case.name, census.evaluated_sets
                );
            }
        }
        if case.name == "sdk-directory-build-props" {
            sidecar_route_live = census
                .moving_in_msbuild()
                .any(|(name, _)| name == "BaseOutputPath");
        }
    }

    eprintln!(
        "global-perturbation SDK chain: {} projects × {} global sets — {committed} \
         committed (name, globals) pairs; {moving} (case, name) pairs move in \
         MSBuild, of which we track {tracked}",
        cases.len(),
        global_sets(&root).len(),
    );
    startup.report("global-perturbation SDK chain");

    // The floor here is on *MSBuild's* movement, deliberately — unlike the
    // synthetic tests, whose inputs we author. What our side commits over the
    // real SDK chain is a measurement, not a target: it may legitimately be zero
    // (the chain trips uncertainty causes today), and pinning it would turn a
    // measurement into a ratchet nobody agreed to. What must not silently drift
    // is the *input*: an SDK whose properties stopped depending on the
    // configuration would make this whole test vacuous, and that is worth being
    // told about.
    //
    // `derived_moving` excludes `Configuration`/`Platform` themselves. They move
    // by construction — they *are* what the sweep varies — so counting them here
    // would let this floor stay green on five projects that had stopped reaching
    // the SDK chain entirely.
    assert!(
        moving >= 5,
        "the real SDK chain moved only {moving} SDK-derived (case, name) pairs \
         across the global sweep — either the SDK stopped deriving these from the \
         configuration, or the sweep is no longer reaching it"
    );
    assert!(
        sidecar_route_live,
        "`BaseOutputPath` did not move for `sdk-directory-build-props`, so its \
         configuration-gated `Directory.Build.props` is no longer being found and \
         conditioned — that case is testing nothing"
    );
}
