# `borzoi-msbuild`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

MSBuild `.fsproj` parser /
evaluator: extracts the Compile order, expands `$(…)` substitution, evaluates
the condition subset, follows the SDK's `Directory.Build.props|targets`
import points, and — when an SDK resolves to the canonical dotnet
layout — walks the real `Microsoft.Common.props` → `NuGet.props` chain,
including the `Directory.Packages.props` central-package import.
Self-contained: depends only on `roxmltree` and `self_cell` (which holds a
parsed document beside its text, so the crate forbids `unsafe`), and, behind
`test-support` only, `borzoi-spawn` (the soundness sweep's FIFO watch holds
the FIFO open while no child is launched). Intended to be reusable outside
this repo. Every file-system query an evaluation makes
goes through `observed`, which records it in the result's `read_set` (absences
included); the crate's own `clippy.toml` bans the `std` calls elsewhere, and
test code reaches them through `observed::host_fs`. A resolver the caller
passes must query through the `Observer` it is handed. The read set is held
to `observed::soundness::sweep` (perturb each file; a read set that still
validates must mean an unchanged evaluation), which every
`with_imports_tests` helper runs over its test's tree, so a new reader that
skips the observer fails there or in clippy. A whole-file read opens only a
regular file (`observed::open_regular`): a FIFO's open waits for a writer.
The helpers' sweeps also make each file a link to a FIFO in turn
(`soundness::fifo_perturbations`), and fail, rather than hang, on any query
that opens it. An `Observer` asks each query
once per evaluation, and `parse_fsproj_with_imports_reusing` reuses an
earlier evaluation's parse of an imported file whose bytes, read again, are
the same (`observed::ImportDocuments`); `observed::reuse` holds both to the
reference that asks every time (`Observer::asking_every_time`) at every step
of every helper's sweep and on every integration test's evaluation
(`tests/common`'s `parse_fsproj_with_imports`). The evaluator is
differentially tested against the
real MSBuild evaluator via `tools/msbuild-condition-oracle` — a test-only
JSONL batch oracle (in the `tools/fcs-dump` / `tools/nuget-oracle` mould)
that evaluates in-process through the MSBuild API; it is never a
runtime dependency of the LSP. Reached from the tests through the crate's
`test-support`-feature `test_support` module. It has four ops, and the
distinction matters: `eval` (a `Condition` string) and `expand` (a property
*body*) both take their input *after* MSBuild's XML layer has run, so they
are structurally blind to it. Their stubs write a tab, line feed or
carriage return as a character reference, so MSBuild reads each as itself,
as it does in a project file (it normalises neither attribute values nor
line ends); `condition_diff` and `property_expr_diff` each grade their
evaluator on such text with a whitespace axis. `project` hands MSBuild a
whole document verbatim and reads back the evaluated property table, which is the only way
to diff the XML layer itself (insignificant whitespace, entity decoding,
CDATA, comment-split text); `items` is `project`'s item-side twin, reading
back an item type's evaluated `FullPath`s (what `-getItem:` reports, but
resident — a per-case `dotnet msbuild` pays .NET startup every time, which a
generative sweep cannot afford). `project` and `items` also carry the
evaluation's **global properties** — the `-p:` set, which is *not* a
property-group write: it is read-only to the document, outranking every write
of that name unless `TreatAsLocalProperty` opts out. Both evaluate as a build
does (a `ProjectInstance`, as `dotnet build` and `dotnet restore` do), so a
toolset name such as `MSBuildSDKsPath` is a global like any other. The
editable `Project` a design-time host loads (`"designTime": true` on
`project`) also evaluates the items under a false gate, so it rejects every
project a build rejects and more; the walk's rejection model is its rule, and
`where_msbuild_evaluates_a_condition` pins where the two differ.
`rejection_generative_diff.rs` holds that model to it over generated projects
whose conditions and bodies MSBuild may throw on (hostile values, uncertain
operands in every position), and the condition judgement to `eval` under
every assignment of the uncertain names; the projects MSBuild rejects that the
walk commits are counted and pinned by the open gap each is. The five
differentials that ride on these ops:
`condition_diff.rs`, `property_expr_diff.rs`,
`fsproj_property_table_diff.rs`,
`fsproj_item_escape_generative_diff.rs` (item specs over an escape-bearing
alphabet — the harness that guards MSBuild's escaped-value domain, where the
rule is *scan and split before you decode; trim in the domain; decode at the
leaf*; see `docs/completed/msbuild-escaped-value-plan.md`), and
`fsproj_global_perturbation_diff.rs`. All assert
*certain-implies-exact*: when we commit a value, MSBuild must agree exactly;
a decline makes no claim.
The last one exists because the other four are structurally blind to one
defect class. They evaluate both sides under the *same* globals, so a value
whose evaluation depends on a global the caller supplied — through a route we
do not model — agrees with MSBuild exactly and passes every one of them. The
LSP injects `Configuration=Debug, Platform=AnyCPU` as a guess and publishes
what comes back as fixed fact, so that class is live. Sweeping the global set
turns it back into an ordinary certain-implies-exact violation; no new
contract was needed, only a harness that varies what the others hold fixed.
It runs the corner list of routes (gates, `<Choose>` arms, property-selected
imports, `TreatAsLocalProperty`, toolset names as globals), a generated
sweep, the Compile item set, and the **real SDK chain**, and prints a movement
census — how many values MSBuild moves across the sweep, and for each whether
we tracked it, declined it as untrusted, or never reached it. Every point is
also evaluated by MSBuild started from three directories (one oracle child
each) and by the walk with no startup directory, where nothing the directory
moves may be committed, and with each, where every commit must be MSBuild's
from there; the census counts those points too. Read that census before investing in a
"depends on a caller-supplied global" provenance dimension: today the
evaluator is sound on this axis and pays for it in declines
(`OutDir`/`OutputPath`/`DefineConstants` are untrusted under every global set
on a real SDK project), which makes such a dimension a coverage investment,
not a soundness fix.
Three ops execute rather than evaluate. `targetItems` runs one target on an
evaluation and reads back an item list: `fsproj_compile_order_generative_diff.rs`
runs F#'s `FSharpSourceCodeCompileOrder` (its text lifted from the installed
SDK into a synthetic SDK) and holds the compile order we commit to
certain-implies-exact, since the order the compiler sees is not the evaluated
`@(Compile)`. `restoreCone`
builds `GenerateRestoreGraphFile` in-process and reports every target and
task that ran, with file hashes and task-assembly identities.
`restore_cone_census.rs` pins that cone per project and per installed SDK
(stage 8 of `docs/nuget-dgspec-boundary-plan.md`), under the global
properties `borzoi_oracle_harness::restore_globals` holds to `restore.rs`'s
command line.
`restoreCone` also returns the `_RestoreGraphEntry` items
`WriteRestoreGraphTask` was handed, logged as its input. The census
puts each cone's entries through `borzoi_nuget`'s `write_restore_graph`
and pins the item seam's verdict on each cone of SDK targets alone: the
cone's own spec, byte for byte, or a decline.
It also reads every property and item type the cone's targets reference,
in two places. One is the end of our evaluation, through a probe on the walk
(`test_support::parse_fsproj_reads`), which must leave the `ParsedProject`
unchanged. The other is the end of MSBuild's, through the `evaluated` op,
which evaluates without building. A trusted value MSBuild disagrees with
panics. Every other verdict (unset, inexact, untrusted, an item table's
identities and taint, and their metadata) is pinned in
`restore_cone_reads_*.txt`. That is the worklist for A₁.3's executor.
The probe also answers where each target the cone ran is defined, and an
exact answer that is not the definition MSBuild's target table keeps
panics. `fsproj_target_definitions_generative_diff` holds those answers to
the same table on generated import graphs.
`fsproj_target_execution_generative_diff` holds A₁.3c's executor (the
probe's `execute`) to the oracle's `runTargets` op, which builds targets
in-process and reports the targets that started and the properties and
items left; the census pins where the executor stops on each cone.
`fsproj_generic_items_generative_diff` holds the generic item tables the
probe reads, metadata included, to the `itemsMeta` op on generated
projects.
What fsc is really handed comes from
`borzoi_oracle_harness::msbuild_oracle::fsc_args` (`crates/oracle-harness/AGENTS.md`):
use it rather than re-deriving an fsc input from evaluated values, since
every hand re-derivation leaked. Its first consumer is
`borzoi_msbuild::fsc::compiled_assembly_name`, the name of the assembly a
project compiles to. It commits only over a positive domain: every property,
item type, item metadata name and global set from outside the .NET install
is on one of its lists, and each allowed property's value matches its
grammar; documents outside the install are literal and unconditional (#993,
#1060). Widen the domain by adding a name to a list, never by subtracting a
route. Environment variables are the exception, by a stated assumption (the
build's environment is the evaluation's): a variable declines when an SDK
file reads a property of its name or the build's tools read it, both listed
per verified SDK in `src/fsc_environment_reads.txt` (scanned from the SDK's
documents and binaries by `tests/fsc_environment_reads.rs`, which fails until
an SDK bump is rescanned, the binaries through the condition oracle's
`envReads` op), unless it is the toolchain's own, an allowed property or
graded inert, and the loader's and a script launcher's (`LD_`, `DYLD_`,
`BASH_ENV`, …, which run before any code of the install) always decline;
any other is inert by construction, which the grader checks by setting
names off both lists and requiring fsc's arguments unchanged. The pin is
keyed by platform (the binaries differ), each list the union over
platforms; a platform's sections are regenerated on it. `fsproj_assembly_name_perturbation_diff`
grades every listed name: it sets each one, everywhere it can be set, to
line-break and option-shaped values, and holds each commit to fsc's `-o:`
(its ignored `deep_every_perturbation` covers every case, and with
`BORZOI_UPDATE_MANIFESTS=1` records the SDK and its workload manifests in
`src/fsc_verified_sdks.txt`). A name goes on a list only together with its
grading. The derivation's register is keyed by what fsc receives, not by
where input comes from: `fsc::FSC_PARAMETERS` lists every parameter of the
SDK's `<Fsc>` invocation, its whole expression and what feeds it, and
`fsc::BUILD_TIME_SITES` every write the SDK's targets make to those at build
time, each by its expression and every condition it runs under, with its
gate. `fsc_parameter_register` reads every verified SDK's targets and fails
on a parameter, an expression, a feed or a build-time site the register does
not hold. A finding that names an input reaching fsc other than through a
registered parameter and its sites means that test is wrong: fix the test
first, then report. The module documentation tabulates the gates; the
assets file's freshness is assumed, as the LSP's env assumes it (#1044).
`fsc_name_census` (ignored, `BORZOI_FSC_NAME_CENSUS_ROOTS`) reports how much
of a corpus the derivation commits for and every rule each project breaks.
The workload locator SDKs (`sdk_resolver/workloads.rs`) have their own
test-only oracle, `tools/workload-oracle`, which loads each installed SDK's
workload resolver by reflection (on that SDK's runtime, so SDK 11's
prerelease is graded too). `workload_locator_diff` holds the feature band,
the band order and both locators' answers on generated dotnet layouts to it,
for every SDK of `BORZOI_DOTNET_ROOT_SDK11`.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-msbuild`; the repository's root `AGENTS.md` has the pre-push gate.

This crate's CI job also runs ignored sweeps, which `cargo test` skips. Run them before pushing:

```sh
bash tools/ci/corpus-sweeps.sh msbuild            # all of them
bash tools/ci/corpus-sweeps.sh --list msbuild     # their names, to run one
```

The MSBuild corpus differential (`msbuild-corpus`) evaluates the F# compiler's
own projects, whose `global.json` asks for SDK 11, so it evaluates them against
the devshell's second dotnet root, `BORZOI_DOTNET_ROOT_SDK11`
(`dotnet-sdk-corpus` in `flake.nix`). Keep SDK 11 out of the default root: with
no `global.json` above them, every temporary fixture would resolve it as the
newest SDK.

Workspace builds always turn this crate's `test-support` feature on, so an item gated on `any(test, feature = "test-support")` can hide a use or an intra-doc link from them. After a change here run CI's featureless pair as well:

```sh
nix develop -c cargo clippy -p borzoi-msbuild --lib -- -D warnings
RUSTDOCFLAGS="-D warnings" nix develop -c cargo doc -p borzoi-msbuild --no-deps --document-private-items
```

Read first:

- `docs/completed/msbuild-escaped-value-plan.md` before touching escaped values
- `docs/nuget-dgspec-boundary-plan.md` for the restore cone and A₁
- skills: `msbuild-condition-oracle`, `msbuild-trust-audit`
