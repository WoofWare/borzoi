# MSBuild's unix path fixup (`MaybeAdjustFilePath`)

> Found by the E0 decoder differential in `docs/completed/msbuild-escaped-value-plan.md`,
> on its first run against real MSBuild. It is **not** an escaping bug and does
> not belong to that stack: it is a separate, host- and cwd-dependent
> normalisation.

> **Status:** landed. P0 (#948), the P3 keystone (#953), the expansion stage
> (#987) and the startup-directory worlds (#993) are in. A relative probe is a
> question about MSBuild's startup directory, which a served evaluation does
> not know: the walk carries one value per answer and commits only what every
> answer agrees on, and an evaluation whose startup directory the caller
> supplies (the restore cone's) asks the file system instead. What remains is
> listed under "Still to do": each is a decline, not a guess.

## The behaviour (reference)

On **non-Windows hosts only**, MSBuild's expander passes every expanded piece
through `FileUtilities.MaybeAdjustFilePath` (`Expander.cs:186,225,229`;
`FileUtilities.cs:608`). For a piece that

- is not empty, and does not start with `$(`, `@(` or `\\`, and
- contains a `\`,

MSBuild converts **every** `\` to `/` *and collapses runs of slashes*
(`CollapseSlashes`, a `[\\/]+` → `/` rewrite — so `a\\b` and `a\/b` both become
`a/b`), then keeps the rewrite **iff the result "looks like a unix file path"**
(`LooksLikeUnixFilePath`, `FileUtilities.cs:718`): its first segment exists **as
a directory**, probed with `Directory.Exists(Path.Combine(baseDirectory, seg))`.

The `baseDirectory` is the load-bearing part, and it differs by call site:

| call site | `baseDirectory` | decidable by us? |
| --- | --- | --- |
| property values, item specs, conditions (`Expander`'s builder) | **`""` → the MSBuild process's current working directory: its startup directory** | **No**, unless the caller starts the process |
| item metadata (`LazyItemOperation.cs:215,252`) | the startup directory, then a second whole-value pass under the containing project's directory | Only the second pass, and only partly |

The startup directory is one directory for the whole build: the entry project
and every project it builds through the `MSBuild` task, in-proc or on a worker
node, probe under the directory `dotnet build` was started in, not under their
own (probed with `-m:1` and `-m:4`, from the project's directory, an unrelated
one, and one holding `obj/`). The exception is `-mt`, the multithreaded mode,
which probes under each project's directory; borzoi models no build run that
way. A target's expansion probes under the project's directory, which the build
request sets.

So **the evaluated property table is not a function of the project text**: the
same project evaluates differently depending on the directory `dotnet build` was
invoked from. We have no MSBuild process and therefore no cwd to consult — the
value is *genuinely ambiguous*, not merely unknown. An *escaped* backslash is
invisible to the fixup (`.%5cx` keeps its backslash where `.\x` would not): the
fixup runs on escaped text, upstream of unescaping.

## Why declining is wrong (reference)

"A backslash-bearing property value is ambiguous, so decline it" would poison
the SDK chain: `Microsoft.Common.props` writes `<BaseIntermediateOutputPath …>obj\</…>`
(one of ~46 backslash-bearing SDK property writes), and `BaseIntermediateOutputPath`
feeds `MSBuildProjectExtensionsPath`, which discovers the `NuGet.props` →
`Directory.Packages.props` chain. Declining it would take package resolution down
for every project — to fix a divergence with no consumer-visible consequence:
`obj\` and `obj/` name the same directory once used as a path, and we normalise
separators at every path use. The ambiguity is real but usually **immaterial**.

The model that follows: for each eligible piece the fixup has exactly **two**
possible results (probe hits ⇒ `converted`, misses ⇒ `raw`). Evaluate the
consumer under each world and commit iff they agree. Path uses are provably
immaterial (both worlds normalise to the same `Path::components()`), conditions
bracket ≤ 2^k worlds and commit on unanimity, exact-value consumers degrade only
on genuine disagreement. A key refinement the keystone forced: a fixup-eligible
piece consumed *through a path function* collapses its two worlds back to one
(`Combine`'s result crosses an expansion boundary and meets `MaybeAdjustFilePath`
again), so a value whose worlds agree is *committed determinate*, not degraded.

## Landed stages (one line each)

- **doc** (#928) — pin the behaviour against real MSBuild and plan the response.
- **P0** (#948) — `properties/path_fixup.rs`: `fn worlds(value) -> Option<String>`
  (the eligibility + `\`→`/`/slash-collapse rewrite, ported from `FileUtilities.cs`
  with citations), plus the two-cwd `path_fixup_diff.rs` oracle that runs `dotnet
  msbuild` from a hit-cwd and a miss-cwd and asserts our two worlds bracket both
  answers exactly. Inert on Windows.
- **P3 keystone** (#953) — the fixup-ambiguity in the MSBPEP chain never reaches a
  *stored* exact value; it is consumed entirely inside two functions whose
  committed answer is cwd-independent (oracle-pinned both cwds, guarded by the
  two-cwd expression differential in `path_fixup_diff.rs`):
  - `[System.IO.Path]::Combine` converts a **live** backslash unconditionally, so
    `combine_path` (joins with `/`, rewrites each part) *is* the answer; the old
    "declines any backslash-bearing part" guard was removed. An **escaped** `%5c`
    survives as a literal `\` that `combine_path` cannot represent, so the shared
    path-arg layer (`eval_exact_path_arg`) declines it *for Combine only* (flag
    `reject_escaped_backslash`). `NormalizePath`/`GetDirectoryNameOfFileAbove`
    normalise via `GetFullPath` (converts a backslash however spelled) and keep
    committing.
  - `[System.IO.Path]::IsPathRooted` commits every **non-leading** backslash
    (rootedness is fixed by the first character, which the fixup leaves alone) and
    declines only a **leading** one (a live `\a`→`/a` is indistinguishable from an
    escaped `%5ca` once decoded).

  This pins `MSBuildProjectExtensionsPath` to `<projdir>/obj/`, keeps
  `walk_opaque` from latching at the `Common.props` import gate, un-ignores
  `tests::msbuild_project_extensions_path_normalises_the_obj_default`, and drops
  the `sdk_style_netcoreapp_fsharp_implicit_dependencies_match_msbuild` Stage-C
  fixture **270 → 52** causes (the `TargetPlatformVersion`/`PublishAot`/
  `RuntimeIdentifier`/`TargetsNet*` cascades were all collateral of this one
  decline). No world-set, provenance bit, or table degradation was needed.
- **Plain imports** (#903) — a `\` a property supplies to `<Import Project>`
  (the attribute's own are `/` already, by `FixFilePath`). MSBuild opens
  `FixFilePath(GetFullPath(dir/expansion))`: it collapses `..` over `/` alone,
  so a `\` the fixup kept is a name character there (`q\..\../..` pops
  `q\..\..` whole), and the kept spelling is the duplicate-import key
  (`zz\..\T.props` imports an already-imported `T.props` again). Each piece's
  fixup only rewrites slashes, so when the *whole* expansion's probe hits, the
  path is lexically the expansion with every `\` a `/` whatever the pieces did.
  The walk commits exactly then: `unix_adjustment_rewrites` asks
  `path_fixup::unix_path_probe` (`.`/`..` hit; an absolute segment is probed
  through `observed`), and declines the import otherwise. The pieces'
  decisions are not modelled; `sdk_import_project_path_diff` runs MSBuild from
  three working directories and holds every commit to all of them.
- **Expansions** (#987) — `properties::substitute` adjusts each piece (a
  literal run, a reference's value) and then the whole value, as MSBuild's
  `SpanBasedConcatenator` and `ExpandIntoStringLeaveEscaped` do
  (`path_fixup::adjust`). A probe of `.`/`..` hits, an absolute one is asked
  through `observed` (`dotnet_io`'s `Directory.Exists` /
  `FileOrDirectoryExists`), and a relative one turns on the working directory.
  A value MSBuild stores without expanding it — a global, the environment, a
  toolset or reserved name, a task output — keeps
  its `\` until a read adjusts it: `MSBuildUserExtensionsPath`, the host's
  `$(LocalAppData)` joined with `Microsoft\MSBuild`, reads as
  `…/Microsoft/MSBuild`. A seed's backslash that meets a relative probe, and
  any absolute probe on the path that asks no file system, declines
  (`PathAdjustmentUndecided`); project text's relative probe was taken to
  miss, until the worlds stage. A condition operand is expanded, and adjusted, only when
  MSBuild's scanner saw something to expand in it. Targets run in the project's
  directory, so the executor declines every relative probe
  (`substitute_in_target`). `path_fixup_expansion_diff` holds this to MSBuild
  from an empty working directory and one holding every relative segment, over
  generated values × sources × read sites (body, condition, `Exists`, property
  function).

- **Startup-directory worlds** (#993) — `properties::worlds`. Each relative
  segment a probe names is a free yes/no (is it a directory where MSBuild
  started?), and a value is a decision tree over them (`Worlds`), built by
  running a computation once per assignment it turns out to need
  (`in_every_world`) and collapsing every split whose sides agree. A property
  write stores the tree; a read in an expansion takes its world's value, so a
  path function that converts its argument (`Combine`) collapses the worlds,
  and a value the SDK only ever composes into such a function is one value. A
  condition is evaluated in every world and decided only where all agree, so
  `'$(BaseIntermediateOutputPath)' == ''` decides and `== 'obj/'` does not
  (`Outcome::StartupDirectory` where every world returns a boolean, which is no
  rejection). A path value collapses only where its reader reads the same
  thing in every world: a Compile or reference `Include` with no `Exclude` on
  the full paths it publishes (`separator_insensitive`), its items then
  carrying no identity, so a `Remove`, an `Update` or `@(…)` declines; a
  `Remove` or `Exclude` on full paths unless MSBuild compares a literal
  fragment as written (`match_collapse`); an import's `Project`, which reads
  the spelling, onto the world every other is with some `\` respelled `/`
  (`import_collapse`), then judged as before (`adjustment_settles`); none
  collapses text holding an escape. A Compile or package `Update` collapses
  no worlds: its batch keys, leaves and removes fragments by their spelling,
  so a spec whose worlds differ at all is one the walk does not know. An
  `Update` the walk does not know (one it cannot expand, reads from an
  untrusted value, or whose worlds differ) leaves its batch
  unknown, and every later fragment may collide with it; a strand is counted
  only for an `Update` that writes captured metadata (`CompileOrder`, or a
  captured package metadatum), since the strand applies its own. MSBuild
  expands each `Exclude` fragment a second time, so its own first segment
  decides its `\` again and a reference spliced raw is expanded then: an
  `Exclude` whose fragment that pass may move declines. MSBuild's
  `FixFilePath` turns each `\` written in an import's `Project`, SDK or
  plain, and in the argument of a condition's `Exists` or `HasTrailingSlash`
  into `/` on Unix before expanding it (`path_fixup::fix_file_path`), for
  every reader of it. An `Update` that leaves the batch removes its fragments
  spelled as their key, which `update_batches_match_msbuild` sweeps. A bare
  `Include` reads a wildcard spelled as an escape as a literal naming a full
  path; an `Exclude` reads it as written. Once the walk declines a
  property write for the startup directory (skips one under a gate whose
  outcome turns on it or asks past the segment cap, refuses one past the
  cap, or declines a `DefaultTargets` that turns on it, which it then
  refuses rather than unsets), a later condition that may throw on any name
  the walk is not certain of is a possible rejection
  (`State::startup_directory_declined`): the declined write holds, in some
  world, a value the walk does not, under any name it is copied to and past
  any later write the walk is not sure ran. It does not track which names the
  write reaches (a group's own gates may read siblings it writes, an
  imported `DefaultTargets` may copy one, an import the walk follows may not
  run); no SDK write is declined so, so the coarse rule costs nothing
  measured. The same through any other undecided gate waits on #1009, as
  does a write the walk refuses because a property function fails in some
  worlds: it does not tell a function MSBuild throws on from one it does not
  model, and the SDK's own path functions over a value whose worlds differ
  are the latter. An `Exists` guard over an import's list asks about each
  entry, as MSBuild's does. An import
  whose path the walk cannot compute is a possible rejection even under an
  `Exists` of that path: `Exists` is true of a directory and of a spelling the
  import reads apart. An end-of-walk reader computes its output in each world
  and commits where they agree (the output name, the framework list, the
  define list, the central-package flags). Every other reader takes one value
  only where every world agrees (`State::expand`). `property_reads`
  publishes a split value as `UntrustedCause::StartupDirectory`, carrying each
  value, so a reader of part of one (an output file's name) can collapse it on
  that part. A computation asking more than `MAX_SEGMENTS` (6; the corpora
  reach 3) segments along a path declines. With a startup directory supplied
  (`Start::Known`), each probe asks `Directory.Exists` under it through the
  observer, so the read set covers it. `path_fixup_expansion_diff` runs MSBuild
  from the project's directory with and without the segments and from four
  unrelated directories (holding no segment, every one, and each alone), over
  generated values × sources × read sites (body, condition, `Exists`, property
  function, `Compile` include and glob, a generic item's identities beside a
  `Remove`), and holds every served commit to all of them and every supplied
  one to its own; it includes the SDK's `obj\`, which `main` published as
  trusted. A property function's throw is judged per world (#1009's
  classification, `Issue::Throws`'s `everywhere`): one some world does not
  make is a possible rejection, never a certain one, and a condition's leaf is
  judged in every world (`judge_leaf_in_every_world`). The rejection-shaped
  sites (an indexer past the end, a coercion, a gate over a coerced write) meet
  wrong answers `main` shares (#1097), so the fresh-seed soak draws only the
  others, where the walk answers no point wrongly; the fixed-seed sweep
  (`fixed_seed_sweep_regresses_nothing_main_answers`) draws every site and
  holds each wrong claim to `main`'s walk over the same point
  (`tests/manifests/path_fixup_baseline.txt`, `tools/path-fixup-baseline.sh`):
  one `main` answered rightly or declined fails it, and one `main` shares is
  pinned (`tests/manifests/path_fixup_pins.txt`).

The superseded stages — the original P1 (conditions bracket the worlds), P2
(exact-value consumers degrade), and their "scan the evaluated property table"
framing — were wrong to treat the ambiguity as a property of the *final
evaluated string*. It is a property of the derivation: a value's worlds are
decided piece by piece and then whole, a splice carries what its property
stored, and a global bypasses the expander until it is read. The worlds stage
evaluates the derivation once per world instead, which gets each of those
right without modelling it.

## Still to do

Each of these declines today; none guesses.

- **Imports under a supplied startup directory.** A plain import whose
  expansion keeps a relative `\` that moves the file (`adjustment_settles`)
  declines even where the startup directory is known, since
  `unix_adjustment_rewrites` does not ask it. Nothing on the restore cone's
  chain reaches it.
- **A target's relative probe.** The executor declines every one: a target
  runs in the project's directory, but at a moment of the build (after restore
  has created `obj/`, say) the walk does not observe.
- **Item metadata.** Its second pass probes under the containing project's
  directory, which this crate does not ask, so a metadatum whose value still
  holds a relative `\` declines (`properties::metadata_pass`). No modelled
  metadatum holds one in the corpora.
- **Property functions.** A function result holding a live `\` declines
  (`expr::has_unix_backslash`) whatever the startup directory, so what moves
  at a property function is never committed, even with the directory
  supplied.
