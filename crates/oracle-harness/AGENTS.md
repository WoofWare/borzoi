# `borzoi-oracle-harness`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

Test-only. `BatchChild`:
a *resident* oracle (`fcs-dump …-batch`, `msbuild-condition-oracle`,
`nuget-oracle`) driven as a lock-step request/response loop, so .NET startup is
paid once per test binary rather than once per case. A wedged or crashed oracle
is killed, respawned and the request retried, then panics — bounded and loud
beats silent and forever. Builds on `borzoi-spawn`. Also `manifest`: the
exact per-item pin a deterministic corpus gate compares its run against (a
sorted line per item, a line diff on any movement, `BORZOI_UPDATE_MANIFESTS=1`
to regenerate) — the replacement for one-sided count ratchets — and
`corpus_key`, the host-independent spelling of a corpus file and position in
an entry (Nix's macOS `~nix~case~hack~` suffix decoded). And `nuget_oracle`,
the `tools/nuget-oracle` driver, which lives here because both
`borzoi-nuget`'s differentials and the LSP's restore-graph oracle drive it.
And `xml_pump`: every short element path of an XML input repeated thousands
of levels deep, run on a 2 MiB stack. `roxmltree` (≥ 0.21.2) parses
iteratively, so a deep file overflows only through a walk of ours that
recurses per element; `borzoi-msbuild`'s `xml_nesting_pump` and
`borzoi-nuget`'s `dgspec::xml_nesting_pump` hold every reader of untrusted
XML to that without naming the recursive paths. A new reader belongs in one.

And `msbuild_oracle::fsc_args`, what fsc is really handed: it runs a real
`dotnet msbuild -nodeReuse:false -restore -t:Build` on a project where it
lies (hand it a fixture of its own), with `tools/msbuild-condition-oracle`'s
`FscArgsLogger` attached, and reads each `Fsc` invocation's response file
off the command line the task logs (its reported items unescape `%XX`, turn
`\` into `/` and leave out `--refout:`), parsed into a typed
`fsc_args::FscArguments` (a terminal option, `--version` and the like, yields
no assembly). A real build, not an imitation of one: an in-process imitation
(its own restore, its own target list, references left unbuilt, the compiler
skipped) differed from the CLI in each of those, in review after review.
Its domain is a build that does not read the process's command line, where
the logger shows. That is stated, not checked: a check against a second,
uninstrumented build kept missing what it did not know to compare, so it was
deleted, and the trees the differentials generate hold it by grammar (no
property function, no build code), which the generators assert. Callers set
globals and environment variables only through `BuildInputs`, which refuses
names that choose the toolchain, the compiler, the restore or MSBuild's
machinery. The build's own environment is closed too: a `BuildEnvironment`
carries only `BUILD_ENVIRONMENT_NAMES`, and the caller hands it to every
build, probe and host lookup (`msbuild_command`, `fsc_args`'s request,
`msbuild_user_extensions_path`, `dotnet_host`). The harness reads no
variable of its own process for a build: the crate's `clippy.toml` bans
`std::env`'s readers (by resolved path, so no import or alias hides one), and
each deliberate read that is not a build's (a tool's selector, where the
oracle's own scratch files go) carries an `allow` with its reason. So the
caller decides what a build inherits (the differentials pass their process's
`std::env::vars()`). Every build starts from
`msbuild_command`, which launches the .NET host itself rather than a
`dotnet` on `PATH` (the devshell's is a bash wrapper, which rewrites `PWD`,
`OLDPWD` and `SHLVL`), so the build sees exactly the variables it is handed. `borzoi-msbuild`'s
`fsc_args_oracle_calibration` holds the reading to real compiling builds
(the arguments `-getItem` reports, and the file fsc writes).

## Hostile values

`hostile` holds the strange values every generator should search, once, by the
kind of input (`hostile::Kind`: file names, path spellings, file-system states
and changes, property values, XML spellings, environments, working
directories, wire requests, source text). Each kind has a typed alphabet whose
entries carry a `Dimension` (the family: a switch-shaped name, a FIFO, an
option behind an escaped line break) and the reason the value is hostile.
`hostile::fs::HostileFs` makes every file-system state, writes nothing outside
its tree however a path is spelt, and reports, never skips, a state the
platform cannot make.

A harness enumerates the alphabet and mixes it into its own values in one
case in `hostile::RATE`, and records each drawn value where it reaches the subject in
a `Census`, opened through `hostile::coverage::open(file!(), …)`. A declared
dimension that never reaches the subject fails the test, as does an excluded
one that does and a census dropped without `finish`. Only a refusal that shows
the platform makes no value of a dimension excuses it
(`Unmakeable::excuses`). What each census owes, and what it excludes with the
reason, is pinned in `crates/<crate>/tests/manifests/hostile/<census>.txt`, the
same on every platform.

`src/hostile/boundaries.tsv` lists the generative differentials and
perturbation sweeps under `crates/` with the kinds each draws or the reason
none applies: every file a token scan takes for a generator (a proptest
strategy, one of the hand-rolled random number generators, a shared
perturbation engine, a telling file name), and the table-driven grids, which
have no such marker and are added by hand. `hostile::coverage`'s test fails on
a scanned generator with no row (CI runs it ungated, in the lint job). A row
marked `pending` is a harness that predates the library and that a retrofit
has yet to reach; `coverage::PENDING_BACKLOG` caps their number, so a new
generator cannot take the status.

`src/hostile/seed.tsv` maps the 200 review findings the library was built from
to the dimension that generates each, or the reason none does, and to what
became of it.

Known and out of scope for the library itself, so a review finding of the kind
is closed:

- The alphabets and the hand-added grid rows are incomplete by design, and
  grow when a harness or a finding needs a value.
- A special file the platform refuses at one path (a sandbox's policy, say)
  excuses its dimension for that run, though another path might have taken
  it. CI's runners refuse none, so the census there is exact.
- `coverage::PENDING_BACKLOG` caps the pending rows by count, not by path.
- The table's check ties a `draws` row to a file that uses the library and
  names its census. That the census is opened is for its manifest and the
  harness's own test to show.
- A seed row's outcome is checked against the kinds its census declares, not
  against the dimensions the census's manifest pins as owed.
- A spelling that looks like a Windows path is handed to the subject and not
  resolved. `spelling::resolve` compares canonical paths, so a hard link to
  the file is another file to it.
- The fixture's own names are not names a harness can ask for: `linked` at
  the tree's root, and `b` under the far link, which its `..` spelling then
  finds.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-oracle-harness`; the repository's root `AGENTS.md` has the pre-push gate.
