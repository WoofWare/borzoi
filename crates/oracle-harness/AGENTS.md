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

A harness enumerates the alphabet and mixes it into its own values at
`hostile::RATE`, and records each drawn value where it reaches the subject in
a `Census`, opened through `hostile::coverage::open(file!(), …)`. A declared
dimension that never reaches the subject fails the test, as does an excluded
one that does and a census dropped without `finish`. Only a refusal that shows
the platform makes no value of a dimension excuses it
(`Unmakeable::excuses`). What became of each dimension is pinned in
`crates/<crate>/tests/manifests/hostile/<census>.txt`.

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
is closed: the alphabets and the hand-added grid rows are incomplete by
design, and grow when a harness or a finding needs a value.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-oracle-harness`; the repository's root `AGENTS.md` has the pre-push gate.
