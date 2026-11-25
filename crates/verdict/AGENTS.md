# `borzoi-verdict`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

Answers that can be incomplete, as types that cannot be read as complete
(#1121). `Verdict<T, C>` is a value the producer commits to or the cause
`C` of its doubt; `Lookup<T, C>` is `Found`, `ProvedAbsent` or
`Unknown(C)`. They are the same information (`Lookup<T, C>` is
`Verdict<Option<T>, C>`), converted losslessly both ways.

The recurring wrong-answer class this exists for is "provably absent"
conflated with "didn't look": an `Option` or a `bool` from a producer that
may not have seen everything, read as complete. So the crate deliberately has
no conversion from or to `Option`/`bool`, no `Default`, no iteration and no
`or` on `Verdict`. The crate docs say why for each, and their `compile_fail`
doctests spell the absences out. A reading can be added under any name, so
`tests/pin.rs` pins the exact text of every file under `src` (by hash of the
bytes rustc compiles, so CRLF reads as LF, in `tests/src.pin`) and the set of
their names: any edit or new file fails until
the pin is regenerated with `BORZOI_UPDATE_MANIFESTS=1`, so the reviewer sees
every change to the primitive. Do not add any such reading; a consumer that
needs one writes the `match` that makes its choice visible.

Every operation's laws are in its doc comment, and `tests/laws.rs` checks
each one exhaustively over a finite domain (every value, cause and function
on it). Collecting is also checked under every way a `FromIterator` target
can read what it is offered (all of it, none, a prefix, as many as the size
hint promises, then asking again after the end), checking the size hint it
is offered at every step, and over a source that is not fused. A new
operation comes with its laws and their exhaustive check, and a regenerated
pin. Add an operation only with the consumer that needs it.

No dependencies, `no_std` (`sha1` is a dev-dependency, for the pin only).
Reusable crates may depend on it; each that does says so in its "depends only
on" line.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-verdict`; the repository's root `AGENTS.md` has the pre-push gate.
