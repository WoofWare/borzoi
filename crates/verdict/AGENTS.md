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
doctests hold the absences. Do not add any of them; a consumer that needs one
of those readings writes the `match` that makes its choice visible.

Every operation's laws are in its doc comment, and `tests/laws.rs` checks
each one exhaustively over a finite domain (every value, cause and function
on it). A new operation comes with its laws and their exhaustive check.
Add an operation only with the consumer that needs it.

No dependencies, `no_std`. Reusable crates may depend on it; each that does
says so in its "depends only on" line.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-verdict`; the repository's root `AGENTS.md` has the pre-push gate.
