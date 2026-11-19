# `borzoi-print`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

An owned F# syntax tree a program builds
(`tree`, with validated names in `names`), and a *reference* printer that
writes it as source: every expression, pattern and type parenthesised, every
expression on one line, verbose forms throughout. It is the output half of
source generation; `borzoi-cst`'s lossless tree comes only from parsing.
The tree's types take the F# version they target (`version`: `Expr<V8_0>`
and so on), and a construct a version lacks carries that version's
uninhabited gate, so a tree cannot hold it. Each gate is named after FCS's
`LanguageFeature` and held to `borzoi-cst`'s feature table, its only
dependency. Its correctness oracle is in `borzoi-cst`'s tests
(`tests/all/print_roundtrip/`), beside the FCS harness it needs: for a tree
`t` at version `V`, FCS at `V` must parse `print(t)` with no diagnostic at
all and its parse must lower back to `t` exactly (and our parser must agree
with FCS); generated trees are checked at `preview` too, and each gated
construct must type-check at its version and be rejected one version below
it, by FCS's parser's FS3350 or, for a gate only the checker enforces, by
its checker (`print_roundtrip::gates`). The checker cannot grade a tree with
unbound names, so it grades the trees written over `print_roundtrip::check`'s
typed prelude: the gates, and the exhaustive table of computation-expression
statements nested in each other, at every version, where it must report no
error. A computation expression's body takes the context it sits in (a
builder's braces or a list's brackets, `tree::Context`), as a tree takes its
version, because the checker reads the two differently. The trees come from a generator over the
whole tree at every version, from exhaustive tables of keywords, short
operator spellings and computation-expression statements nested in each
other, and from every corpus file lowered with the unmodelled declarations
dropped (`print_roundtrip::corpus`, pinned per file). When the oracle finds
a value F# cannot express, the fix is to the tree's types, so that value
cannot be built; CI runs the printer's tests under the `cst` change filter.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-print`; the repository's root `AGENTS.md` has the pre-push gate.
