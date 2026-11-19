# `borzoi-assembly`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

F#-flavoured reader for
ECMA-335 assemblies: owned `Entity`/`Member`/`TypeRef` model, the
`EcmaView` trait, and a projector over an *in-crate* ECMA-335 reader
(no `dotnetdll` — it is GPL). Self-contained: depends only on `flate2`
(pure-Rust deflate for F# compressed signature resources) and `sha1`
(PublicKeyToken derivation). Intended to be reusable outside this repo.
A single undecodable member or type is dropped and recorded rather than
sinking the whole assembly (`Entity::skipped_members` /
`EcmaView::enumerate_type_defs_with_skips`), so a modern BCL DLL
projects all but the handful of types it genuinely cannot represent.
Ships a `test-support` feature exposing the differential-test normaliser
(`test_support` module) for callers that diff this projection against
another (e.g. the C# sidecar's Roslyn-emitted metadata), and the
`modifier_metamorphic` probe: ECMA-335 II.7.1.1's `modopt`/`modreq` rule
checked as a *metamorphic property* over real assemblies (decorate every
signature node with an unrecognised modifier and re-project — a `modopt`
must move nothing but the member's `drops_optional_modifier` record, a
`modreq` must leave no member standing). Any guard in
the projector that inspects the *head* of a signature (`matches!(sig,
TypeSig::ByRef(_))`) silently stops firing when a modifier sits in front of
it, and the compiler cannot catch that; the probe can, so read it before
writing such a guard.
The projection is name resolution's view, and it filters (undecodable
members, compiler output, pickle-only declarations another assembly cannot
name), so a question of *existence* — may anything of any accessibility sit
at this path — reads `existence::ExistenceIndex` instead: every `TypeDef`
row and every entity of the host F# pickle, at every accessibility, with no
projection in between. `borzoi-sema`'s `assembly_entities_diff` holds it row
for row to FCS's view of the assembly and to a `System.Reflection.Metadata`
walk (fcs-dump's `assembly-entities` batch kind).
A *whole-assembly* skip is a different grade of failure, gated by
`projection_skip_sweep` (`#[ignore]`d, `BORZOI_DLL_SWEEP_ROOT`): with an
assembly's types missing, no reading into any *other* assembly is provably
unshadowed, since the missing one could declare a colliding type or an
assembly-level `[<AutoOpen>]`. So the reader localizes wherever it can — a
`TypeRef` whose resolution scope is outside the modelled subset rides on the
row (`Result<RefScope, UnsupportedScope>`) and costs only the types that walk
out through it. The sweep classifies each loss **by cause, not by path**:
every `.dll`/`.exe`/`.winmd` under the roots is probed, and any loss whose
cause is not on the sweep's short `EXEMPT` list fails the gate. Filtering to
"what NuGet could select as a compile asset" instead would mean rebuilding
`borzoi_nuget::assets` here, and an approximation that wrongly *excludes* a
file hides exactly the regression the gate exists to catch.
**net4x is an unsupported target**, so the two targeting-pack shapes the
reader refuses whole (a netmodule, and an `mscorlib` whose manifest resource
is linked rather than embedded) are exempt rather than tracked work.
Unsupported means "will not be invested in", not "refused" — nothing declines
a `net472` project today, so a user who opens one gets less of it. Nothing
follows for the TFM vocabulary: parsing `net472` and modelling NuGet's
acceptance of `.NETFramework` are requirements of the MSBuild/NuGet
differentials, which reproduce those tools regardless of what borzoi serves
well. Run the sweep before widening any parse-time refusal:

```sh
BORZOI_DLL_SWEEP_ROOT=~/.nuget/packages \
nix develop -c cargo test -p borzoi-assembly --test all projection_skip_sweep:: \
  -- --ignored --nocapture
```

## Working here

Iterate with `nix develop -c cargo test -p borzoi-assembly`; the repository's root `AGENTS.md` has the pre-push gate.

Workspace builds always turn this crate's `test-support` feature on, so an item gated on `any(test, feature = "test-support")` can hide a use or an intra-doc link from them. After a change here run CI's featureless pair as well:

```sh
nix develop -c cargo clippy -p borzoi-assembly --lib -- -D warnings
RUSTDOCFLAGS="-D warnings" nix develop -c cargo doc -p borzoi-assembly --no-deps --document-private-items
```

Read first:

- skill: `assembly-surface-check`
