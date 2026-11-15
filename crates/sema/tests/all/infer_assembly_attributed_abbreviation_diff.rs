//! A type abbreviation carrying `[<AutoOpen>]` or `[<Extension>]` in a
//! referenced F# assembly brings the extension members of the type it
//! abbreviates into scope wherever its namespace is (#832), and inference
//! must decline every call one of them could join.
//!
//! In the fixture (`tests/fixtures/ext_universe_env`):
//!
//! ```fsharp
//! namespace ExtUniverse.StrAo
//! [<AutoOpen>]
//! type AoAlias = ExtUniverse.Str.StrExts   // Equals(this string, int) : int64
//! ```
//!
//! and in the project, `open ExtUniverse.StrAo` then `"abc".Equals(1)`: FCS
//! binds the extension. The extension gate asks an opened assembly namespace
//! for the extension members its types declare, and an abbreviation declares
//! none of its own.
//!
//! # The table
//!
//! [`Abbrev`] (the fixture's attributed abbreviations of a C#-style class of
//! `string` and of one of `Hashtable`, with each attribute written directly
//! and through a same-assembly alias, and the plain abbreviations as
//! controls) × [`Reach`] (an `open` of the abbreviation's namespace, or a
//! file declared inside it). Every project calls both extensions' names:
//! `"abc".Equals(1)` and `(asTable x).ContainsKey(1)`.
//!
//! # The properties
//!
//! 1. Certain-implies-exact soundness in every file.
//! 2. Through a plain abbreviation's namespace both calls commit (except
//!    `ContainsKey` in a file declared inside the namespace, whose ancestor
//!    `ExtUniverse` declares one in its module `FsExts`). Through an
//!    attributed one's, neither commits, and the literal one carries
//!    `ExtensionInScope`: the abbreviation's target is not enumerated, so no
//!    name is known absent.
//! 3. Where FCS binds a call to the extension (it types it `int64` where the
//!    intrinsic is `bool`) is pinned ([`fcs_binds`]).

use crate::common::ext_scope::{Call, check};
use borzoi_oracle_harness::par_map::par_map;

/// One of the fixture's abbreviations, by its namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Abbrev {
    /// `[<Extension>] type Alias = StrExts`.
    StrAb,
    /// `[<AutoOpen>] type AoAlias = StrExts`.
    StrAo,
    /// `[<AO>] type AoAlias = StrExts`, `type AO = AutoOpenAttribute`.
    StrAoAliased,
    /// `[<Ext>] type Alias = StrExts`, `type Ext = ExtensionAttribute`.
    StrAbAliased,
    /// `type PlainAlias = StrExts`.
    StrPlain,
    /// `[<Extension>] type Alias = CsExts`.
    Ab,
    /// `[<AutoOpen>] type AoAlias = CsExts`.
    Ao,
    /// `type PlainAlias = CsExts`.
    Plain,
}

impl Abbrev {
    const ALL: [Abbrev; 8] = [
        Abbrev::StrAb,
        Abbrev::StrAo,
        Abbrev::StrAoAliased,
        Abbrev::StrAbAliased,
        Abbrev::StrPlain,
        Abbrev::Ab,
        Abbrev::Ao,
        Abbrev::Plain,
    ];

    fn namespace(self) -> &'static str {
        match self {
            Abbrev::StrAb => "ExtUniverse.StrAb",
            Abbrev::StrAo => "ExtUniverse.StrAo",
            Abbrev::StrAoAliased => "ExtUniverse.StrAoAliased",
            Abbrev::StrAbAliased => "ExtUniverse.StrAbAliased",
            Abbrev::StrPlain => "ExtUniverse.StrPlain",
            Abbrev::Ab => "ExtUniverse.Ab",
            Abbrev::Ao => "ExtUniverse.Ao",
            Abbrev::Plain => "ExtUniverse.Plain",
        }
    }

    fn attributed(self) -> bool {
        !matches!(self, Abbrev::StrPlain | Abbrev::Plain)
    }

    /// The index in [`CALLS`] of the call its target's extension is named
    /// for.
    fn own_call(self) -> usize {
        match self {
            Abbrev::Ab | Abbrev::Ao | Abbrev::Plain => 1,
            _ => 0,
        }
    }
}

/// How the calling file reaches the abbreviation's namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reach {
    /// `module Use` then `open <namespace>`.
    Open,
    /// `namespace <namespace>` then `module Use =`.
    Enclosing,
}

const CALLS: [Call; 2] = [
    Call {
        binder: "c1",
        text: "\"abc\".Equals(1)",
    },
    Call {
        binder: "c2",
        text: "(asTable x).ContainsKey(1)",
    },
];

fn source(abbrev: Abbrev, reach: Reach) -> String {
    let body = [
        "let asTable (h: System.Collections.Hashtable) = h".to_string(),
        format!("let {} x = {}", CALLS[0].binder, CALLS[0].text),
        format!("let {} x = {}", CALLS[1].binder, CALLS[1].text),
    ];
    let lines: Vec<String> = match reach {
        Reach::Open => {
            let mut l = vec!["module Use".to_string(), body[0].clone()];
            l.push(format!("open {}", abbrev.namespace()));
            l.extend(body[1..].iter().cloned());
            l
        }
        Reach::Enclosing => {
            let mut l = vec![
                format!("namespace {}", abbrev.namespace()),
                "module Use =".into(),
            ];
            l.extend(body.iter().map(|b| format!("    {b}")));
            l
        }
    };
    lines.join("\n") + "\n"
}

/// Whether FCS binds the abbreviation's own call to its target's extension.
fn fcs_binds(abbrev: Abbrev, _reach: Reach) -> bool {
    abbrev.attributed()
}

#[test]
fn attributed_assembly_abbreviations_decline_every_call() {
    let mut cells = Vec::new();
    for abbrev in Abbrev::ALL {
        for reach in [Reach::Open, Reach::Enclosing] {
            cells.push((abbrev, reach));
        }
    }
    let results = par_map(cells.len(), |i| {
        let (abbrev, reach) = cells[i];
        check(&[("Use.fs", source(abbrev, reach))], &CALLS)
    });
    let mut failures = Vec::new();
    for (&(abbrev, reach), checked) in cells.iter().zip(&results) {
        let label = format!("{abbrev:?}/{reach:?}");
        for u in &checked.unsound {
            failures.push(format!("{label}: unsound: {u}"));
        }
        for (k, (call, outcome)) in CALLS.iter().zip(&checked.calls).enumerate() {
            if !abbrev.attributed() {
                // A file declared in `ExtUniverse.<x>` has `ExtUniverse` in its
                // namespace chain, which the gate takes as in scope, and
                // `ExtUniverse.FsExts` declares a `ContainsKey` extension.
                let ancestor_declares = reach == Reach::Enclosing && k == 1;
                if ancestor_declares {
                    if !outcome.gated() {
                        failures.push(format!(
                            "{label}: `{}` should carry ExtensionInScope through the \
                             `ExtUniverse` namespace; census {:?}",
                            call.text, outcome.census
                        ));
                    }
                } else if outcome.ours.is_none() || outcome.gated() {
                    failures.push(format!(
                        "{label}: `{}` should commit through a plain abbreviation; census {:?}",
                        call.text, outcome.census
                    ));
                }
            } else if k == 0 && !outcome.gated() {
                failures.push(format!(
                    "{label}: `{}` should carry ExtensionInScope; ours {:?}, census {:?}",
                    call.text, outcome.ours, outcome.census
                ));
            } else if outcome.ours.is_some() {
                failures.push(format!(
                    "{label}: `{}` should not commit; ours {:?}, census {:?}",
                    call.text, outcome.ours, outcome.census
                ));
            }
            let binds = outcome.fcs.as_deref() == Some("System.Int64");
            let want = k == abbrev.own_call() && fcs_binds(abbrev, reach);
            if binds != want {
                failures.push(format!(
                    "{label}: FCS {} `{}` to the extension, which the pin says it {}",
                    if binds { "binds" } else { "does not bind" },
                    call.text,
                    if want { "does" } else { "does not" },
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures over {} cells:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}
