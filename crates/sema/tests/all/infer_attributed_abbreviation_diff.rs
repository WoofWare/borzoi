//! A project type abbreviation carrying `[<AutoOpen>]` or `[<Extension>]`
//! brings its target's extension members into scope (#831), and inference
//! must decline every call one of them could join.
//!
//! FCS reads both attributes off the abbreviation's own type and then works
//! on the type it abbreviates: an `[<AutoOpen>]` abbreviation in scope opens
//! the target's static content (`CanAutoOpenTyconRef` →
//! `AddStaticContentOfTypeToNameEnv`, whose `tryAppTy` strips the
//! abbreviation), C#-style extension members included; an `[<Extension>]`
//! one passes `IsTyconRefUsedForCSharpStyleExtensionMembers` on its own
//! attribute and then lists the target's methods. So
//!
//! ```fsharp
//! [<AutoOpen>]
//! type A = ExtUniverse.Str.StrExts   // static member Equals(this string, int) : int64
//! let c x = "abc".Equals(1)          // FCS: int64
//! ```
//!
//! binds the extension with no `open` of the assembly that declares it. The
//! extension gate keys a project's extension sources by the attributes that
//! may be the `[<Extension>]` marker, so it does not see the first.
//!
//! # The table
//!
//! [`Attr`] (none, and the spellings of the two attributes) × [`Target`] (a
//! C#-style class of `string`, one of `Hashtable`) × [`Placement`] (the same
//! file, an unopened nested module, an earlier file opened, an earlier file
//! of a shared namespace, an earlier file unopened). Every project calls
//! both extensions' names: `"abc".Equals(1)` (a literal receiver, which the
//! resolver needs no name for) and `(asTable x).ContainsKey(1)`.
//!
//! # The properties
//!
//! 1. Certain-implies-exact soundness in every file.
//! 2. With no attribute, both calls commit: the abbreviation alone brings no
//!    extension, so declining there is availability lost.
//!    With either attribute, neither call commits, and the literal one
//!    carries `ExtensionInScope`: an attributed abbreviation's target is not
//!    enumerated, so no name is known absent.
//! 3. Where FCS binds a call to the extension (it types it `int64` where the
//!    intrinsic is `bool`) is pinned ([`fcs_binds`]), so a cell that stops
//!    discriminating is seen.

use crate::common::ext_scope::{Call, check};
use borzoi_oracle_harness::par_map::par_map;

/// The attribute on the abbreviation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Attr {
    None,
    AutoOpen,
    AutoOpenLong,
    /// `[<AO>]` where `type AO = AutoOpenAttribute`.
    AutoOpenAliased,
    ExtensionQualified,
    /// `[<Extension>]` after `open System.Runtime.CompilerServices`.
    ExtensionOpened,
}

impl Attr {
    const ALL: [Attr; 6] = [
        Attr::None,
        Attr::AutoOpen,
        Attr::AutoOpenLong,
        Attr::AutoOpenAliased,
        Attr::ExtensionQualified,
        Attr::ExtensionOpened,
    ];

    /// The lines declaring the abbreviation `A` of `target`.
    fn decl(self, target: &str) -> Vec<String> {
        let attr: &[&str] = match self {
            Attr::None => &[],
            Attr::AutoOpen => &["[<AutoOpen>]"],
            Attr::AutoOpenLong => &["[<AutoOpenAttribute>]"],
            Attr::AutoOpenAliased => &["type AO = AutoOpenAttribute", "[<AO>]"],
            Attr::ExtensionQualified => &["[<System.Runtime.CompilerServices.Extension>]"],
            Attr::ExtensionOpened => &["open System.Runtime.CompilerServices", "[<Extension>]"],
        };
        attr.iter()
            .map(|l| (*l).to_string())
            .chain(std::iter::once(format!("type A = {target}")))
            .collect()
    }
}

/// The extension class the abbreviation names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Target {
    /// `ExtUniverse.Str.StrExts`: `Equals(this string, int)`.
    Str,
    /// `ExtUniverse.Cs.CsExts`: `ContainsKey(this Hashtable, int)`.
    Cs,
}

impl Target {
    fn path(self) -> &'static str {
        match self {
            Target::Str => "ExtUniverse.Str.StrExts",
            Target::Cs => "ExtUniverse.Cs.CsExts",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Placement {
    OwnTop,
    OwnNestedUnopened,
    EarlierOpened,
    EarlierSharedNamespace,
    EarlierUnopened,
}

impl Placement {
    const ALL: [Placement; 5] = [
        Placement::OwnTop,
        Placement::OwnNestedUnopened,
        Placement::EarlierOpened,
        Placement::EarlierSharedNamespace,
        Placement::EarlierUnopened,
    ];
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

fn indent(lines: Vec<String>) -> Vec<String> {
    lines.into_iter().map(|l| format!("    {l}")).collect()
}

/// The project: an optional `Ext.fs`, then `Use.fs`, whose last bindings are
/// [`CALLS`]. `asTable` types the `Hashtable` receiver ahead of every `open`.
fn sources(attr: Attr, target: Target, placement: Placement) -> Vec<(&'static str, String)> {
    let decl = attr.decl(target.path());
    let preamble = "let asTable (h: System.Collections.Hashtable) = h".to_string();
    let calls: Vec<String> = CALLS
        .iter()
        .map(|c| format!("let {} x = {}", c.binder, c.text))
        .collect();
    let mut out = Vec::new();
    let use_lines: Vec<String> = match placement {
        Placement::OwnTop => {
            let mut u = vec!["module Use".to_string(), preamble];
            u.extend(decl);
            u.extend(calls);
            u
        }
        Placement::OwnNestedUnopened => {
            let mut u = vec!["module Use".to_string(), preamble, "module N =".into()];
            u.extend(indent(decl));
            u.extend(calls);
            u
        }
        Placement::EarlierOpened | Placement::EarlierUnopened => {
            let mut e = vec!["module ExtLib".to_string()];
            e.extend(decl);
            out.push(("Ext.fs", e.join("\n") + "\n"));
            let mut u = vec!["module Use".to_string(), preamble];
            if placement == Placement::EarlierOpened {
                u.push("open ExtLib".into());
            }
            u.extend(calls);
            u
        }
        Placement::EarlierSharedNamespace => {
            let mut e = vec!["namespace Shared".to_string()];
            e.extend(decl);
            out.push(("Ext.fs", e.join("\n") + "\n"));
            let mut u = vec!["namespace Shared".to_string(), "module Use =".into()];
            u.extend(indent(std::iter::once(preamble).chain(calls).collect()));
            u
        }
    };
    out.push(("Use.fs", use_lines.join("\n") + "\n"));
    out
}

/// The cells where FCS binds a call to the abbreviated class's extension:
/// `(attr, target, placement)`, the call being the target's own. Every
/// attribute binds wherever the abbreviation is in scope, and nowhere else.
fn fcs_binds(attr: Attr, placement: Placement) -> bool {
    attr != Attr::None
        && matches!(
            placement,
            Placement::OwnTop | Placement::EarlierOpened | Placement::EarlierSharedNamespace
        )
}

#[test]
fn attributed_abbreviations_decline_every_call() {
    let mut cells = Vec::new();
    for attr in Attr::ALL {
        for target in [Target::Str, Target::Cs] {
            for placement in Placement::ALL {
                cells.push((attr, target, placement));
            }
        }
    }
    let results = par_map(cells.len(), |i| {
        let (attr, target, placement) = cells[i];
        check(&sources(attr, target, placement), &CALLS)
    });
    let mut failures = Vec::new();
    for (&(attr, target, placement), checked) in cells.iter().zip(&results) {
        let label = format!("{attr:?}/{target:?}/{placement:?}");
        for u in &checked.unsound {
            failures.push(format!("{label}: unsound: {u}"));
        }
        for (k, (call, outcome)) in CALLS.iter().zip(&checked.calls).enumerate() {
            if attr == Attr::None {
                if outcome.ours.is_none() || outcome.gated() {
                    failures.push(format!(
                        "{label}: `{}` should commit with no attribute; census {:?}",
                        call.text, outcome.census
                    ));
                }
            } else if k == 0 && !outcome.gated() {
                // The literal receiver needs no resolution, so the gate is
                // always what declines it.
                failures.push(format!(
                    "{label}: `{}` should carry ExtensionInScope; ours {:?}, census {:?}",
                    call.text, outcome.ours, outcome.census
                ));
            } else if outcome.ours.is_some() {
                // An `[<AutoOpen>]` abbreviation in scope may also bring a
                // static named `asTable`, so the resolver may decline the
                // receiver before the gate is asked; either way, no commit.
                failures.push(format!(
                    "{label}: `{}` should not commit; ours {:?}, census {:?}",
                    call.text, outcome.ours, outcome.census
                ));
            }
            let own_call = matches!((target, k), (Target::Str, 0) | (Target::Cs, 1));
            let binds = outcome.fcs.as_deref() == Some("System.Int64");
            let want = own_call && fcs_binds(attr, placement);
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
