//! The assemblies one assembly names as its **friends**: what its
//! `[<assembly: InternalsVisibleTo>]` attributes say, read from the raw
//! manifest attributes with no projection in between.
//!
//! FCS grants a referencing assembly the internals of a referenced one when
//! some such attribute names it (`AddNonLocalCcu`,
//! `src/Compiler/Checking/CheckDeclarations.fs:325`): every argument goes
//! through `System.Reflection.AssemblyName(arg).Name`, compared ordinally with
//! the referencing assembly's name, and an argument that does not parse names
//! nobody. The arguments come from `GetInternalsVisibleToAttributes`
//! (`src/Compiler/Driver/CompilerImports.fs:1140`): the manifest's custom
//! attributes whose constructor's declaring type is the non-nested type
//! named `System.Runtime.CompilerServices.InternalsVisibleToAttribute`, in any
//! scope (`classifyILAttrib`, `TypedTreeOps.Attributes.fs:153`), with a
//! single string argument (`TryFindInternalsVisibleToAttr`, line 1257: no
//! argument, or a null one, contributes nothing).
//!
//! What a consumer may conclude from [`FriendDeclarations`] is certain only
//! in one direction per entry. A [`FriendEntry::Named`] name is exactly what
//! `AssemblyName(..).Name` returns for its argument, or the argument does not
//! parse and names nobody; so "no entry names B" holds for FCS too. Every
//! attribute the reader cannot read that far is a [`FriendEntry::Unread`],
//! which may name anyone.

use crate::reader::{EnumWidths, FixedArg, Image};

/// What an assembly's `InternalsVisibleTo` attributes name.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FriendDeclarations {
    /// One per attribute that is, or may be, an `InternalsVisibleTo`, in
    /// manifest order. Empty when the assembly provably names no friend.
    pub entries: Vec<FriendEntry>,
}

/// One attribute that is, or may be, an `InternalsVisibleTo`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FriendEntry {
    /// An `InternalsVisibleTo` naming this simple assembly name, or naming
    /// nobody (an argument `AssemblyName` rejects): never another name.
    Named(String),
    /// An attribute that may be an `InternalsVisibleTo` naming any assembly,
    /// and why the reader cannot say which.
    Unread(String),
}

impl FriendDeclarations {
    /// A declaration set nothing could be read of: it may name anyone.
    pub fn unread(why: impl Into<String>) -> Self {
        Self {
            entries: vec![FriendEntry::Unread(why.into())],
        }
    }
}

/// The simple name `AssemblyName(arg).Name` gives `arg`, when `arg` is in the
/// certified spelling: its text up to the first comma is non-empty and made
/// of ASCII letters, digits, `_`, `.` and `-`. Such a token holds nothing the
/// parser rewrites (no quote, escape or white space), so the parser either
/// returns it as the name or rejects the whole argument, whatever follows
/// the comma. Any other spelling is `None`: the parser may read a name off
/// it that the token does not show.
pub fn certified_simple_name(arg: &str) -> Option<&str> {
    let token = arg.split_once(',').map_or(arg, |(token, _)| token);
    let certified = !token.is_empty()
        && token
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'));
    certified.then_some(token)
}

/// The attribute's full name, as `classifyILAttrib` matches it.
const IVT_FULL_NAME: &str = "System.Runtime.CompilerServices.InternalsVisibleToAttribute";

/// Read the friend declarations of `image`'s manifest.
pub(crate) fn read(image: &Image) -> FriendDeclarations {
    let widths = EnumWidths::new();
    let mut entries = Vec::new();
    for raw in &image.assembly_attributes {
        let owner = match image.attribute_owning_type(raw) {
            Ok(owner) => owner,
            Err(e) => {
                entries.push(FriendEntry::Unread(format!(
                    "an assembly attribute's type cannot be named ({e:?})"
                )));
                continue;
            }
        };
        // FCS joins the namespace and name before comparing
        // (`readBlobHeapAsTypeName`), so the split between them is not part of
        // the match. A nested owner is not one FCS classifies, but reading
        // one as a declaration only adds a name that may be a friend.
        let joined = if owner.namespace.is_empty() {
            owner.name.clone()
        } else {
            format!("{}.{}", owner.namespace, owner.name)
        };
        if joined != IVT_FULL_NAME {
            continue;
        }
        let decoded = match image.decode_attribute(raw, &widths) {
            Ok(decoded) => decoded,
            Err(e) => {
                entries.push(FriendEntry::Unread(format!(
                    "an InternalsVisibleTo blob does not decode ({e:?})"
                )));
                continue;
            }
        };
        match decoded.fixed_args.as_slice() {
            [FixedArg::String(Some(arg))] => entries.push(match certified_simple_name(arg) {
                Some(name) => FriendEntry::Named(name.to_string()),
                None => FriendEntry::Unread(format!(
                    "an InternalsVisibleTo argument outside the certified spelling ({arg:?})"
                )),
            }),
            // `TryFindInternalsVisibleToAttr` reads nothing from either.
            [] | [FixedArg::String(None)] => {}
            other => entries.push(FriendEntry::Unread(format!(
                "an InternalsVisibleTo constructor of unexpected arguments ({other:?})"
            ))),
        }
    }
    FriendDeclarations { entries }
}

#[cfg(test)]
mod tests {
    use super::certified_simple_name;

    #[test]
    fn the_certified_spelling_is_the_token_before_the_first_comma() {
        assert_eq!(certified_simple_name("Lib.Tests"), Some("Lib.Tests"));
        assert_eq!(
            certified_simple_name("Lib.Tests, PublicKey=0024000004800000"),
            Some("Lib.Tests")
        );
        assert_eq!(certified_simple_name("a-b_c.9"), Some("a-b_c.9"));
        for outside in [
            "",
            ",PublicKey=00",
            " Lib",
            "Lib ",
            "\"Lib\"",
            "Li\\,b",
            "Lib\t",
            "Lïb",
            "Lib=1",
        ] {
            assert_eq!(certified_simple_name(outside), None, "{outside:?}");
        }
    }
}
