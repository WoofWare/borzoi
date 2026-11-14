//! Which types F# seals, so that a use of a value taking one is not
//! loosened against it.

use super::*;

/// Whether `path` names a sealed BCL primitive: the numeric primitives,
/// `Boolean`, `String`, `Char`, `Decimal` and `unit`. Every scalar type
/// [`literal_ty`] produces is one, which a unit test asserts.
pub(super) fn is_sealed_primitive(path: &[&str]) -> bool {
    matches!(
        path,
        ["System", "Int32"]
            | ["System", "SByte"]
            | ["System", "Byte"]
            | ["System", "Int16"]
            | ["System", "UInt16"]
            | ["System", "UInt32"]
            | ["System", "Int64"]
            | ["System", "UInt64"]
            | ["System", "IntPtr"]
            | ["System", "UIntPtr"]
            | ["System", "Double"]
            | ["System", "Single"]
            | ["System", "Decimal"]
            | ["System", "String"]
            | ["System", "Char"]
            | ["System", "Boolean"]
            | ["Microsoft", "FSharp", "Core", "Unit"]
    )
}

/// F#'s `unit`, as FCS names it.
pub(super) const UNIT: &str = "Microsoft.FSharp.Core.Unit";

/// [`UNIT`]'s segments.
pub(super) const UNIT_PATH: [&str; 4] = ["Microsoft", "FSharp", "Core", "Unit"];

/// `System.Object`, the bound of a loosening every type meets.
pub(super) const OBJECT_PATH: [&str; 2] = ["System", "Object"];

/// Whether FCS treats `ty` as **sealed** (`isSealedTy`), so that a use of a
/// value taking it does not loosen it ([`Gen::loosened`]). `false` whenever it
/// cannot be shown, which loosens more than FCS does and so only declines.
///
/// A type variable is not a reference type, so it is sealed, as are function,
/// tuple and array types, `unit`, value types, and F# unions, records and
/// exceptions. An IL class is sealed by its flag (an F# class carries the flag
/// exactly when it is `[<Sealed>]`); an interface never is.
pub(super) fn is_sealed(env: &AssemblyEnv, tys: &TyTable, ty: Ty) -> bool {
    match tys.kind(ty) {
        TyKind::Var(_)
        | TyKind::Param(_)
        | TyKind::Fun { .. }
        | TyKind::Tuple(_)
        | TyKind::Array { .. } => true,
        // Whether a project type is sealed turns on its kind and attributes,
        // which are not read.
        TyKind::Project { .. } => false,
        TyKind::Named { path, args } => {
            if (args.is_empty() && is_sealed_primitive(&path.segments_in(env.names())))
                || tys.is_named(env.names(), ty, &UNIT_PATH)
            {
                return true;
            }
            let path = path.spelled(env.names());
            let Some((name, namespace)) = path.split_last() else {
                return false;
            };
            // A generic application names its type by its compiled path, which
            // the source-name index does not hold for a renamed one
            // (`FSharpList`).
            let handle = if args.is_empty() {
                env.lookup_type_if_certain(namespace, name, 0)
            } else {
                env.generic_type_at_compiled_path(namespace, name, args.len())
            };
            let Some(handle) = handle else {
                return false;
            };
            let entity = env.entity(handle);
            match entity.kind {
                EntityKind::Struct
                | EntityKind::Enum
                | EntityKind::Union
                | EntityKind::Record
                | EntityKind::Exception
                | EntityKind::Delegate => true,
                EntityKind::Class => entity.is_sealed,
                EntityKind::Interface
                | EntityKind::Module
                | EntityKind::Abbreviation
                | EntityKind::Measure => false,
            }
        }
    }
}
