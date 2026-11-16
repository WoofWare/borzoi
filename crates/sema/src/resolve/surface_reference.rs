//! The `surface-reference` check: every [`resolve_file`](super::resolve_file)
//! also runs the surface walk ([`surface_file`](super::surface_file)) on the
//! same file and entering state, and panics unless the two surfaces are equal
//! (D3 of `docs/resolve-what-a-request-reads-plan.md`).
//!
//! Every caller of `resolve_file` under the feature is then an oracle for the
//! property: the corpus sweeps check each file in isolation, the project folds
//! check each file against its real entering state, and the generated grids
//! and projects check what they generate.

use borzoi_cst::syntax::{AstNode, ImplFile};

use super::model::{FileSurface, ProjectItems, ResolvedFile};
use crate::AssemblyEnv;
use crate::recovery::SyntaxRecovery;

/// Panic, naming each field that differs, unless the surface walk of `file`
/// publishes `full`'s surface.
pub(super) fn assert_surface_walk_agrees(
    file: &ImplFile,
    preceding: &ProjectItems,
    assemblies: &AssemblyEnv,
    recovery: &SyntaxRecovery,
    full: &ResolvedFile,
) {
    let surface = super::surface_file(file, preceding, assemblies, recovery);
    if surface == full.surface {
        return;
    }
    let fields = differing_fields(&full.surface, &surface);
    let text = file.syntax().text().to_string();
    let head: String = text.chars().take(200).collect();
    panic!(
        "the surface walk's surface differs from the full walk's in {fields:#?}\n\
         file ({} bytes) begins:\n{head}",
        text.len()
    );
}

/// Each field of the two surfaces that differs, with both values. Exhaustive,
/// so a field added to [`FileSurface`] is a compile error here until it is
/// compared.
fn differing_fields(full: &FileSurface, surface: &FileSurface) -> Vec<String> {
    let FileSurface {
        defs,
        own_type_simple_names,
        placed_types,
        unplaced_types,
        unplaced_type_places,
        own_module_simple_names,
        contributions,
        declares_core_attribute_alias,
        extension_names,
        exports,
        item_base,
        export_decls,
        sig_screen,
        sig_exports,
        damage,
    } = full;
    let mut out = Vec::new();
    macro_rules! compare {
        ($($field:ident),* $(,)?) => {$(
            if *$field != surface.$field {
                out.push(format!(
                    "{}:\n  full:    {:?}\n  surface: {:?}",
                    stringify!($field),
                    $field,
                    surface.$field
                ));
            }
        )*};
    }
    compare!(
        defs,
        own_type_simple_names,
        placed_types,
        unplaced_types,
        unplaced_type_places,
        own_module_simple_names,
        contributions,
        declares_core_attribute_alias,
        extension_names,
        exports,
        item_base,
        export_decls,
        sig_screen,
        sig_exports,
        damage,
    );
    out
}
