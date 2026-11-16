//! The extension-absence gate an overloaded call consults ([`ExtensionScope`]).

use super::*;
use crate::assembly_env::ExtensionView;
use crate::resolve::{ExtensionNames, NamesUnknowable};

/// The OV-6 overload engine's **extension-absence gate** (see
/// `docs/overload-resolution-plan.md` §4.1(4) and
/// `docs/extension-scope-enumeration-plan.md`). An overloaded call `recv.M(args)`
/// may commit an *intrinsic* winner only when no in-scope F#-style or C#-style
/// extension member **named `M`** could join FCS's method group (the P15 landmine:
/// an applicable extension can beat an applicable intrinsic on any betterness rule
/// before rule 10).
///
/// An in-scope extension competes only within its own name's group (probed —
/// the enumeration plan §1), so each source is asked about the name:
///
/// - **Project side — [`Self::project`].** The extension-member names this file
///   and every preceding Compile-order file declare
///   ([`ResolvedFile::extension_names`], [`ResolvedFile::preceding_extension_names`]):
///   augmentation members, members under an attribute that may be
///   `[<Extension>]`, or every name when a file declares something whose names
///   cannot be read (an attributed type abbreviation, a recovered parse, a `#r`).
///   Scope-blind: a project extension in a module nobody opens still names its
///   call, and position-blind: a name a file's damaged text spells names every
///   call in it.
/// - **Assembly side — name-keyed (EX-1/EX-2).** The env's auto-open surfaces,
///   the file's in-scope namespace chain, and its explicit `open <namespace>`
///   targets ([`Self::in_scope_namespaces`]), asked through
///   [`AssemblyEnv::extension_named_in_scope`] by call shape (`is_static`).
/// - **`open`s.** An `open` inside the certified domain (see the resolver's
///   open classification) is enumerated: an opened namespace joins the
///   assembly side above, and a project module or namespace brings nothing
///   the project side does not already hold. Every other `open`
///   ([`Self::unenumerated_open`]: an assembly module, an `open type`, a
///   relative or shortened reading, a module abbreviation, an unresolved or
///   uncertain path) declines every call. While a project reference is not
///   built ([`AssemblyEnv::references_not_built`]), a project `open` declines
///   every call too: the unbuilt assembly may share the project's namespaces.
///   An `open` in text the parser recovered from counts as both kinds, since
///   FCS may recover it to either.
///
/// A source whose names cannot be computed is a wholesale defer, so no
/// refinement can license a commit a full name enumeration would not. The
/// [`Default`] scope (no source, no opened namespace, nothing unknowable) is used
/// by in-crate unit tests that drive [`Gen`] without a file.
#[derive(Default)]
pub(crate) struct ExtensionScope {
    /// The project's extension-member names: what this file and every
    /// preceding file may declare, their damaged text included.
    project: ExtensionNames,
    /// Some explicit `open` in the file brings an extension surface the resolver
    /// does not enumerate ([`ResolvedFile::opens_unenumerated`]).
    unenumerated_open: bool,
    /// Some explicit `open` in the file names a project module or namespace
    /// ([`ResolvedFile::opens_project`]).
    project_open: bool,
    /// The file's **in-scope namespace chain plus its explicit `open <namespace>`
    /// targets**: the always-in-scope root `[]`, each declared namespace and its
    /// ancestors, and every assembly namespace an `open` brought in (EX-2,
    /// [`ResolvedFile::open_extension_namespaces`]). A referenced-assembly extension
    /// declared in any of these is in scope — an enclosing namespace needs no
    /// `open`, an `open`ed one is opened — so the assembly-side gate is asked the
    /// same query about all of them per call.
    in_scope_namespaces: Vec<Vec<String>>,
}

/// Which of the extension-scope gate's inputs declined a call (what
/// `ExtensionScope::decline` answers).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateInput {
    /// A project file declares something whose extension names cannot be
    /// read, so no name is known absent.
    ProjectUnknowable(NamesUnknowable),
    /// A project file declares an extension member, or a member that may be
    /// one, of the call's name.
    ProjectName,
    /// An `open` the resolver does not enumerate.
    OpenNotEnumerated,
    /// A project `open` while a project reference is not built: the
    /// assembly it will be may share the opened namespace.
    ProjectOpenReferencesNotBuilt,
    /// A referenced assembly's extension of the call's name is in scope, or
    /// its in-scope surface cannot be enumerated.
    AssemblyInScope,
}

impl ExtensionScope {
    pub(crate) fn of(resolved: &ResolvedFile) -> ExtensionScope {
        // The root must be included explicitly — `namespace_paths` omits it, and it
        // is always in scope (so `module M` sees a global `[<Extension>]`). The
        // file's explicit `open <namespace>` targets (EX-2) join it: opening a
        // namespace makes its extensions in-scope exactly as an enclosing namespace
        // does, so the same per-namespace query serves both.
        let in_scope_namespaces = std::iter::once(Vec::new())
            .chain(resolved.namespace_paths().iter().cloned())
            .chain(resolved.open_extension_namespaces().iter().cloned())
            .collect();
        let mut project = resolved.preceding_extension_names().clone();
        project.absorb(&resolved.extension_names());
        ExtensionScope {
            project,
            unenumerated_open: resolved.opens_unenumerated(),
            project_open: resolved.opens_project(),
            in_scope_namespaces,
        }
    }

    /// Which input, if any, declines a call of an extension member **named
    /// `name`** in the file: `None` exactly when every source
    /// provably lacks the name, the precondition for committing an intrinsic
    /// overload of that name. `is_static` selects the call shape, since FCS
    /// takes only *instance* extensions into a value receiver's group and only
    /// *static* ones into a type-qualified call's.
    pub(crate) fn decline(
        &self,
        assemblies: ExtensionView<'_>,
        name: &str,
        is_static: bool,
    ) -> Option<GateInput> {
        if let Some(why) = self.project.unknowable() {
            return Some(GateInput::ProjectUnknowable(why));
        }
        if self.project.may_have(name, is_static) {
            return Some(GateInput::ProjectName);
        }
        if self.project_open && assemblies.references_not_built() {
            return Some(GateInput::ProjectOpenReferencesNotBuilt);
        }
        if self.unenumerated_open {
            return Some(GateInput::OpenNotEnumerated);
        }
        if assemblies.extension_named_in_scope(&self.in_scope_namespaces, name, is_static) {
            return Some(GateInput::AssemblyInScope);
        }
        None
    }

    /// Whether an extension member named `name` is provably absent from the
    /// file's in-scope extension surface ([`Self::decline`] finds no input).
    pub(crate) fn absent(
        &self,
        assemblies: ExtensionView<'_>,
        name: &str,
        is_static: bool,
    ) -> bool {
        self.decline(assemblies, name, is_static).is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::{ExtensionScope, GateInput};
    use crate::AssemblyEnv;
    use crate::resolve::{ExtensionNames, NamesUnknowable};

    #[test]
    fn extension_scope_decline_decision_logic() {
        // With an empty env (no referenced assembly can contribute anything)
        // and no project source, every name is absent.
        let env = AssemblyEnv::default();
        let extension_free = ExtensionScope::default();
        assert_eq!(
            extension_free.decline(env.extension_view(), "Substring", false),
            None
        );
        assert_eq!(
            extension_free.decline(env.extension_view(), "Compare", true),
            None
        );

        // Project names decline their own name, and only it.
        let mut instance = crate::hash::HashSet::default();
        instance.insert("Substring".to_string());
        let named = ExtensionScope {
            project: ExtensionNames::Known {
                instance,
                statics: crate::hash::HashSet::default(),
            },
            ..ExtensionScope::default()
        };
        assert_eq!(
            named.decline(env.extension_view(), "Substring", false),
            Some(GateInput::ProjectName)
        );
        assert_eq!(
            named.decline(env.extension_view(), "Substring", true),
            None,
            "an instance name"
        );
        assert_eq!(named.decline(env.extension_view(), "Trim", false), None);

        // Unknowable project names decline every name, saying why.
        let unknowable = ExtensionScope {
            project: ExtensionNames::Unknowable(NamesUnknowable::HashReference),
            ..ExtensionScope::default()
        };
        assert_eq!(
            unknowable.decline(env.extension_view(), "NoSourceDeclaresThis", false),
            Some(GateInput::ProjectUnknowable(NamesUnknowable::HashReference))
        );

        // An `open` the resolver does not enumerate declines every name.
        let unenumerated = ExtensionScope {
            unenumerated_open: true,
            ..ExtensionScope::default()
        };
        assert_eq!(
            unenumerated.decline(env.extension_view(), "NoSourceDeclaresThis", false),
            Some(GateInput::OpenNotEnumerated)
        );
        // A project `open` declines only under an unbuilt project reference.
        let mut unbuilt = AssemblyEnv::default();
        unbuilt.mark_references_not_built();
        let project_open = ExtensionScope {
            project_open: true,
            ..ExtensionScope::default()
        };
        assert_eq!(
            project_open.decline(env.extension_view(), "Substring", false),
            None
        );
        assert_eq!(
            project_open.decline(unbuilt.extension_view(), "Substring", false),
            Some(GateInput::ProjectOpenReferencesNotBuilt)
        );
    }
}
