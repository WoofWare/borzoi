//! The extension-absence gate an overloaded call consults ([`ExtensionScope`]).

use super::*;
use crate::resolve::{Damage, ExtensionNames, NamesUnknowable};
use borzoi_cst::syntax::TextSize;

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
///   call. If the parser recovered from this file, what its damaged tail may
///   declare ([`Self::own_damage`]) joins them for the calls it can reach.
/// - **Assembly side — name-keyed (EX-1/EX-2).** The env's auto-open surfaces,
///   the file's in-scope namespace chain, and its explicit `open <namespace>`
///   targets ([`Self::in_scope_namespaces`]), asked through
///   [`AssemblyEnv::extension_named_in_scope`] by call shape (`is_static`).
/// - **`open`s the resolver could not name-key (EX-2 ⇒ [`Self::opens_unknowable`]).**
///   Still presence-based: every call in the file defers (#794 PR 2).
///
/// A source whose names cannot be computed is a wholesale defer, so no
/// refinement can license a commit a full name enumeration would not. The
/// [`Default`] scope (no source, no opened namespace, nothing unknowable) is used
/// by in-crate unit tests that drive [`Gen`] without a file.
#[derive(Default)]
pub(crate) struct ExtensionScope {
    /// The project's extension-member names: what this file's tree and every
    /// preceding file declare (a preceding file's damage included).
    project: ExtensionNames,
    /// What this file's damaged tail may declare, if the parser recovered from
    /// it: it reaches only the calls at or after [`Damage::from`].
    own_damage: Option<Damage>,
    /// Some explicit `open` in the file brings an extension surface the resolver
    /// could not name-key (EX-2): a project module/namespace, an assembly module /
    /// `open type`, or an opaque / vetoed / dropped-path open. Presence-based —
    /// every commit defers when set — and set straight from
    /// [`ResolvedFile::open_extension_unknowable`].
    opens_unknowable: bool,
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
    /// An `open` whose extension surface the resolver does not enumerate.
    OpenNotEnumerated,
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
        project.absorb(resolved.extension_names());
        ExtensionScope {
            project,
            own_damage: None,
            opens_unknowable: resolved.open_extension_unknowable(),
            in_scope_namespaces,
        }
    }

    /// [`Self::of`] the file whose tree is `root`, with what its damaged tail
    /// may declare if the parser recovered from it.
    pub(crate) fn of_tree(resolved: &ResolvedFile, root: &SyntaxNode) -> ExtensionScope {
        ExtensionScope {
            own_damage: crate::resolve::damage(root, resolved.recovery()),
            ..ExtensionScope::of(resolved)
        }
    }

    /// Which input, if any, declines a call of an extension member **named
    /// `name`** at offset `at` of the file: `None` exactly when every source
    /// provably lacks the name, the precondition for committing an intrinsic
    /// overload of that name. `is_static` selects the call shape, since FCS
    /// takes only *instance* extensions into a value receiver's group and only
    /// *static* ones into a type-qualified call's.
    pub(crate) fn decline(
        &self,
        env: &AssemblyEnv,
        name: &str,
        is_static: bool,
        at: TextSize,
    ) -> Option<GateInput> {
        if let Some(why) = self.project.unknowable() {
            return Some(GateInput::ProjectUnknowable(why));
        }
        if self.project.may_have(name, is_static) {
            return Some(GateInput::ProjectName);
        }
        if let Some(damage) = self.own_damage.as_ref().filter(|d| d.from <= at) {
            if let Some(why) = damage.names.unknowable() {
                return Some(GateInput::ProjectUnknowable(why));
            }
            if damage.names.may_have(name, is_static) {
                return Some(GateInput::ProjectName);
            }
        }
        if self.opens_unknowable {
            return Some(GateInput::OpenNotEnumerated);
        }
        if env.extension_named_in_scope(&self.in_scope_namespaces, name, is_static) {
            return Some(GateInput::AssemblyInScope);
        }
        None
    }

    /// Whether an extension member named `name` is provably absent from the
    /// file's in-scope extension surface ([`Self::decline`] finds no input).
    pub(crate) fn absent(
        &self,
        env: &AssemblyEnv,
        name: &str,
        is_static: bool,
        at: TextSize,
    ) -> bool {
        self.decline(env, name, is_static, at).is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::{ExtensionScope, GateInput};
    use crate::AssemblyEnv;
    use crate::resolve::{ExtensionNames, NamesUnknowable};
    use borzoi_cst::syntax::TextSize;

    #[test]
    fn extension_scope_decline_decision_logic() {
        // With an empty env (no referenced assembly can contribute anything)
        // and no project source, every name is absent.
        let env = AssemblyEnv::default();
        let extension_free = ExtensionScope::default();
        assert_eq!(
            extension_free.decline(&env, "Substring", false, TextSize::from(0)),
            None
        );
        assert_eq!(
            extension_free.decline(&env, "Compare", true, TextSize::from(0)),
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
            named.decline(&env, "Substring", false, TextSize::from(0)),
            Some(GateInput::ProjectName)
        );
        assert_eq!(
            named.decline(&env, "Substring", true, TextSize::from(0)),
            None,
            "an instance name"
        );
        assert_eq!(named.decline(&env, "Trim", false, TextSize::from(0)), None);

        // Unknowable project names decline every name, saying why.
        let unknowable = ExtensionScope {
            project: ExtensionNames::Unknowable(NamesUnknowable::HashReference),
            ..ExtensionScope::default()
        };
        assert_eq!(
            unknowable.decline(&env, "NoSourceDeclaresThis", false, TextSize::from(0)),
            Some(GateInput::ProjectUnknowable(NamesUnknowable::HashReference))
        );

        // An `open` the resolver could not name-key defers every name.
        let unknowable_open = ExtensionScope {
            opens_unknowable: true,
            ..ExtensionScope::default()
        };
        assert_eq!(
            unknowable_open.decline(&env, "NoSourceDeclaresThis", false, TextSize::from(0)),
            Some(GateInput::OpenNotEnumerated)
        );
        assert!(!unknowable_open.absent(&env, "Substring", false, TextSize::from(0)));
    }
}
