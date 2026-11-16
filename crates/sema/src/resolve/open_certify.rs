//! Whether the extension-scope gate may enumerate an `open`: the **certified
//! domain** (#794 PR 2a-i).
//!
//! An `open` is enumerated only when its written path (`open A.B` or
//! `open global.A.B`) names exactly what it opens, with no relative or
//! shortened reading and no abbreviation in between, and:
//!
//! - on the **project** side, every interpretation the resolver found is a
//!   namespace reading or a project module at that path whose values the walk
//!   can list (no module abbreviation, no module whose values it hides);
//! - on the **assembly** side, the path names namespaces only: no top-level
//!   entity of any accessibility sits at any split of it, and no dropped type
//!   does. What the assemblies bring is then exactly the contents of the
//!   namespace at the written path, which the gate asks about directly
//!   ([`ExtensionView::extension_named_in_scope`]), whatever the resolver made
//!   of the path.
//!
//! Every other `open` is unenumerated and declines every call. The assembly
//! side is read only through an [`ExtensionView`], which holds no lookup
//! filtered by accessibility: name resolution's view of an assembly is the
//! public one, but a friend assembly's internal extension is in scope all the
//! same (`InternalsVisibleTo`), so [`certify`] cannot be handed anything that
//! answers from that view. `infer_assembly_extension_grid` holds the domain
//! to FCS over every `open` form, and to a visibility perturbation.

use crate::assembly_env::ExtensionView;

/// One interpretation of an `open`, as the resolver found it, carrying only
/// the project-side facts the domain reads.
#[derive(Debug, Clone, Copy)]
pub(super) enum Interpretation<'a> {
    /// A namespace reading (project and/or assembly) at `path`.
    Namespace { path: &'a [String] },
    /// A project module at `path`; `listable` when it is no abbreviation and
    /// the walk can list its values.
    ProjectModule { path: &'a [String], listable: bool },
    /// An assembly module (#794 PR 2b enumerates these).
    AssemblyModule,
}

/// What the resolver knows of one `open`.
#[derive(Debug, Clone)]
pub(super) struct OpenFacts<'a> {
    /// The path as written, `global.` stripped.
    pub(super) written: &'a [String],
    pub(super) interpretations: Vec<Interpretation<'a>>,
    /// The walk declined to read the path with certainty (an incomplete
    /// prefix, a dropped type the path names, a module only an auto-open
    /// lends a short name, an unmodelled assembly type).
    pub(super) walk_uncertain: bool,
}

/// The namespace whose assembly content an enumerated `open` brings, or
/// `None` when the `open` is outside the certified domain.
pub(super) fn certify(facts: &OpenFacts<'_>, assemblies: ExtensionView<'_>) -> Option<Vec<String>> {
    let written = facts.written;
    if written.is_empty() || facts.walk_uncertain || facts.interpretations.is_empty() {
        return None;
    }
    if !assemblies.names_namespaces_only(written)
        || assemblies.any_split_has_a_dropped_type(written)
    {
        return None;
    }
    let project_side_certain = facts.interpretations.iter().all(|i| match *i {
        Interpretation::Namespace { path } => path == written,
        Interpretation::ProjectModule { path, listable } => path == written && listable,
        Interpretation::AssemblyModule => false,
    });
    project_side_certain.then(|| written.to_vec())
}

#[cfg(test)]
mod tests {
    use super::{Interpretation, OpenFacts, certify};
    use crate::AssemblyEnv;

    fn segs(path: &str) -> Vec<String> {
        path.split('.').map(str::to_owned).collect()
    }

    #[test]
    fn only_a_written_path_read_at_itself_is_certified() {
        let env = AssemblyEnv::default();
        let view = env.extension_view();
        let written = segs("A.B");
        let other = segs("N.A.B");
        let facts = |interpretations, walk_uncertain| OpenFacts {
            written: written.as_slice(),
            interpretations,
            walk_uncertain,
        };
        let namespace = Interpretation::Namespace { path: &written };
        let module = Interpretation::ProjectModule {
            path: &written,
            listable: true,
        };
        assert_eq!(
            certify(&facts(vec![namespace, module], false), view),
            Some(written.clone())
        );
        // The namespace query is asked about the written path whichever arm
        // certified it.
        assert_eq!(
            certify(&facts(vec![module], false), view),
            Some(written.clone())
        );
        for refused in [
            facts(vec![], false),
            facts(vec![namespace], true),
            facts(vec![Interpretation::Namespace { path: &other }], false),
            facts(
                vec![Interpretation::ProjectModule {
                    path: &written,
                    listable: false,
                }],
                false,
            ),
            facts(vec![namespace, Interpretation::AssemblyModule], false),
        ] {
            assert_eq!(certify(&refused, view), None, "{refused:?}");
        }
    }
}
