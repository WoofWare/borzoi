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
//! - on the **assembly** side, the path names namespaces only: no entity of
//!   any accessibility sits at any split of it. What the assemblies bring is
//!   then exactly the contents of the namespace at the written path, which
//!   the gate asks about directly (the extension query),
//!   whatever the resolver made of the path;
//! - and every **other reading** F# could give the path holds nothing in the
//!   assemblies, of any accessibility. Unless the path is `global.`-rooted,
//!   FCS also reads it relative to each enclosing container and to each
//!   container an earlier `open` lent (the implicit opens included), and
//!   through the `[<AutoOpen>]` modules either holds. The resolver lists
//!   those readings through the public view, so a friend assembly's
//!   internal-only namespace or module at one is missing from its
//!   interpretations; [`certify`] asks the [`ExistenceSet`] about each
//!   instead ([`other_readings_hold_nothing`]). A module abbreviation at the
//!   path's head is a reading it cannot bound, and declines.
//!
//! Every other `open` is unenumerated and declines every call. The assembly
//! side is read only through an [`ExistenceSet`]: what the assemblies'
//! raw metadata declares at every accessibility, behind a module boundary
//! that holds no reference to the env. Name resolution's view of an assembly
//! is the public one, but a friend assembly's internal extension is in scope
//! all the same (`InternalsVisibleTo`), so [`certify`] cannot be handed
//! anything that answers from that view. `infer_assembly_extension_grid` holds the domain
//! to FCS over every `open` form, and to a visibility perturbation.

use crate::assembly_env::existence::ExistenceSet;

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
    /// The path was written `global.`-rooted, so F# reads it at the root
    /// alone.
    pub(super) rooted: bool,
    /// The path's head is a module abbreviation in scope.
    pub(super) head_is_alias: bool,
    /// Every container an earlier `open` in scope lent its contents' short
    /// names from, the implicit opens included.
    pub(super) open_prefixes: Vec<&'a [String]>,
    /// The enclosing containers, outermost first: namespace segments, then
    /// module segments.
    pub(super) container_path: &'a [String],
}

/// The namespace whose assembly content an enumerated `open` brings, or
/// `None` when the `open` is outside the certified domain.
pub(super) fn certify(facts: &OpenFacts<'_>, assemblies: &ExistenceSet) -> Option<Vec<String>> {
    let written = facts.written;
    if written.is_empty() || facts.walk_uncertain || facts.interpretations.is_empty() {
        return None;
    }
    if !assemblies.names_namespaces_only(written) {
        return None;
    }
    let project_side_certain = facts.interpretations.iter().all(|i| match *i {
        Interpretation::Namespace { path } => path == written,
        Interpretation::ProjectModule { path, listable } => path == written && listable,
        Interpretation::AssemblyModule => false,
    });
    (project_side_certain && other_readings_hold_nothing(facts, assemblies))
        .then(|| written.to_vec())
}

/// Whether no reading of the written path but the root one can find
/// anything in the assemblies, whatever its accessibility: for each base a
/// relative reading starts from (each container an `open` lent, and each
/// enclosing container), nothing at the base followed by the path, and no
/// `[<AutoOpen>]` chain under the base lending the path's head as a short
/// name. Every enclosing
/// container is a base, the outer namespaces included, which bounds FCS's
/// reading from above; nothing at a container means nothing under it, so
/// the walk stops at the first.
fn other_readings_hold_nothing(facts: &OpenFacts<'_>, assemblies: &ExistenceSet) -> bool {
    if facts.rooted {
        return true;
    }
    if facts.head_is_alias {
        return false;
    }
    let written = facts.written;
    let head = &written[0];
    let reading_holds_nothing = |base: &[String]| {
        let mut full = base.to_vec();
        full.extend_from_slice(written);
        assemblies.holds_nothing_at(&full) && !assemblies.lends_a_short_name_under(base, head)
    };
    if !facts
        .open_prefixes
        .iter()
        .all(|base| reading_holds_nothing(base))
    {
        return false;
    }
    for k in 1..=facts.container_path.len() {
        let base = &facts.container_path[..k];
        if assemblies.holds_nothing_at(base) {
            break;
        }
        if !reading_holds_nothing(base) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{Interpretation, OpenFacts, certify};
    use crate::assembly_env::existence::ExistenceSet;

    fn segs(path: &str) -> Vec<String> {
        path.split('.').map(str::to_owned).collect()
    }

    #[test]
    fn only_a_written_path_read_at_itself_is_certified() {
        let set = ExistenceSet::default();
        let view = &set;
        let written = segs("A.B");
        let other = segs("N.A.B");
        let facts = |interpretations, walk_uncertain| OpenFacts {
            written: written.as_slice(),
            interpretations,
            walk_uncertain,
            rooted: false,
            head_is_alias: false,
            open_prefixes: Vec::new(),
            container_path: &[],
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
