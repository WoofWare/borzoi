//! The file-wide **unknowables** ([`Unknowables`]): the reasons the walk has
//! found, anywhere in the file so far, that some question about the whole
//! file has no enumerable answer.
//!
//! Each reason is raised where the walk meets the construct that makes it so,
//! and a raised reason stays raised for the rest of the file: there is
//! [`Unknowables::raise`] and no way to lower one. A reader asks
//! [`Unknowables::contains`], so a site that defers on a reason cannot read
//! a value that some later code reset.
//!
//! What a pass over the whole file decides before the walk starts is not an
//! unknowable the walk raises; it is a [`Prescan`](super::prescan::Prescan)
//! fact, which the walk borrows and cannot write.

/// One reason a file-wide question has no enumerable answer; see the
/// [module docs](self).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Unknowable {
    /// Some explicit `open` in the file lies outside the certified domain the
    /// resolver enumerates (an assembly module, an `open type`, a relative
    /// reading, a module abbreviation, an opaque, vetoed or dropped-path
    /// open), so the extension gate declines every call. File-global like
    /// [`Output::open_extension_namespaces`](crate::resolve::output::Output::open_extension_namespaces):
    /// an `open` in a nested module counts for the whole file.
    UnenumeratedSurface,
    /// Some explicit `open` in the file names a project module or namespace.
    /// The extensions it brings are the project's own, which the gate reads
    /// anyway; but under an unbuilt project reference (whose namespaces it may
    /// share) the gate keeps such an `open` as a wholesale decline.
    ProjectSurface,
    /// An earlier `namespace global` block of this file held an `open`. FCS
    /// carries what such an open brings into the blocks after it (probed: a
    /// later block's `Alpha.Color.Red` binds the opened module's `Alpha`
    /// over a same-file `namespace Alpha`), which the per-block open state
    /// does not model.
    GlobalBlockOpen,
}

impl Unknowable {
    /// Every reason, each once.
    #[cfg(test)]
    pub(super) const ALL: [Unknowable; 3] = [
        Unknowable::UnenumeratedSurface,
        Unknowable::ProjectSurface,
        Unknowable::GlobalBlockOpen,
    ];

    /// The reason's bit in an [`Unknowables`]. Distinct reasons have distinct
    /// discriminants (the compiler rejects a repeated one), so they have
    /// distinct bits.
    fn bit(self) -> u8 {
        1 << (self as u8)
    }
}

/// The set of reasons raised so far in the file; see the
/// [module docs](self).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Unknowables(u8);

impl Unknowables {
    /// Raise `reason` for the rest of the file.
    pub(super) fn raise(&mut self, reason: Unknowable) {
        self.0 |= reason.bit();
    }

    /// Whether `reason` has been raised.
    pub(super) fn contains(self, reason: Unknowable) -> bool {
        self.0 & reason.bit() != 0
    }
}

#[cfg(test)]
mod tests {
    use super::{Unknowable, Unknowables};
    use crate::{AssemblyEnv, ProjectItems, SyntaxRecovery, resolve_file};
    use borzoi_cst::parser::parse;
    use borzoi_cst::syntax::{AstNode, ImplFile};
    use proptest::prelude::*;

    /// The reasons resolving `src` alone raises.
    fn raised(src: &str) -> Vec<Unknowable> {
        let parsed = parse(src);
        let recovery = SyntaxRecovery::of(&parsed);
        let file = ImplFile::cast(parsed.root).expect("an impl file");
        let env = AssemblyEnv::default();
        let rf = resolve_file(&file, &ProjectItems::default(), &env, &recovery);
        assert_eq!(
            rf.opens_unenumerated(),
            rf.unknowables.contains(Unknowable::UnenumeratedSurface)
        );
        assert_eq!(
            rf.opens_project(),
            rf.unknowables.contains(Unknowable::ProjectSurface)
        );
        Unknowable::ALL
            .into_iter()
            .filter(|&r| rf.unknowables.contains(r))
            .collect()
    }

    /// Each construct raises its own reason and no other: a raise site
    /// that names the wrong reason moves a row. The public accessors agree
    /// with the set they read.
    #[test]
    fn each_construct_raises_exactly_its_reason() {
        let rows: &[(&str, &[Unknowable])] = &[
            ("module M\nlet x = 1\n", &[]),
            (
                "module M\nmodule N =\n    let y = 1\nopen M.N\nlet x = 1\n",
                &[Unknowable::ProjectSurface],
            ),
            // A relative `open` is outside the certified domain.
            (
                "module M\nmodule N =\n    let y = 1\nopen N\nlet x = 1\n",
                &[Unknowable::UnenumeratedSurface, Unknowable::ProjectSurface],
            ),
            (
                "module M\nopen Nowhere\nlet x = 1\n",
                &[Unknowable::UnenumeratedSurface],
            ),
            (
                "module M\nopen type Nowhere.T\nlet x = 1\n",
                &[Unknowable::UnenumeratedSurface],
            ),
            (
                "namespace global\nopen System\ntype U = int\nnamespace A\ntype V = int\n",
                // In an empty env the `open` is unenumerable too.
                &[Unknowable::UnenumeratedSurface, Unknowable::GlobalBlockOpen],
            ),
        ];
        for (src, expected) in rows {
            assert_eq!(raised(src), *expected, "{src:?}");
        }
    }

    fn reason() -> impl Strategy<Value = Unknowable> {
        proptest::sample::select(Unknowable::ALL.to_vec())
    }

    proptest! {
        /// The set holds exactly the reasons raised into it, after every
        /// raise: raising one reason raises no other, and lowers none.
        #[test]
        fn the_set_holds_exactly_the_reasons_raised(
            raised in prop::collection::vec(reason(), 0..12),
        ) {
            let mut set = Unknowables::default();
            for (i, &r) in raised.iter().enumerate() {
                set.raise(r);
                for probe in Unknowable::ALL {
                    prop_assert_eq!(
                        set.contains(probe),
                        raised[..=i].contains(&probe),
                        "after raising {:?}, {:?}",
                        &raised[..=i],
                        probe
                    );
                }
            }
        }
    }
}
