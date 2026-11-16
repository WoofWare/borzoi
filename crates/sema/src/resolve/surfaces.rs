//! The surface fold and the target fold (D4 of
//! `docs/resolve-what-a-request-reads-plan.md`).
//!
//! A later file reads only the surfaces of the files before it, so the state
//! entering any file is the fold's bookkeeping ([`FoldState::advance`])
//! replayed over those surfaces. [`ProjectSurfaces`] is that fold, and a full
//! walk of one file is asked of it ([`ProjectSurfaces::resolve_file`]): the
//! walks of the other files are never needed. [`resolve_target`] is the fold
//! to a file and the full walk of it.
//!
//! What each answers is what the cold full fold answers: a property over
//! generated projects (`tests/all/resolve_target_fold.rs`) holds every target,
//! every replayed walk and every `item_def` to it, and under the
//! `surface-reference` feature every cold full fold checks its own files
//! against the surface fold.

use std::sync::Arc;

use super::model::{FileSurface, ResolvedFile, item_def_in};
use super::{FoldOutput, FoldSlot, FoldState, ProjectFile, fold, signature_partners};
use crate::AssemblyEnv;
use crate::def::Def;

use super::model::Resolution;

/// The surfaces of a prefix of a project's Compile items, as the fold
/// computes them: each file's [`FileSurface`] against the state the files
/// before it leave.
///
/// The [`ProjectFile`] list is the caller's, as for [`ResolvedProject`]:
/// every method that takes `files` must be handed the list the fold folded.
///
/// [`ResolvedProject`]: super::ResolvedProject
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectSurfaces {
    files: Vec<Arc<FileSurface>>,
}

impl ProjectSurfaces {
    /// How many Compile items the fold covered.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether the fold covered no Compile item.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// The surface of the Compile item at `index`, if the fold covered it.
    pub fn surface(&self, index: usize) -> Option<&FileSurface> {
        self.files.get(index).map(|surface| &**surface)
    }

    /// [`ResolvedProject::item_def`](super::ResolvedProject::item_def), for
    /// the files this fold covered.
    pub fn item_def(&self, res: Resolution) -> Option<(usize, &Def)> {
        item_def_in(&self.files, res)
    }

    /// The full walk of `files[index]` against the state the surfaces before
    /// it leave: what the full fold of `files` publishes at `index`.
    ///
    /// # Panics
    ///
    /// Panics when `index` is past the fold's horizon (`index > self.len()`)
    /// or past `files`.
    pub fn resolve_file(
        &self,
        files: &[ProjectFile],
        index: usize,
        assemblies: &AssemblyEnv,
    ) -> ResolvedFile {
        assert!(
            index <= self.files.len(),
            "file {index} is past the surface fold's horizon ({})",
            self.files.len()
        );
        let partners = signature_partners(files);
        let state = self.entering(files, &partners, index, assemblies);
        walk_at(files, &partners, &self.files, &state, index, assemblies)
    }

    /// The state entering `files[index]`: [`FoldState::advance`] replayed
    /// over the surfaces before it.
    pub(crate) fn entering(
        &self,
        files: &[ProjectFile],
        partners: &[Option<usize>],
        index: usize,
        assemblies: &AssemblyEnv,
    ) -> FoldState {
        let mut state = FoldState::new(assemblies);
        for (i, surface) in self.files[..index].iter().enumerate() {
            let slot = FoldSlot::of(files, partners, &self.files, i);
            state.advance(surface, &slot, assemblies.names());
        }
        state
    }
}

/// The full walk of `files[index]` against `state`, the state entering it,
/// with `earlier` the surfaces before it: what the full fold publishes there.
fn walk_at(
    files: &[ProjectFile],
    partners: &[Option<usize>],
    earlier: &[Arc<FileSurface>],
    state: &FoldState,
    index: usize,
    assemblies: &AssemblyEnv,
) -> ResolvedFile {
    let mut rf = ResolvedFile::build(&files[index], state, assemblies);
    FoldSlot::of(files, partners, earlier, index).complete(&mut rf.surface, assemblies.names());
    rf
}

/// Fold the surfaces of `files[..horizon]`, with pairing from the whole
/// `files` list as [`resolve_project_files_prefix`](super::resolve_project_files_prefix)
/// pairs.
///
/// # Panics
///
/// Panics when `horizon > files.len()`.
pub fn resolve_project_surfaces(
    files: &[ProjectFile],
    horizon: usize,
    assemblies: &AssemblyEnv,
) -> ProjectSurfaces {
    ProjectSurfaces {
        files: fold::<FileSurface>(None, files, horizon, assemblies, None).files,
    }
}

/// [`resolve_project_surfaces`] reusing an earlier surface fold (`prev`, of
/// `prev_files`) wherever an edit cannot have changed a surface, under the
/// cutoff [`resolve_project_files_prefix_incremental`](super::resolve_project_files_prefix_incremental)
/// uses. Returns exactly what a cold surface fold of `new_files` would, and
/// which items were reused.
///
/// # Panics
///
/// Panics when `horizon > new_files.len()`.
pub fn resolve_project_surfaces_incremental(
    prev_files: &[ProjectFile],
    prev: &ProjectSurfaces,
    new_files: &[ProjectFile],
    horizon: usize,
    assemblies: &AssemblyEnv,
) -> (ProjectSurfaces, Vec<bool>) {
    let folded = fold(
        Some((prev_files, &prev.files)),
        new_files,
        horizon,
        assemblies,
        None,
    );
    (
        ProjectSurfaces {
            files: folded.files,
        },
        folded.reused,
    )
}

/// What a request on one file needs from the project: the surfaces of the
/// files before it, and its own full walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TargetResolution {
    surfaces: ProjectSurfaces,
    target: ResolvedFile,
}

impl TargetResolution {
    /// The surfaces of the files before the target.
    pub fn surfaces(&self) -> &ProjectSurfaces {
        &self.surfaces
    }

    /// The target's full walk.
    pub fn target(&self) -> &ResolvedFile {
        &self.target
    }
}

/// The surfaces of `files[..index]` and the full walk of `files[index]`:
/// what the full fold of `files` publishes at `index`, without the full
/// walks of the files before it.
///
/// # Panics
///
/// Panics when `index >= files.len()`.
pub fn resolve_target(
    files: &[ProjectFile],
    index: usize,
    assemblies: &AssemblyEnv,
) -> TargetResolution {
    assert!(
        index < files.len(),
        "target {index} is past the Compile list ({})",
        files.len()
    );
    let folded = fold::<FileSurface>(None, files, index, assemblies, None);
    let partners = signature_partners(files);
    let target = walk_at(
        files,
        &partners,
        &folded.files,
        &folded.state,
        index,
        assemblies,
    );
    TargetResolution {
        surfaces: ProjectSurfaces {
            files: folded.files,
        },
        target,
    }
}
