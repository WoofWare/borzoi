//! Hostile working directories
//! ([`Kind::WorkingDirectory`](super::Kind::WorkingDirectory)).
//!
//! MSBuild resolves some relative paths against the directory it was started
//! from and not against the project (its Unix path fix-up probes
//! `Directory.Exists("obj")` there), so the directory a tool starts in is an
//! input. [`directory`] gives the directory for each case.

use std::path::{Path, PathBuf};

use super::Dimension;

/// A directory to start a tool from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Cwd {
    /// The project's directory, holding an `obj/`.
    ProjectDirectory,
    /// The project's directory, holding no `obj/`.
    ProjectDirectoryUnrestored,
    /// A fresh empty directory.
    UnrelatedEmpty,
    /// A fresh directory holding a directory for each path segment the
    /// project names.
    HoldsProjectSegments,
    /// The root directory.
    RootDirectory,
}

impl Cwd {
    /// Every working directory.
    pub const ALL: &'static [Cwd] = &[
        Cwd::ProjectDirectory,
        Cwd::ProjectDirectoryUnrestored,
        Cwd::UnrelatedEmpty,
        Cwd::HoldsProjectSegments,
        Cwd::RootDirectory,
    ];

    /// The working directory's dimension.
    pub fn dimension(self) -> Dimension {
        match self {
            Cwd::ProjectDirectory => Dimension::ProjectDirectory,
            Cwd::ProjectDirectoryUnrestored => Dimension::ProjectDirectoryUnrestored,
            Cwd::UnrelatedEmpty => Dimension::UnrelatedEmpty,
            Cwd::HoldsProjectSegments => Dimension::HoldsProjectSegments,
            Cwd::RootDirectory => Dimension::RootDirectory,
        }
    }
}

/// The directory for `cwd`, for a project in `project_dir`.
///
/// `segments` are the first segments of the relative paths the project
/// spells (`obj`, `bin`, a source directory): what
/// [`Cwd::HoldsProjectSegments`] holds. `scratch` is a directory outside the
/// project in which the unrelated directories are made, each fresh.
///
/// [`Cwd::ProjectDirectory`] makes `obj/` in the project if it has none, and
/// [`Cwd::ProjectDirectoryUnrestored`] changes nothing.
///
/// # Panics
///
/// If [`Cwd::ProjectDirectoryUnrestored`] is asked for a project that has an
/// `obj/`: the case would not be the one it is counted as. Or if `scratch` is
/// inside the project, or a segment is not one plain path component.
pub fn directory(cwd: Cwd, project_dir: &Path, segments: &[&str], scratch: &Path) -> PathBuf {
    let fresh = || {
        // Where the directories are, not how they are spelt: a scratch
        // directory that is a link into the project is inside it.
        let real = |dir: &Path| {
            dir.canonicalize()
                .unwrap_or_else(|e| panic!("{} is no directory: {e}", dir.display()))
        };
        assert!(
            !real(scratch).starts_with(real(project_dir)),
            "{} is inside the project",
            scratch.display()
        );
        tempfile::Builder::new()
            .prefix("cwd-")
            .tempdir_in(scratch)
            .expect("create a working directory")
            .keep()
    };
    match cwd {
        Cwd::ProjectDirectory => {
            std::fs::create_dir_all(project_dir.join("obj")).expect("create obj/");
            project_dir.to_owned()
        }
        Cwd::ProjectDirectoryUnrestored => {
            assert!(
                !project_dir.join("obj").exists(),
                "{} has an obj/, so it is no unrestored project",
                project_dir.display()
            );
            project_dir.to_owned()
        }
        Cwd::UnrelatedEmpty => fresh(),
        Cwd::HoldsProjectSegments => {
            let dir = fresh();
            for segment in segments {
                assert!(
                    !segment.is_empty()
                        && !segment.contains(['/', '\\', '\0'])
                        && *segment != "."
                        && *segment != "..",
                    "{segment:?} is not one plain path component"
                );
                // Two of the project's paths may share a first segment, or
                // spell one in two cases on a file system that folds them.
                std::fs::create_dir_all(dir.join(segment)).expect("create a segment's directory");
            }
            dir
        }
        Cwd::RootDirectory => PathBuf::from("/"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hostile::Kind;
    use std::collections::BTreeSet;

    #[test]
    fn every_working_directory_has_its_own_dimension() {
        let dimensions: BTreeSet<_> = Cwd::ALL.iter().map(|c| c.dimension()).collect();
        assert_eq!(dimensions.len(), Cwd::ALL.len());
        assert_eq!(dimensions, Kind::WorkingDirectory.dimensions().collect());
    }

    #[test]
    fn each_directory_is_what_it_says() {
        let root = tempfile::tempdir().unwrap();
        let (project, scratch) = (root.path().join("proj"), root.path().join("scratch"));
        std::fs::create_dir_all(&project).unwrap();
        std::fs::create_dir_all(&scratch).unwrap();
        let segments = ["obj", "bin", "src", "src"];

        let unrestored = directory(
            Cwd::ProjectDirectoryUnrestored,
            &project,
            &segments,
            &scratch,
        );
        assert_eq!(unrestored, project);
        assert!(!project.join("obj").exists());

        let empty = directory(Cwd::UnrelatedEmpty, &project, &segments, &scratch);
        assert!(empty.starts_with(&scratch));
        assert_eq!(std::fs::read_dir(&empty).unwrap().count(), 0);

        let holding = directory(Cwd::HoldsProjectSegments, &project, &segments, &scratch);
        assert_ne!(holding, empty);
        for segment in segments {
            assert!(holding.join(segment).is_dir());
        }

        assert_eq!(
            directory(Cwd::RootDirectory, &project, &segments, &scratch),
            Path::new("/")
        );

        let restored = directory(Cwd::ProjectDirectory, &project, &segments, &scratch);
        assert_eq!(restored, project);
        assert!(project.join("obj").is_dir());
    }

    #[test]
    #[should_panic(expected = "is no unrestored project")]
    fn an_unrestored_project_with_an_obj_is_refused() {
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("obj")).unwrap();
        directory(
            Cwd::ProjectDirectoryUnrestored,
            root.path(),
            &[],
            Path::new("/nonexistent"),
        );
    }
}
