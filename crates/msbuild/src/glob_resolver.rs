//! Filesystem-backed MSBuild glob resolver — the imperative shell around
//! the pure `crate::glob` matcher.
//!
//! The evaluator never touches the filesystem to glob (gospel "dependency
//! rejection"): it routes any globbing/excluding item element through a
//! caller-supplied [`crate::GlobResolver`]. This module is the resolver
//! every caller in the workspace passes — the LSP, and the MSBuild
//! differentials that must test exactly what the LSP runs, the same way
//! [`crate::resolve_sdk`] is the shipped `SdkResolver`. For each wildcard
//! fragment it lists the file system below the fragment's walk root, runs
//! the port of MSBuild's file matcher (`crate::glob::file_matcher`) over that
//! listing, passes literal fragments through unchanged, and joins everything
//! in MSBuild's document order.
//!
//! ## Semantics (pinned against real `dotnet msbuild`)
//!
//! For each `Include` fragment, in document order:
//!
//! - Fragments arrive split and still escaped ([`SpecFragment`]). Whether
//!   one is a glob is MSBuild's classification of its escaped text
//!   ([`SpecFragment::is_wildcard`]), so an escaped `%2a` is a star in a
//!   filename and `a%2a*.fs` is the literal `a**.fs`; each is decoded here,
//!   after that, and never split again, so an escaped `%3b` is a `;` in a
//!   filename.
//! - A **literal** fragment is emitted regardless of whether the file
//!   exists (MSBuild passes literal includes through unconditionally); an
//!   `Exclude` that matches it still removes it, as `FileSpecMatcherTester`
//!   decides.
//! - A **wildcard** fragment is expanded as `FileMatcher.GetFiles` expands it:
//!   the walk from its fixed directory, with the excludes the file matcher is
//!   handed ([`SpecFragment::excludes_from_globs`]) placed against that walk's
//!   root, in MSBuild's `OrdinalIgnoreCase` order within the fragment (see the
//!   `crate::glob` module). The walk root may climb out of the project
//!   (`../shared/*.fs`) or be absolute (`/opt/lib/*.fs`).
//!
//! Fragments are concatenated in document order and **not** deduplicated:
//! MSBuild keeps duplicates from overlapping fragments (e.g. `a.fs;*.fs`
//! lists `a.fs` twice), and so do we.
//!
//! ## Correctness envelope
//!
//! The resolver commits a list only when it is MSBuild's list; otherwise it
//! returns a [`GlobDecline`] and the evaluator marks the item set uncertain.
//!
//! - **An allow-list, not a deny-list.** MSBuild's matchers carry Windows
//!   filename rules, UTF-16 widths and .NET case folding that the port does
//!   not model in full. Rather than chase each, the resolver commits only
//!   when every spec it matches against, and every name a glob would match, is
//!   inside the shape the MSBuild differentials verify
//!   (`glob::unmodelled_shape`); anything else declines
//!   ([`GlobDecline::OutsideModelledShape`]), so a shape nobody has checked
//!   cannot commit a wrong list. Within it, the file matcher's walk and
//!   regular expressions are ported (`crate::glob::file_matcher`), and
//!   legality ([`GlobDecline::IllegalFilespec`]) and a drive-enumerating `**`
//!   ([`GlobDecline::DriveEnumeratingWildcard`]) decline.
//! - **The file system decides what exists; everything past that ignores
//!   ASCII case.** The include's fixed directory and each exclude's are looked
//!   up as written (an exclude whose fixed directory does not exist takes
//!   nothing), and the directories the walk enters are the ones listed. Names
//!   are compared by `FileMatcher.IsMatch`, which folds ASCII case on every
//!   culture, and base directories `OrdinalIgnoreCase`. The regular
//!   expressions the file matcher and `FileSpecMatcherTester` compare paths by
//!   ignore case by the build's culture, which is not observable: the
//!   resolver expands each fragment under the invariant culture and under a
//!   Turkish one, and declines where they differ
//!   ([`GlobDecline::CultureDependentCase`]).
//! - Recursive (`**`) globs descend at most `MAX_GLOB_DEPTH` components
//!   to bound runaway enumeration; meeting a directory at that depth
//!   declines ([`GlobDecline::DepthLimit`]).
//! - Symlinked **files** and **directories** are followed, as MSBuild
//!   follows them (probed), and listed under the link's name. A link back to
//!   a directory already on the walk's path is a cycle, which declines
//!   ([`GlobDecline::SymlinkCycle`]) rather than guess what MSBuild does.
//! - A glob that selects a file found through a symbolic link to a
//!   directory (a directory the walk entered through a link, or the walk's
//!   root being one) declines ([`GlobDecline::SymlinkedDirectory`]). MSBuild's
//!   `FileMatcher.GetFilesRecursive` lists nothing in a directory that is a
//!   link whose final target contains it:
//!   `IsSubdirectoryOf(dir, Directory.ResolveLinkTarget(dir, returnFinalTarget: true).FullName, FileUtilities.PathComparison)`
//!   (probed on MSBuild 18.9: `src/*/*.fs` skips `src/link` linking to the
//!   project directory, and `link/*.fs` with `link` linking to it is empty).
//!   Three inputs decide that, and the walk observes none of them:
//!   - the link's final target, which .NET resolves *lexically*: each hop's
//!     text joined to the directory of the path so far, and `..` taking the
//!     name written before it, link or not. The canonical target the walk
//!     sees can name a different directory, so no comparison of canonical
//!     paths decides the rule;
//!   - the directory's path as the build spells it, every ancestor up to `/`
//!     included, above the walk's root and above the project directory too,
//!     where the build's own spelling of the project directory decides;
//!   - the comparison, `Ordinal` or `OrdinalIgnoreCase` by whether MSBuild's
//!     probe of `Path.GetTempPath()` finds the build's temp directory
//!     case-sensitive, so a link to a case variant of an ancestor
//!     (`/p/src/link -> /P`, or `é` for `É`) is walked by one build and
//!     skipped by another on the same tree.
//!
//!   A glob that only walks through such a directory, selecting nothing
//!   found there, commits: the rule moves nothing it lists. Whether the
//!   walk's root is a link is asked of it as [`crate::GlobRequest::base_dir`]
//!   spells it; a build that spells the project directory through a link
//!   where `base_dir` has none is outside what the walk sees. Reading each
//!   link's target (a query `observed` does not make) would let the resolver
//!   follow the rule wherever the build's spelling of the project directory
//!   is [`crate::GlobRequest::base_dir`]'s, declining only where the temp
//!   directory decides.
//! - **Known boundary: `MSBuildCacheFileEnumerations`.** With that environment
//!   variable set (non-empty) in the build's process, the file matcher keeps
//!   every expansion process-wide (`FileMatcher.s_cachedGlobExpansions`)
//!   until the build manager clears its caches, keyed `OrdinalIgnoreCase` on
//!   the project directory, the spec and its excludes, and asks the file
//!   system nothing for a key it holds. Two specs that differ only in case
//!   (`sub/*.fs`, then `SUB/*.fs`) then share whichever expansion the process
//!   made first, its spelling included, on a case-sensitive file system as on
//!   any other; and a file created after an expansion can be missing from
//!   later ones. What a build process expanded before is state of the build
//!   that no evaluation here can see, so this is not modelled: the resolver
//!   answers as a build without the variable does, whose evaluation context
//!   caches expansions keyed ordinally.
//! - A literal include meets its excludes ignoring ASCII case on every host,
//!   as MSBuild's `FileSpecMatcherTester` does, and declines where the
//!   build's culture would decide a regular expression's verdict.

use std::path::{Path, PathBuf};

use crate::observed::{self, EntryKind, Observer};
use crate::{GlobRequest, SpecFragment, Unmodelled};

use crate::glob::file_matcher::{
    Culture, FileSpec, FileSpecRegex, Listing, Search, file_name, full_path, get_files, is_match,
    is_recursive_directory_match, path_combine,
};
use crate::glob::{
    GlobDecline, compares_unnormalised, has_tilde_after_first_fixed_segment,
    is_drive_enumerating_filespec, is_legal_filespec, sort_like_msbuild, split_filespec,
    split_segments, unmodelled_shape,
};

/// Maximum number of path components a recursive (`**`) glob descends.
const MAX_GLOB_DEPTH: usize = 64;

/// Expand one [`GlobRequest`] into the ordered list of absolute paths to
/// splice as items — exactly MSBuild's list, or a [`GlobDecline`] saying why
/// it cannot be reproduced. Suitable as a [`crate::GlobResolver`].
pub fn resolve(req: &GlobRequest<'_>) -> Result<Vec<PathBuf>, GlobDecline> {
    // The project directory as the evaluation spells it: the base every
    // relative spec is combined with, and the prefix the walk strips from
    // what it lists. It is a *literal* path (it may legitimately contain
    // `*`/`?` on a case-sensitive Unix file system) and is never parsed as a
    // glob.
    let base_norm = req.base_dir.to_string_lossy().replace('\\', "/");
    let base_segs = split_segments(&base_norm);

    // The allow-list: every spec the resolver matches anything against, and
    // every name a glob would match, must be in the shape it models
    // (`glob::unmodelled_shape`); anything else declines. A literal include
    // with no excludes is matched against nothing, so only it goes unchecked.
    for exclude in req.excludes {
        within_modelled_shape(&exclude.unescape(), &base_norm)?;
    }
    // `EngineFileUtilities.GetFileList` lists nothing for any fragment, literal
    // or not, once an exclude the file matcher is handed enumerates a drive
    // from its root; it logs a warning instead.
    if let Some(exclude) = req
        .excludes
        .iter()
        .filter(|e| e.excludes_from_globs())
        .map(|e| e.unescape().replace('\\', "/"))
        .find(|norm| is_drive_enumerating_filespec(norm))
    {
        return Err(GlobDecline::DriveEnumeratingWildcard { spec: exclude });
    }

    // A glob include is matched by MSBuild's file matcher, which is handed
    // the excludes `SpecFragment::excludes_from_globs` keeps, each decoded and
    // then read as a file spec (every decoded `*`/`?` a wildcard). The list is
    // consulted only by a glob include, so what it cannot model declines only
    // there: a filespec the matcher refuses, and one whose fixed directory
    // the matcher resolves against the build's working directory
    // (`Unmodelled::TildeInFixedDirectory`).
    let glob_excludes: Result<Vec<FileSpec>, GlobDecline> = req
        .excludes
        .iter()
        .filter(|e| e.excludes_from_globs())
        .map(|e| {
            let norm = e.unescape().replace('\\', "/");
            if has_tilde_after_first_fixed_segment(&norm) {
                return Err(GlobDecline::OutsideModelledShape {
                    spec: norm,
                    shape: Unmodelled::TildeInFixedDirectory,
                });
            }
            FileSpec::parse(&base_norm, &norm).ok_or(GlobDecline::IllegalFilespec { pattern: norm })
        })
        .collect();
    // The glob excludes' searches: those whose fixed directory exists. Asked
    // of the file system once, by the first glob include, so a list of
    // literal includes reads nothing.
    let mut live_excludes: Option<Vec<Search>> = None;

    let mut out: Vec<PathBuf> = Vec::new();
    // The evaluator already split, trimmed and $()-expanded each fragment
    // and stripped `@()`/`%()` references, so each is a literal or wildcard
    // path, classified on its escaped text and decoded here.
    for frag in req.include {
        let raw = frag.unescape();
        let norm = raw.replace('\\', "/");
        if !frag.is_wildcard() {
            // Literal passthrough: MSBuild emits a literal include whether
            // or not the file exists; only a matching Exclude removes it. The
            // emitted path is `base_dir.join` (an absolute `norm` replaces the
            // base, a relative one extends it). Every character of `norm` is
            // data, a decoded `%2a` star included.
            if !req.excludes.is_empty() {
                within_modelled_shape(&raw, &base_norm)?;
            }
            if literal_survives_excludes(&raw, req.excludes, &base_norm, &base_segs)? {
                out.push(req.base_dir.join(&norm));
            }
            continue;
        }
        within_modelled_shape(&raw, &base_norm)?;
        if has_tilde_after_first_fixed_segment(&norm) {
            return Err(GlobDecline::OutsideModelledShape {
                spec: norm,
                shape: Unmodelled::TildeInFixedDirectory,
            });
        }
        if is_drive_enumerating_filespec(&norm) {
            return Err(GlobDecline::DriveEnumeratingWildcard { spec: norm });
        }
        let Some(spec) = FileSpec::parse(&base_norm, &norm) else {
            return Err(GlobDecline::IllegalFilespec { pattern: norm });
        };
        let Some(search) = spec.search(directory_exists(req.observer, spec.probe())) else {
            continue;
        };
        let glob_excludes = glob_excludes.as_ref().map_err(Clone::clone)?;
        let live_excludes = live_excludes.get_or_insert_with(|| {
            glob_excludes
                .iter()
                .filter_map(|e| e.search(directory_exists(req.observer, e.probe())))
                .collect()
        });
        let root = host_path(search.base_directory());
        let listing = list(&root, search.depth(), req.observer)?;
        // Every name the walk could list is held to the allow-list too,
        // matched or not: a name outside it could match where the port says
        // it does not. A non-ASCII name is the exception, being common and
        // harmless to an ASCII pattern (which the specs are) except in two
        // ways: a `?` meeting a character two UTF-16 units wide, and a letter
        // folded onto ASCII, by `OrdinalIgnoreCase` (`ı`, `ſ`) or by the file
        // matcher's case-ignoring regular expressions (`K`, the Kelvin sign,
        // onto `k`, and `İ` onto `i`, on any culture: oracle-pinned). So it is
        // held only where a `?` is in play, or it has one of those letters.
        let question = norm.contains('?')
            || req
                .excludes
                .iter()
                .filter(|e| e.excludes_from_globs())
                .any(|e| e.unescape().contains('?'));
        each_file(&listing, "", &mut |rel| {
            let shape = match unmodelled_shape(rel) {
                Some(Unmodelled::NonAscii) if !question && !rel.contains(FOLDED_ONTO_ASCII) => {
                    unmodelled_shape(&rel.replace(|c: char| !c.is_ascii(), "x"))
                }
                shape => shape,
            };
            match shape {
                Some(shape) => Err(GlobDecline::OutsideModelledShape {
                    spec: rel.to_string(),
                    shape,
                }),
                None => Ok(()),
            }
        })?;
        // The walk under each culture's case equivalence; a regular
        // expression's verdict on `i` and `I` is the build's culture's.
        let [invariant, turkish] = Culture::ALL.map(|culture| {
            get_files(&base_norm, &search, live_excludes, &listing, culture)
                .map(|mut found| {
                    found.sort_by(|a, b| a.path.cmp(&b.path));
                    found
                })
                .map_err(|unlisted| GlobDecline::DepthLimit { dir: unlisted.dir })
        });
        let (invariant, turkish) = (invariant?, turkish?);
        if invariant != turkish {
            let path = invariant
                .iter()
                .chain(&turkish)
                .find(|f| !(invariant.contains(f) && turkish.contains(f)))
                .map(|f| f.path.clone())
                .unwrap_or_default();
            return Err(GlobDecline::CultureDependentCase { path });
        }
        // MSBuild may skip a directory these were found through, and would
        // then list none of them.
        if let Some(link) = invariant.iter().find_map(|f| f.link.clone()) {
            return Err(GlobDecline::SymlinkedDirectory { path: link });
        }
        let mut selected: Vec<String> = invariant.into_iter().map(|f| f.path).collect();
        sort_like_msbuild(&mut selected)?;
        for path in selected {
            // What the walk lists is relative to the project directory where
            // the spec is, and absolute where it is not.
            let absolute = if path.starts_with('/') {
                path
            } else {
                format!("{base_norm}/{path}")
            };
            out.push(Path::new("/").join(split_segments(&absolute).join("/")));
        }
    }
    Ok(out)
}

/// Non-ASCII letters MSBuild's matchers fold onto ASCII ones: `ı` and `ſ`
/// under `OrdinalIgnoreCase`, and `K` (the Kelvin sign) and `İ` under the file
/// matcher's case-ignoring regular expressions.
const FOLDED_ONTO_ASCII: [char; 4] = ['\u{131}', '\u{17f}', '\u{212a}', '\u{130}'];

/// A path the walk spells, as the file system is asked it: .NET's
/// `Directory.Exists` and enumeration take `Path.GetFullPath` first, which
/// resolves `.` and `..` lexically.
fn host_path(path: &str) -> PathBuf {
    PathBuf::from(if path.starts_with('/') {
        full_path(path)
    } else {
        path.to_string()
    })
}

/// `Directory.Exists`, which `GetFileSearchData` asks of a spec's fixed
/// directory rooted at the project directory. The host's file system answers,
/// so on a case-sensitive one `SUB/*.fs` finds nothing where only `sub`
/// exists, and an exclude spelt under an empty `SUB` takes from `sub` too
/// (oracle-pinned, #607).
fn directory_exists(observer: &Observer, path: &str) -> bool {
    observed::is_dir(observer, &host_path(path))
}

/// The allow-list gate for one decoded spec (`glob::unmodelled_shape`). An
/// absolute spec is checked below the project directory, so spelling a file
/// as `$(MSBuildProjectDirectory)/a.fs` in a checkout under a non-ASCII path
/// is still modelled: that prefix is a literal the two sides share.
fn within_modelled_shape(spec: &str, base_norm: &str) -> Result<(), GlobDecline> {
    let norm = spec.replace('\\', "/");
    let base = base_norm.trim_end_matches('/');
    let checked = norm
        .strip_prefix(base)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(&norm);
    match unmodelled_shape(checked) {
        Some(shape) => Err(GlobDecline::OutsideModelledShape {
            spec: spec.to_string(),
            shape,
        }),
        None => Ok(()),
    }
}

/// The literal segments a decoded spec is anchored under: none for an
/// absolute spec, the project directory's for a relative one.
fn anchor_prefix<'b>(base_segs: &'b [&'b str], norm: &str) -> &'b [&'b str] {
    if norm.starts_with('/') {
        &[]
    } else {
        base_segs
    }
}

/// A spelling as `Path.GetFullPath(Path.Combine(base, spelling))` writes it,
/// for comparison: rooted at the project directory unless already absolute,
/// `.` segments dropped and `..` segments resolved lexically (at the root, a
/// `..` stays at the root), with `/` separators and no leading `/`.
fn lexical_full_path(base_segs: &[&str], spelling: &str) -> String {
    let norm = spelling.replace('\\', "/");
    let mut segs: Vec<&str> = anchor_prefix(base_segs, &norm).to_vec();
    for seg in split_segments(&norm) {
        if seg == ".." {
            segs.pop();
        } else {
            segs.push(seg);
        }
    }
    segs.join("/")
}

/// Whether a **literal** include survives the `Exclude` fragments, as
/// MSBuild's `FileSpecMatcherTester` decides it against an include it does
/// not glob — the reading that differs from a glob include's
/// ([`SpecFragment::excludes_from_globs`]). `item` is the include's decoded
/// spelling.
///
/// - An exclude MSBuild classifies as a glob ([`SpecFragment::is_wildcard`])
///   with an empty fixed directory and a wildcard directory part of `**`
///   matches the item's file name by `FileMatcher.IsMatch`, and needs the
///   item's full path to start with the project directory's
///   (`OrdinalIgnoreCase`, with no separator after it). Any other is
///   recombined with its fixed directory made full and compared with the
///   item's full path by `RegularExpressionFromFileSpec`'s expression. One the
///   file matcher would refuse declines.
/// - Any other exclude is a name. Two names are compared as full paths
///   (`./a.fs` is `a.fs`), unless either is a spelling MSBuild does not
///   normalise ([`compares_unnormalised`]), which is compared as written.
///
/// Comparison ignores ASCII case, directories included, on every host. The
/// regular expression ignores case by the build's culture, so where keeping
/// `i` and `I` apart, as Turkish does, would change the verdict, this declines
/// ([`GlobDecline::CultureDependentCase`]).
fn literal_survives_excludes(
    item: &str,
    excludes: &[SpecFragment],
    base_norm: &str,
    base_segs: &[&str],
) -> Result<bool, GlobDecline> {
    let item_full = format!("/{}", lexical_full_path(base_segs, item));
    // Whether some exclude takes the item: under each culture.
    let (mut excluded, mut excluded_turkish) = (false, false);
    for exclude in excludes {
        let spelling = exclude.unescape();
        let (takes, takes_turkish) = if exclude.is_wildcard() {
            let norm = spelling.replace('\\', "/");
            if !is_legal_filespec(&norm) {
                return Err(GlobDecline::IllegalFilespec { pattern: norm });
            }
            let (fixed, wildcard_dir, filename) = split_filespec(&norm);
            if fixed.is_empty() && is_recursive_directory_match(&wildcard_dir) {
                // `FileMatcher.IsMatch` on the name, which no culture moves.
                let takes = is_match(file_name(&item_full), &filename)
                    && starts_with_ignoring_case(&item_full, base_norm);
                (takes, takes)
            } else {
                // `CreateRegexOrFilenamePattern`: the fixed directory made full
                // (so against a literal include `sub/../*.fs` is `*.fs`, unlike
                // the file matcher, which compares by spelling), then the spec
                // split again and read as a regular expression.
                let mut fixed_full = full_path(&path_combine(base_norm, fixed));
                if !fixed_full.ends_with('/') {
                    fixed_full.push('/');
                }
                let recombined = format!("{fixed_full}{wildcard_dir}{filename}");
                if !is_legal_filespec(&recombined) {
                    return Err(GlobDecline::IllegalFilespec {
                        pattern: recombined,
                    });
                }
                if has_tilde_after_first_fixed_segment(&recombined) {
                    return Err(GlobDecline::OutsideModelledShape {
                        spec: recombined,
                        shape: Unmodelled::TildeInFixedDirectory,
                    });
                }
                let (fixed, wildcard_dir, filename) = split_filespec(&recombined);
                let regex = FileSpecRegex::new(fixed, &wildcard_dir, &filename);
                (
                    regex.is_match(&item_full, Culture::Invariant),
                    regex.is_match(&item_full, Culture::Turkish),
                )
            }
        } else {
            // Each operand is normalised, or not, on its own spelling
            // (`NormalizePathForComparisonNoThrow` is applied to each side).
            let operand = |spelling: &str| {
                if compares_unnormalised(spelling) {
                    spelling.to_string()
                } else {
                    format!("/{}", lexical_full_path(base_segs, spelling))
                }
            };
            let takes = operand(item).eq_ignore_ascii_case(&operand(&spelling));
            (takes, takes)
        };
        excluded |= takes;
        excluded_turkish |= takes_turkish;
        if excluded && excluded_turkish {
            return Ok(false);
        }
    }
    if excluded != excluded_turkish {
        return Err(GlobDecline::CultureDependentCase {
            path: item.to_string(),
        });
    }
    Ok(true)
}

/// `a.StartsWith(b, StringComparison.OrdinalIgnoreCase)` for the ASCII text
/// the allow-list leaves below the project directory.
fn starts_with_ignoring_case(a: &str, b: &str) -> bool {
    a.len() >= b.len() && a.as_bytes()[..b.len()].eq_ignore_ascii_case(b.as_bytes())
}

/// Call `f` with every file of `listing`, as a `/`-joined path below it.
fn each_file(
    listing: &Listing,
    prefix: &str,
    f: &mut impl FnMut(&str) -> Result<(), GlobDecline>,
) -> Result<(), GlobDecline> {
    let join = |name: &str| {
        if prefix.is_empty() {
            name.to_string()
        } else {
            format!("{prefix}/{name}")
        }
    };
    for name in &listing.files {
        f(&join(name))?;
    }
    for (name, child) in &listing.dirs {
        if let Some(child) = child {
            each_file(child, &join(name), f)?;
        }
    }
    Ok(())
}

/// The [`Listing`] of `root` a walk of `depth` levels can read (`None`: a
/// `**` walk, read to `MAX_GLOB_DEPTH`). Every listing is read through the
/// observer, so the evaluation's read set holds each one the walk can depend
/// on; a directory past the depth is named in its parent's listing but not
/// read. Symlinked files and directories are followed, as MSBuild follows
/// them, and listed under the link's own name, each directory with the link
/// it was found through; an unreadable directory lists nothing. Declines
/// where the listing would miss what MSBuild might see: a directory left
/// unread at the depth bound of a `**` walk, or a symlink cycle (see the
/// module's correctness envelope).
fn list(root: &Path, depth: Option<usize>, observer: &Observer) -> Result<Listing, GlobDecline> {
    let (max_depth, recursive) = match depth {
        Some(depth) => (depth, false),
        None => (MAX_GLOB_DEPTH, true),
    };
    let mut ancestors: Vec<PathBuf> = observed::canonicalize(observer, root).into_iter().collect();
    // MSBuild asks of the walk root too whether it is a link to a directory
    // that contains it, so the root is a link the files may be found through.
    let root_link = (observed::link_kind(observer, root) == Ok(EntryKind::Symlink))
        .then(|| root.to_string_lossy().into_owned());
    let mut lister = Lister {
        max_depth,
        recursive,
        observer,
        ancestors: &mut ancestors,
    };
    lister.dir(root, 0, root_link)
}

/// [`list`]'s walk. `ancestors` holds the canonical path of every directory on
/// the way down to the one being listed, that one included, so a link back
/// to one of them is recognised as a cycle.
struct Lister<'a> {
    max_depth: usize,
    recursive: bool,
    observer: &'a Observer,
    ancestors: &'a mut Vec<PathBuf>,
}

impl Lister<'_> {
    /// The listing of `dir`, at `depth` below the root, reached through the
    /// link `link` if any.
    fn dir(
        &mut self,
        dir: &Path,
        depth: usize,
        link: Option<String>,
    ) -> Result<Listing, GlobDecline> {
        let mut listing = Listing {
            link: link.clone(),
            ..Listing::default()
        };
        let Ok(entries) = observed::read_dir(self.observer, dir) else {
            return Ok(listing);
        };
        for entry in entries.into_iter().flatten() {
            // The directory entry's own type does not follow symlinks; `kind` does.
            let (is_dir, is_link) = match entry.kind {
                Ok(EntryKind::File) => (false, false),
                Ok(EntryKind::Dir) => (true, false),
                Ok(EntryKind::Symlink) => match observed::kind(self.observer, &entry.path) {
                    Ok(EntryKind::File) => (false, true),
                    Ok(EntryKind::Dir) => (true, true),
                    _ => continue,
                },
                _ => continue,
            };
            let name = entry.name.to_string_lossy().into_owned();
            if !is_dir {
                listing.files.push(name);
                continue;
            }
            let path = entry.path;
            if depth + 1 >= self.max_depth {
                if self.recursive {
                    return Err(GlobDecline::DepthLimit {
                        dir: path.to_string_lossy().into_owned(),
                    });
                }
                // Only a directory the walk can list can close a cycle.
                listing.dirs.push((name, None));
                continue;
            }
            let Ok(canonical) = observed::canonicalize(self.observer, &path) else {
                continue;
            };
            if self.ancestors.contains(&canonical) {
                return Err(GlobDecline::SymlinkCycle {
                    path: path.to_string_lossy().into_owned(),
                });
            }
            let child_link = link
                .clone()
                .or_else(|| is_link.then(|| path.to_string_lossy().into_owned()));
            self.ancestors.push(canonical);
            let child = self.dir(&path, depth + 1, child_link);
            self.ancestors.pop();
            listing.dirs.push((name, Some(child?)));
        }
        Ok(listing)
    }
}

#[cfg(all(test, unix))]
mod symlink_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;
    use std::collections::BTreeSet;
    use std::fs;
    use tempfile::TempDir;

    /// Create the file tree used by the probe-derived unit tests, mirroring
    /// the layout I measured `dotnet msbuild` against:
    /// `a.fs b.fs m.fs z.fs sub/c.fs sub/deep/d.fs sub/e.fsi`.
    fn fixture() -> TempDir {
        let tmp = TempDir::new().unwrap();
        let base = tmp.path();
        for f in ["a.fs", "b.fs", "m.fs", "z.fs"] {
            fs::write(base.join(f), b"// f\n").unwrap();
        }
        fs::create_dir_all(base.join("sub/deep")).unwrap();
        fs::write(base.join("sub/c.fs"), b"// f\n").unwrap();
        fs::write(base.join("sub/deep/d.fs"), b"// f\n").unwrap();
        fs::write(base.join("sub/e.fsi"), b"// f\n").unwrap();
        tmp
    }

    /// Run the resolver against a base dir with the given include spec and
    /// excludes, returning paths relative to `base` as `/`-joined strings
    /// for compact assertions.
    fn run_rel(base: &Path, include: &str, excludes: &[&str]) -> Vec<String> {
        let include = SpecFragment::split_escaped(include);
        let excludes: Vec<SpecFragment> = excludes
            .iter()
            .flat_map(|s| SpecFragment::split_escaped(s))
            .collect();
        let req = GlobRequest {
            base_dir: base,
            include: &include,
            excludes: &excludes,
            observer: &Observer::new(),
        };
        resolve(&req)
            .expect("the fixture is decidable")
            .into_iter()
            .map(|p| {
                p.strip_prefix(base)
                    .unwrap()
                    .to_string_lossy()
                    .replace('\\', "/")
            })
            .collect()
    }

    // ----- Probe-derived ground-truth unit tests (expected values are the
    // observed `dotnet msbuild -getItem:Compile` outputs) -----

    #[test]
    fn recursive_glob_matches_all_fs_sorted() {
        let tmp = fixture();
        assert_eq!(
            run_rel(tmp.path(), "**/*.fs", &[]),
            ["a.fs", "b.fs", "m.fs", "sub/c.fs", "sub/deep/d.fs", "z.fs"]
        );
    }

    #[test]
    fn top_level_star_is_not_recursive() {
        let tmp = fixture();
        assert_eq!(
            run_rel(tmp.path(), "*.fs", &[]),
            ["a.fs", "b.fs", "m.fs", "z.fs"]
        );
    }

    #[test]
    fn nested_star_is_single_level() {
        let tmp = fixture();
        // `sub/*.fs` is depth-2: it matches `sub/c.fs` but not the
        // depth-3 `sub/deep/d.fs`.
        assert_eq!(run_rel(tmp.path(), "sub/*.fs", &[]), ["sub/c.fs"]);
    }

    #[test]
    fn fsi_is_not_matched_by_fs_glob() {
        let tmp = fixture();
        assert_eq!(run_rel(tmp.path(), "sub/*.fsi", &[]), ["sub/e.fsi"]);
        // and *.fs must not pick up the .fsi
        assert!(!run_rel(tmp.path(), "**/*.fs", &[]).contains(&"sub/e.fsi".to_string()));
    }

    #[test]
    fn literal_then_glob_keeps_duplicate() {
        let tmp = fixture();
        // MSBuild: `a.fs;*.fs` -> [a.fs, a.fs, b.fs, m.fs, z.fs].
        assert_eq!(
            run_rel(tmp.path(), "a.fs;*.fs", &[]),
            ["a.fs", "a.fs", "b.fs", "m.fs", "z.fs"]
        );
    }

    #[test]
    fn two_overlapping_globs_keep_duplicates() {
        let tmp = fixture();
        // MSBuild: `*.fs;?.fs` -> both expansions concatenated.
        assert_eq!(
            run_rel(tmp.path(), "*.fs;?.fs", &[]),
            [
                "a.fs", "b.fs", "m.fs", "z.fs", "a.fs", "b.fs", "m.fs", "z.fs"
            ]
        );
    }

    /// Resolve with `include`/`excludes` split as escaped specs, returning the
    /// result rather than asserting it is decidable.
    fn try_resolve(base: &Path, include: &str, excludes: &[&str]) -> Result<usize, GlobDecline> {
        let include = SpecFragment::split_escaped(include);
        let excludes: Vec<SpecFragment> = excludes
            .iter()
            .flat_map(|s| SpecFragment::split_escaped(s))
            .collect();
        resolve(&GlobRequest {
            base_dir: base,
            include: &include,
            excludes: &excludes,
            observer: &Observer::new(),
        })
        .map(|paths| paths.len())
    }

    /// A directory an exclude names after `**` is taken only where the
    /// include's walk enters it, so an include rooted inside such a directory
    /// keeps its files (#615). The SDK's `**/.*/**` meets `sub/*.fs`, whose
    /// root `.*` cannot match.
    #[test]
    fn a_globstar_exclude_takes_only_directories_the_walk_enters() {
        let tmp = fixture();
        assert_eq!(
            try_resolve(tmp.path(), "sub/deep/*.fs", &["**/deep/**"]),
            Ok(1)
        );
        assert_eq!(
            try_resolve(tmp.path(), "sub/**/*.fs", &["**/deep/**"]),
            Ok(1)
        );
        assert_eq!(
            try_resolve(tmp.path(), "sub/deep/*.fs", &["**/d.fs"]),
            Ok(0)
        );
        assert_eq!(try_resolve(tmp.path(), "sub/*.fs", &["**/.*/**"]), Ok(1));
    }

    /// Against a literal include, every exclude ignores ASCII case, directories
    /// included, on every host (`FileSpecMatcherTester`; oracle-pinned).
    #[test]
    fn a_literal_include_meets_its_excludes_ignoring_case() {
        let tmp = fixture();
        assert_eq!(try_resolve(tmp.path(), "a.fs", &["b.fs"]), Ok(1));
        assert_eq!(try_resolve(tmp.path(), "a.fs", &["A.fs"]), Ok(0));
        assert_eq!(try_resolve(tmp.path(), "sub/c.fs", &["SUB/C.FS"]), Ok(0));
        assert_eq!(try_resolve(tmp.path(), "sub/c.fs", &["S*/c.fs"]), Ok(0));
        assert_eq!(try_resolve(tmp.path(), "sub/c.fs", &["SUB/*.fs"]), Ok(0));
        assert_eq!(try_resolve(tmp.path(), "a.fs;b.fs", &["**/A.fs"]), Ok(1));
        // A regular expression compares `i` with `I`, which the build's
        // culture decides; the filename-only branch does not.
        assert!(matches!(
            try_resolve(tmp.path(), "bi.fs", &["BI*.fs"]),
            Err(GlobDecline::CultureDependentCase { .. })
        ));
        assert_eq!(try_resolve(tmp.path(), "bi.fs", &["BI*.fs", "b*"]), Ok(0));
        assert_eq!(try_resolve(tmp.path(), "bi.fs", &["**/BI.fs"]), Ok(0));
    }

    /// Against a glob include on Linux, an exclude takes part only where its
    /// fixed directory exists as written, and then folds case like the rest
    /// (oracle-pinned, #607).
    #[test]
    #[cfg(target_os = "linux")]
    fn a_glob_include_meets_its_excludes_as_the_file_matcher_does() {
        let tmp = fixture();
        assert_eq!(
            run_rel(tmp.path(), "*.fs", &["A.FS"]),
            ["b.fs", "m.fs", "z.fs"]
        );
        assert_eq!(run_rel(tmp.path(), "S*/*.FS", &[]), ["sub/c.fs"]);
        assert_eq!(run_rel(tmp.path(), "SUB/*.fs", &[]), Vec::<String>::new());
        assert_eq!(run_rel(tmp.path(), "sub/*.fs", &["SUB/*.fs"]), ["sub/c.fs"]);
        assert_eq!(run_rel(tmp.path(), "**/*.fs", &["**/DEEP/**"]).len(), 5);
        fs::create_dir(tmp.path().join("SUB")).unwrap();
        assert_eq!(
            run_rel(tmp.path(), "sub/*.fs", &["SUB/*.fs"]),
            Vec::<String>::new()
        );
        assert_eq!(run_rel(tmp.path(), "**/*.fs", &["SUB/C.fs"]).len(), 5);
        // A regular expression's `i` is the build's culture's to decide.
        fs::write(tmp.path().join("sub/bi.fs"), b"").unwrap();
        assert!(matches!(
            try_resolve(tmp.path(), "s*/BI.fs", &[]),
            Err(GlobDecline::CultureDependentCase { .. })
        ));
        assert_eq!(try_resolve(tmp.path(), "sub/BI.fs", &[]), Ok(1));
    }

    /// Names a regular expression folds onto ASCII, and a `~` the file matcher
    /// looks up from the working directory, decline.
    #[test]
    fn what_a_glob_folds_beyond_ascii_case_declines() {
        let tmp = fixture();
        fs::create_dir_all(tmp.path().join("k/a~b")).unwrap();
        fs::write(tmp.path().join("k/\u{212a}.fs"), b"").unwrap();
        assert!(matches!(
            try_resolve(tmp.path(), "k/*.fs", &[]),
            Err(GlobDecline::OutsideModelledShape {
                shape: Unmodelled::NonAscii,
                ..
            })
        ));
        for (include, excludes) in [("k/A~B/*.fs", &[][..]), ("**/*.fs", &["k/A~B/*.fs"][..])] {
            assert!(
                matches!(
                    try_resolve(tmp.path(), include, excludes),
                    Err(GlobDecline::OutsideModelledShape {
                        shape: Unmodelled::TildeInFixedDirectory,
                        ..
                    })
                ),
                "{include}"
            );
        }
    }

    /// Against a literal include, ordinary names compare as full paths and a
    /// name holding a `*` compares as written (`FileSpecMatcherTester`).
    #[test]
    fn literal_names_compare_as_msbuild_compares_them() {
        let tmp = fixture();
        assert_eq!(
            run_rel(tmp.path(), "./a.fs;sub/../b.fs", &["a.fs", "b.fs"]),
            Vec::<String>::new()
        );
        let abs = format!("{}/a%2ab.fs", tmp.path().display());
        assert_eq!(run_rel(tmp.path(), "a%2ab.fs", &[&abs]), ["a*b.fs"]);
        assert_eq!(try_resolve(tmp.path(), "./a%2ab.fs", &["a%2ab.fs"]), Ok(1));
        assert_eq!(
            run_rel(tmp.path(), "a%2ab.fs", &["a%2ab.fs"]),
            Vec::<String>::new()
        );
    }

    /// The shapes MSBuild's file matcher does not read the plain way decline
    /// by name; `*.*` is every file.
    #[test]
    fn file_matcher_shapes_decline_or_read_as_msbuild() {
        let tmp = fixture();
        fs::write(tmp.path().join("noext"), b"").unwrap();
        assert!(matches!(
            try_resolve(tmp.path(), "a**b.fs", &[]),
            Err(GlobDecline::IllegalFilespec { .. })
        ));
        assert!(matches!(
            try_resolve(tmp.path(), "*.fs", &["a%2a%2ab.fs"]),
            Err(GlobDecline::IllegalFilespec { .. })
        ));
        // A live illegal exclude declines against a literal include too; one
        // whose stars are decoded is not a glob there, only a name.
        assert!(matches!(
            try_resolve(tmp.path(), "a.fs", &["a**b.fs"]),
            Err(GlobDecline::IllegalFilespec { .. })
        ));
        assert_eq!(try_resolve(tmp.path(), "a.fs;z.fs", &["x%2a%2a.fs"]), Ok(2));
        // The file matcher relates a `.` segment by spelling: `./a.fs` is
        // based elsewhere than `*.fs`, and takes nothing from it, nor does
        // `a.fs` from `./*.fs`; its walk looks for a directory named `.`.
        assert_eq!(try_resolve(tmp.path(), "*.fs", &["./a.fs"]), Ok(4));
        assert_eq!(try_resolve(tmp.path(), "./*.fs", &["a.fs"]), Ok(4));
        assert_eq!(try_resolve(tmp.path(), "./*.fs", &[]), Ok(4));
        assert_eq!(try_resolve(tmp.path(), "*/./**/*.fs", &[]), Ok(0));
        assert_eq!(run_rel(tmp.path(), "**/./*.fs", &[]).len(), 6);
        assert_eq!(run_rel(tmp.path(), "*.*", &["*.fs"]), ["noext"]);
        assert_eq!(run_rel(tmp.path(), "*", &["%2a.%2a"]), Vec::<String>::new());
    }

    #[test]
    fn literal_passthrough_does_not_check_existence() {
        let tmp = fixture();
        // MSBuild includes a non-existent literal verbatim.
        assert_eq!(run_rel(tmp.path(), "ghost.fs", &[]), ["ghost.fs"]);
    }

    #[test]
    fn glob_with_no_match_is_empty() {
        let tmp = fixture();
        assert!(run_rel(tmp.path(), "ghost*.fs", &[]).is_empty());
    }

    #[test]
    fn exclude_filters_literal_but_not_ghost() {
        let tmp = fixture();
        // MSBuild: `a.fs;b.fs;ghost.fs` Exclude `a.fs` -> [b.fs, ghost.fs].
        assert_eq!(
            run_rel(tmp.path(), "a.fs;b.fs;ghost.fs", &["a.fs"]),
            ["b.fs", "ghost.fs"]
        );
    }

    #[test]
    fn exclude_glob_removes_subtree() {
        let tmp = fixture();
        // MSBuild: `**/*.fs` Exclude `sub/**/*.fs` -> top-level only.
        assert_eq!(
            run_rel(tmp.path(), "**/*.fs", &["sub/**/*.fs"]),
            ["a.fs", "b.fs", "m.fs", "z.fs"]
        );
    }

    #[test]
    fn paths_are_joined_onto_base_dir() {
        let tmp = fixture();
        let excludes: Vec<SpecFragment> = Vec::new();
        let req = GlobRequest {
            base_dir: tmp.path(),
            include: &SpecFragment::split_escaped("a.fs"),
            excludes: &excludes,
            observer: &Observer::new(),
        };
        assert_eq!(
            resolve(&req).expect("the fixture is decidable"),
            vec![tmp.path().join("a.fs")]
        );
    }

    // ----- Globs rooted outside the project directory -----

    fn canon(p: impl AsRef<Path>) -> PathBuf {
        crate::observed::host_fs::canonicalize(p.as_ref())
            .unwrap_or_else(|e| panic!("canonicalize {}: {e}", p.as_ref().display()))
    }

    /// Resolve and canonicalise the results, so `..`/`/private` differences
    /// don't defeat equality when the glob root is outside `base`.
    fn resolve_canon(base: &Path, include: &str, excludes: &[&str]) -> Vec<PathBuf> {
        let include = SpecFragment::split_escaped(include);
        let excludes: Vec<SpecFragment> = excludes
            .iter()
            .flat_map(|s| SpecFragment::split_escaped(s))
            .collect();
        let req = GlobRequest {
            base_dir: base,
            include: &include,
            excludes: &excludes,
            observer: &Observer::new(),
        };
        resolve(&req)
            .expect("the fixture is decidable")
            .into_iter()
            .map(canon)
            .collect()
    }

    #[test]
    fn parent_relative_glob_resolves_sibling_directory() {
        // tmp/{proj, shared/{x.fs, y.fs}}; base = proj; `../shared/*.fs`
        // must enumerate the sibling `shared` dir, not the project dir.
        let tmp = TempDir::new().unwrap();
        let proj = tmp.path().join("proj");
        let shared = tmp.path().join("shared");
        fs::create_dir_all(&proj).unwrap();
        fs::create_dir_all(&shared).unwrap();
        for f in ["x.fs", "y.fs"] {
            fs::write(shared.join(f), b"// f\n").unwrap();
        }
        assert_eq!(
            resolve_canon(&proj, "../shared/*.fs", &[]),
            [canon(shared.join("x.fs")), canon(shared.join("y.fs"))]
        );
    }

    #[test]
    fn parent_relative_glob_honours_exclude() {
        let tmp = TempDir::new().unwrap();
        let proj = tmp.path().join("proj");
        let shared = tmp.path().join("shared");
        fs::create_dir_all(&proj).unwrap();
        fs::create_dir_all(&shared).unwrap();
        for f in ["x.fs", "y.fs"] {
            fs::write(shared.join(f), b"// f\n").unwrap();
        }
        assert_eq!(
            resolve_canon(&proj, "../shared/*.fs", &["../shared/y.fs"]),
            [canon(shared.join("x.fs"))]
        );
    }

    #[test]
    fn parent_relative_glob_absolute_exclude_does_not_cross_match() {
        // MSBuild matches an Exclude against the Include's items in the
        // Include's own (project-relative, `..`-preserving) frame, *not* by
        // collapsing to a canonical absolute path. So an absolute exclude
        // does NOT cross-match a `../shared/*.fs` include — both siblings
        // survive. This is verified against real MSBuild by the
        // parent-relative corners of `tests/glob_msbuild_diff.rs`; the contrast (a same-frame relative
        // exclude *does* filter) is `parent_relative_glob_honours_exclude`
        // above.
        let tmp = TempDir::new().unwrap();
        let proj = tmp.path().join("proj");
        let shared = tmp.path().join("shared");
        fs::create_dir_all(&proj).unwrap();
        fs::create_dir_all(&shared).unwrap();
        for f in ["x.fs", "y.fs"] {
            fs::write(shared.join(f), b"// f\n").unwrap();
        }
        let abs_excl = shared.join("y.fs").to_string_lossy().into_owned();
        assert_eq!(
            resolve_canon(&proj, "../shared/*.fs", &[&abs_excl]),
            [canon(shared.join("x.fs")), canon(shared.join("y.fs"))]
        );
    }

    // A `*` in a directory name is only legal on Unix-like filesystems, so
    // this fixture (and its oracle mirror) is gated accordingly.
    #[cfg(unix)]
    #[test]
    fn base_dir_wildcard_is_literal() {
        // A project directory whose name contains a glob metacharacter (`*`,
        // legal on Unix) must be treated literally: `*.fs` enumerates the
        // real `a*b` directory and must not let the `*` in the name match a
        // sibling `axb`. Folding base_dir into the glob string would
        // over-match the sibling. Pinned against real MSBuild by the
        // literal-base corner of `tests/glob_msbuild_diff.rs`.
        let tmp = TempDir::new().unwrap();
        let proj = tmp.path().join("a*b");
        let sibling = tmp.path().join("axb");
        fs::create_dir_all(&proj).unwrap();
        fs::create_dir_all(&sibling).unwrap();
        fs::write(proj.join("real.fs"), b"// f\n").unwrap();
        fs::write(sibling.join("decoy.fs"), b"// f\n").unwrap();
        assert_eq!(
            resolve_canon(&proj, "*.fs", &[]),
            [canon(proj.join("real.fs"))]
        );
    }

    #[cfg(unix)]
    #[test]
    fn absolute_glob_resolves_against_filesystem_root() {
        // An absolute include glob is rooted at the filesystem root, not the
        // project directory.
        let src = TempDir::new().unwrap();
        for f in ["a.fs", "b.fs"] {
            fs::write(src.path().join(f), b"// f\n").unwrap();
        }
        let proj = TempDir::new().unwrap();
        let include = format!("{}/*.fs", src.path().display());
        assert_eq!(
            resolve_canon(proj.path(), &include, &[]),
            [
                canon(src.path().join("a.fs")),
                canon(src.path().join("b.fs"))
            ]
        );
    }

    // ----- Symlinks -----

    #[cfg(unix)]
    #[test]
    fn symlinked_source_file_is_included() {
        // MSBuild's wildcard expansion includes a symlinked file; the walk
        // must follow the link to classify the target as a file.
        use std::os::unix::fs::symlink;
        let target_dir = TempDir::new().unwrap();
        let target = target_dir.path().join("real.fs");
        fs::write(&target, b"// f\n").unwrap();
        let tmp = TempDir::new().unwrap();
        let base = tmp.path();
        symlink(&target, base.join("linked.fs")).unwrap();
        fs::write(base.join("a.fs"), b"// f\n").unwrap();
        assert_eq!(run_rel(base, "*.fs", &[]), ["a.fs", "linked.fs"]);
    }

    // ----- Exclude anchoring (relative vs absolute frames) -----

    #[test]
    fn relative_glob_absolute_exclude_is_honoured() {
        // A relative recursive Include with an *absolute* Exclude — exactly
        // what MSBuild hands us from `$(MSBuildProjectDirectory)/sub/c.fs`.
        // The candidates are enumerated base-relative, so the exclude must be
        // anchored into the same (absolute) frame or it silently fails to
        // filter.
        let tmp = fixture();
        let abs_excl = tmp.path().join("sub/c.fs").to_string_lossy().into_owned();
        assert_eq!(
            run_rel(tmp.path(), "**/*.fs", &[&abs_excl]),
            ["a.fs", "b.fs", "m.fs", "sub/deep/d.fs", "z.fs"]
        );
    }

    #[test]
    fn absolute_glob_relative_exclude_is_honoured() {
        // The mirror image: an absolute Include glob with a relative Exclude.
        // MSBuild anchors the relative exclude at the project directory, so
        // it only filters when the absolute glob root *is* that directory.
        let tmp = fixture();
        let include = format!("{}/*.fs", tmp.path().display());
        assert_eq!(
            run_rel(tmp.path(), &include, &["b.fs"]),
            ["a.fs", "m.fs", "z.fs"]
        );
    }

    // ----- Independent naive reference for the property test -----

    fn split_norm(s: &str) -> Vec<String> {
        s.split(['/', '\\'])
            .filter(|p| !p.is_empty() && *p != ".")
            .map(str::to_string)
            .collect()
    }

    fn seg_naive(pat: &[char], s: &[char]) -> bool {
        match pat.split_first() {
            None => s.is_empty(),
            Some((&'*', r)) => (0..=s.len()).any(|i| seg_naive(r, &s[i..])),
            Some((&'?', r)) => !s.is_empty() && seg_naive(r, &s[1..]),
            Some((&c, r)) => s.first() == Some(&c) && seg_naive(r, &s[1..]),
        }
    }

    fn path_naive(pat: &[String], path: &[String]) -> bool {
        match pat.split_first() {
            None => path.is_empty(),
            Some((p, r)) if p == "**" => (0..=path.len()).any(|i| path_naive(r, &path[i..])),
            Some((p, r)) => {
                !path.is_empty() && {
                    let pc: Vec<char> = p.chars().collect();
                    let sc: Vec<char> = path[0].chars().collect();
                    seg_naive(&pc, &sc) && path_naive(r, &path[1..])
                }
            }
        }
    }

    fn naive_match(pattern: &str, path: &str) -> bool {
        path_naive(&split_norm(pattern), &split_norm(path))
    }

    /// Independent reference resolver over a *known* file set (not the
    /// filesystem walk), using the naive matcher. Agreement with `resolve`
    /// validates the filesystem enumeration, ordering, dedup, literal
    /// passthrough, and exclude application together.
    fn reference(
        base: &Path,
        known: &BTreeSet<String>,
        include: &str,
        excludes: &[String],
    ) -> Vec<PathBuf> {
        let is_glob = |f: &str| f.contains('*') || f.contains('?');
        let excluded = |path: &str| excludes.iter().any(|e| naive_match(e, path));
        let mut out = Vec::new();
        for frag in include.split(';').map(str::trim).filter(|s| !s.is_empty()) {
            if is_glob(frag) {
                let mut m: Vec<String> = known
                    .iter()
                    .filter(|p| naive_match(frag, p) && !excluded(p))
                    .map(|p| split_norm(p).join("/"))
                    .collect();
                // MSBuild's `OrdinalIgnoreCase`; the generated names are
                // ASCII and case-distinct, so this is total and decidable.
                m.sort_by_key(|p| p.to_ascii_uppercase());
                out.extend(m.into_iter().map(|p| base.join(p)));
            } else {
                let n = frag.replace('\\', "/");
                if !excluded(&n) {
                    out.push(base.join(&n));
                }
            }
        }
        out
    }

    // ----- Generators -----

    /// A relative file path: 1–3 directory levels over {d,e}, file named
    /// from {a,b,c} with a {.fs,.fsi} extension.
    fn rel_path() -> impl Strategy<Value = String> {
        (
            prop::collection::vec(prop::sample::select(vec!["d", "e"]), 0..=2),
            prop::sample::select(vec!["a", "b", "c"]),
            prop::sample::select(vec![".fs", ".fsi"]),
        )
            .prop_map(|(dirs, name, ext)| {
                let mut parts = dirs;
                parts.push(name);
                let mut p = parts.join("/");
                p.push_str(ext);
                p
            })
    }

    /// Pool of glob fragments exercising `*`, `?`, `**`, and nesting.
    fn glob_frag() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "*.fs",
            "*.fsi",
            "?.fs",
            "**/*.fs",
            "**/*",
            "d/*.fs",
            "d/**/*.fs",
            "e/*.fsi",
        ])
        .prop_map(str::to_string)
    }

    /// A ghost literal naming a file that will not exist in the tree.
    fn ghost_frag() -> impl Strategy<Value = String> {
        prop::sample::select(vec!["ghost.fs", "no/such.fs", "d/missing.fsi"])
            .prop_map(str::to_string)
    }

    // ----- Property test -----

    /// One generated scenario: a file tree, an include spec, and excludes.
    #[derive(Debug)]
    struct Scenario {
        files: BTreeSet<String>,
        include: String,
        excludes: Vec<String>,
    }

    fn scenario() -> impl Strategy<Value = Scenario> {
        prop::collection::vec(rel_path(), 1..=8).prop_flat_map(|paths| {
            let files: BTreeSet<String> = paths.into_iter().collect();
            let known: Vec<String> = files.iter().cloned().collect();
            // include fragment pool: known literal, ghost literal, or glob.
            let known_for_incl = known.clone();
            let incl_frag = prop_oneof![
                3 => glob_frag(),
                2 => prop::sample::select(known_for_incl),
                1 => ghost_frag(),
            ];
            let include = prop::collection::vec(incl_frag, 1..=3).prop_map(|fs| fs.join(";"));
            let known_for_excl = known.clone();
            let excl_frag = prop_oneof![
                2 => glob_frag(),
                2 => prop::sample::select(known_for_excl),
            ];
            let excludes = prop::collection::vec(excl_frag, 0..=2);
            (Just(files), include, excludes).prop_map(|(files, include, excludes)| Scenario {
                files,
                include,
                excludes,
            })
        })
    }

    /// Materialise a scenario's files into a fresh tempdir.
    fn materialise(files: &BTreeSet<String>) -> TempDir {
        let tmp = TempDir::new().unwrap();
        for f in files {
            let full = tmp.path().join(f);
            if let Some(parent) = full.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            fs::write(&full, b"// f\n").unwrap();
        }
        tmp
    }

    #[test]
    fn resolver_agrees_with_reference_over_random_trees() {
        let mut runner = TestRunner::default();
        let strat = scenario();
        let n = 256;
        let (mut nonempty, mut excl_removed, mut had_dup, mut ghost_passed) = (0, 0, 0, 0);
        for _ in 0..n {
            let sc = strat.new_tree(&mut runner).unwrap().current();
            let tmp = materialise(&sc.files);
            let req = GlobRequest {
                base_dir: tmp.path(),
                include: &SpecFragment::split_escaped(&sc.include),
                excludes: &sc
                    .excludes
                    .iter()
                    .flat_map(|e| SpecFragment::split_escaped(e))
                    .collect::<Vec<_>>(),
                observer: &Observer::new(),
            };
            let got = resolve(&req).expect("the fixture is decidable");
            let want = reference(tmp.path(), &sc.files, &sc.include, &sc.excludes);
            assert_eq!(
                got, want,
                "include={:?} excludes={:?} files={:?}",
                sc.include, sc.excludes, sc.files
            );

            // Instrumentation.
            if !got.is_empty() {
                nonempty += 1;
            }
            let without = reference(tmp.path(), &sc.files, &sc.include, &[]);
            if without.len() > want.len() {
                excl_removed += 1;
            }
            let unique: BTreeSet<&PathBuf> = got.iter().collect();
            if unique.len() < got.len() {
                had_dup += 1;
            }
            if sc.include.split(';').any(|f| f == "ghost.fs")
                && got.iter().any(|p| p.ends_with("ghost.fs"))
            {
                ghost_passed += 1;
            }
        }
        // The agreement check is only meaningful if the generator explores
        // each interesting regime. Thresholds chosen far below the expected
        // counts so the false-positive rate is well under 1e-11.
        assert!(nonempty >= 60, "too few non-empty results: {nonempty}/{n}");
        assert!(
            excl_removed >= 20,
            "excludes rarely removed anything: {excl_removed}/{n}"
        );
        assert!(had_dup >= 10, "duplicates rarely arose: {had_dup}/{n}");
        assert!(
            ghost_passed >= 5,
            "ghost literals rarely passed through: {ghost_passed}/{n}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_symlink_cycle_declines() {
        let tmp = fixture();
        std::os::unix::fs::symlink(tmp.path(), tmp.path().join("sub/back")).unwrap();
        let excludes: Vec<SpecFragment> = Vec::new();
        let req = GlobRequest {
            base_dir: tmp.path(),
            include: &SpecFragment::split_escaped("**/*.fs"),
            excludes: &excludes,
            observer: &Observer::new(),
        };
        assert!(matches!(
            resolve(&req),
            Err(GlobDecline::SymlinkCycle { .. })
        ));
        // A single-level glob never descends, so the cycle decides nothing.
        let req = GlobRequest {
            base_dir: tmp.path(),
            include: &SpecFragment::split_escaped("*.fs"),
            excludes: &excludes,
            observer: &Observer::new(),
        };
        assert_eq!(resolve(&req).unwrap().len(), 4);
    }

    #[test]
    fn a_recursive_walk_that_reaches_the_depth_bound_declines() {
        let tmp = TempDir::new().unwrap();
        let mut deep = tmp.path().to_path_buf();
        for _ in 0..=MAX_GLOB_DEPTH {
            deep.push("d");
        }
        fs::create_dir_all(&deep).unwrap();
        fs::write(deep.join("x.fs"), b"// f\n").unwrap();
        let excludes: Vec<SpecFragment> = Vec::new();
        let req = GlobRequest {
            base_dir: tmp.path(),
            include: &SpecFragment::split_escaped("**/*.fs"),
            excludes: &excludes,
            observer: &Observer::new(),
        };
        assert!(matches!(resolve(&req), Err(GlobDecline::DepthLimit { .. })));
    }
}
