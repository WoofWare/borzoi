//! Pure MSBuild-style glob semantics for `.fsproj` item includes.
//!
//! This is the policy half of the glob *seam* (`GlobResolver`): the
//! evaluator never globs, it hands each globbing item element to a
//! caller-supplied resolver. This module is the *pure* core of the
//! resolver this crate ships ([`crate::glob_resolver`]): the port of
//! MSBuild's file matcher ([`file_matcher`]), the split and escaped item
//! fragments the seam carries ([`SpecFragment`]), the allow-list of shapes the
//! resolver commits inside ([`unmodelled_shape`]), the file matcher's
//! legality rules, and MSBuild's order within one fragment's expansion. The
//! file-system listing the walk runs over is taken in `glob_resolver`.
//!
//! ## Order
//!
//! A fragment's expansion is ordered exactly as MSBuild orders it:
//! `EngineFileUtilities.GetFileList` sorts each wildcard fragment's matches
//! with `StringComparer.OrdinalIgnoreCase` before returning them, so the
//! order is a function of the names, not of the file system. Where that sort
//! cannot be reproduced exactly the resolver declines: two matches equal
//! under it (only possible on a case-sensitive file system) leave the order
//! to .NET's unstable `Array.Sort`, and a non-ASCII name would need .NET's
//! per-UTF-16 simple case mapping, which this module does not model.
//! Fragments keep document order, and nothing is deduplicated.

pub(crate) mod file_matcher;

use crate::properties::escaping::{self, Escaped};

/// Why a fragment's expansion cannot be reproduced exactly, so the resolver
/// declines rather than commit a list MSBuild may not produce.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlobDecline {
    /// Two matches of one fragment compare equal under `OrdinalIgnoreCase`
    /// (`A.fs` and `a.fs` on a case-sensitive filesystem). MSBuild orders
    /// them with an unstable sort, so no order is *the* order.
    OrderTie { first: String, second: String },
    /// A fragment matched several files and one name is not ASCII. Its
    /// position under `OrdinalIgnoreCase` depends on .NET's per-UTF-16 simple
    /// case mapping, which is not modelled.
    NonAsciiOrder { path: String },
    /// Whether `path` is selected turns on whether `i` and `I` are one letter.
    /// MSBuild matches some globs by a regular expression that ignores case by
    /// the build's culture (the file matcher, one with a wildcard directory
    /// part; `FileSpecMatcherTester`, an exclude outside its filename-only
    /// branch), and under a Turkish or Azerbaijani culture `i` and `I` are two
    /// letters (oracle-pinned). The build's culture is not observable here.
    CultureDependentCase { path: String },
    /// A recursive walk reached [`crate::glob_resolver`]'s depth bound with
    /// directories still below it, so matches may be missing.
    DepthLimit { dir: String },
    /// The walk met a symbolic link back to a directory already on its path.
    /// What MSBuild does with a cycle is not modelled.
    SymlinkCycle { path: String },
    /// The glob selects a file under `path`, a symbolic link to a directory:
    /// the walk's root, or a directory the walk entered. MSBuild's file matcher
    /// skips such a directory when the link's final target, resolved
    /// lexically, contains the link's path as the build spells it, comparing
    /// ordinally or ignoring case by whether the build's temp directory is
    /// case-sensitive. None of the three is observed here (see
    /// [`crate::glob_resolver`]'s correctness envelope).
    SymlinkedDirectory { path: String },
    /// MSBuild's file matcher refuses the decoded filespec (see
    /// `FileMatcher.IsLegalFileSpec`): `a**b.fs`, a `..` after a wildcard, a `...`.
    /// It then falls back to a different reading per caller, which is not
    /// modelled.
    IllegalFilespec { pattern: String },
    /// A glob include, or an exclude the file matcher is handed, enumerates a
    /// drive from its root (`/**`: `FileMatcher.IsDriveEnumeratingWildcardPattern`).
    /// `EngineFileUtilities.GetFileList` then lists nothing for the include,
    /// or, for such an exclude, for every include of the element, and logs a
    /// warning (or fails, under `MSBUILDFAILONDRIVEENUMERATINGWILDCARD`), which
    /// is not modelled.
    DriveEnumeratingWildcard { spec: String },
    /// A spec, or a name a glob would match, is outside the shapes the
    /// resolver models ([`Unmodelled`] says which). The resolver commits only
    /// inside an allow-list the MSBuild differentials verify, so a shape
    /// nobody has checked declines here instead of matching the plain way.
    OutsideModelledShape { spec: String, shape: Unmodelled },
}

impl std::fmt::Display for GlobDecline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GlobDecline::OrderTie { first, second } => write!(
                f,
                "`{first}` and `{second}` differ only in case, so MSBuild's order between them is unspecified"
            ),
            GlobDecline::NonAsciiOrder { path } => write!(
                f,
                "`{path}` has a non-ASCII name, whose position in MSBuild's case-insensitive order is not modelled"
            ),
            GlobDecline::CultureDependentCase { path } => write!(
                f,
                "whether `{path}` is selected depends on whether the build's culture folds `i` onto `I`"
            ),
            GlobDecline::DepthLimit { dir } => {
                write!(
                    f,
                    "the recursive walk stopped at its depth bound in `{dir}`"
                )
            }
            GlobDecline::SymlinkCycle { path } => {
                write!(f, "the symbolic link `{path}` closes a directory cycle")
            }
            GlobDecline::SymlinkedDirectory { path } => write!(
                f,
                "a match lies under the symbolic link `{path}`, which MSBuild skips when its target contains it, by a rule that depends on the build's temp directory"
            ),
            GlobDecline::IllegalFilespec { pattern } => write!(
                f,
                "MSBuild's file matcher refuses the pattern `{pattern}`, and its fallback is not modelled"
            ),
            GlobDecline::DriveEnumeratingWildcard { spec } => write!(
                f,
                "`{spec}` enumerates a drive from its root, which MSBuild warns about and lists nothing for"
            ),
            GlobDecline::OutsideModelledShape { spec, shape } => write!(
                f,
                "`{spec}` {shape}, which the glob resolver does not model"
            ),
        }
    }
}

/// One `;`-separated fragment of an item `Include` or `Exclude`, still in
/// MSBuild's **escaped** domain — the unit [`crate::GlobRequest`] carries
/// across the resolver seam.
///
/// MSBuild splits a spec on the `;`s of its escaped text, classifies each
/// fragment as a glob or a literal on that escaped text, and only then
/// decodes it. A fragment is therefore the product of the split: it never
/// holds a live `;`, so nothing downstream has a reason to split it again,
/// and its classification ([`Self::is_wildcard`]) is asked of the escaped
/// text this type keeps. Decoding is the last step, at [`Self::unescape`].
/// An escaped `%3b` decodes to a `;` that is part of a filename, and an
/// escaped `%2a` to a star that is part of one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecFragment(Escaped);

impl SpecFragment {
    /// Split an escaped item spec into its fragments as MSBuild does: on
    /// every `;` of the escaped text, each fragment trimmed, empty ones
    /// dropped. `a%3bb.fs;z.fs` is two fragments, the first naming `a;b.fs`.
    pub fn split_escaped(spec: &str) -> Vec<SpecFragment> {
        Escaped::from_xml(spec)
            .split_list()
            .map(SpecFragment)
            .collect()
    }

    /// One fragment the evaluator has already split off an escaped spec
    /// (trimmed, non-empty, no live `;`).
    pub(crate) fn from_split(fragment: &str) -> SpecFragment {
        debug_assert!(!fragment.contains(';') && fragment.trim() == fragment);
        SpecFragment(Escaped::from_xml(fragment))
    }

    /// The fragment's escaped spelling, for display.
    pub fn as_escaped(&self) -> &str {
        self.0.as_escaped()
    }

    /// The fragment at its point of use: decoded, exactly once.
    pub fn unescape(&self) -> String {
        self.0.unescape()
    }

    /// Whether MSBuild expands this fragment as a glob
    /// (`EngineFileUtilities.FilespecHasWildcards`): a live `*`/`?` and no
    /// escaped one. When true, every `*`/`?` in [`Self::unescape`] is a
    /// wildcard; when false, the decoded text is a literal path, stars and all
    /// (`a%2a*.fs` is the one item `a**.fs`).
    pub fn is_wildcard(&self) -> bool {
        self.0.is_filespec_wildcard()
    }

    /// Whether this `Exclude` fragment takes part in excluding from a
    /// **glob** include — MSBuild's `EngineFileUtilities.IsValidExclude`,
    /// which drops an exclude carrying both a live and an escaped wildcard
    /// before the file matcher sees any. The ones it keeps are decoded and
    /// then parsed as patterns, so an escaped `%2a` in one *is* a wildcard
    /// there: `Include="*.fs" Exclude="a%2ab.fs"` excludes `axb.fs`, while
    /// against the literal include `axb.fs` the same exclude matches only a
    /// file named `a*b.fs` (both pinned against `dotnet msbuild` 10.0.301).
    pub fn excludes_from_globs(&self) -> bool {
        !(escaping::has_live_wildcard(self.0.as_escaped())
            && escaping::contains_escaped_wildcards(self.0.as_escaped()))
    }
}

/// Which allow-list rule a spec or name breaks
/// ([`GlobDecline::OutsideModelledShape`]). Each names MSBuild behaviour the
/// file matcher's port does not model, so all of it declines.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Unmodelled {
    /// A character outside printable ASCII. MSBuild's `?` matches one UTF-16
    /// code unit, not one character, and its `OrdinalIgnoreCase` folds
    /// non-ASCII letters onto ASCII ones (`ı` onto `I`).
    NonAscii,
    /// A trailing path separator: MSBuild keeps the empty filename part, so
    /// the spec names a directory, not a file.
    TrailingSeparator,
    /// A segment ending in `.` or a space (other than `.` and `..`), which
    /// MSBuild's Windows-derived filename rules treat specially (`*.fs.`).
    TrailingDotOrSpace,
    /// One of `"<>|:`, which Windows forbids in a filename and MSBuild's
    /// matchers treat specially (as wildcards, or as a drive separator).
    WindowsReservedCharacter,
    /// A glob's fixed directory has a `~` in a segment after its first, which
    /// MSBuild's file matcher resolves as a Windows short name relative to the
    /// build's working directory (`glob::has_tilde_after_first_fixed_segment`).
    TildeInFixedDirectory,
}

impl std::fmt::Display for Unmodelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Unmodelled::NonAscii => "has a character outside printable ASCII",
            Unmodelled::TrailingSeparator => "ends in a path separator",
            Unmodelled::TrailingDotOrSpace => "has a segment ending in `.` or a space",
            Unmodelled::WindowsReservedCharacter => "has one of `\"<>|:`",
            Unmodelled::TildeInFixedDirectory => {
                "has a `~` in a fixed directory segment after the first"
            }
        })
    }
}

/// The allow-list: whether a **decoded** spec, or a name a glob would match,
/// is in the shape the resolver models, and if not, which rule it breaks.
/// Printable ASCII; no trailing separator, and no segment ending in `.` or a
/// space (`.` and `..` themselves are segments, not endings); none of
/// `"<>|:`. Runs of separators collapse, as MSBuild's do (`bin\/**`, the
/// SDK's own spelling of an output exclude, is `bin/**`). A `*` or `?` is allowed: in a glob it is a wildcard, and in a
/// literal name (decoded from `%2a`) MSBuild compares it as written
/// ([`compares_unnormalised`]).
pub fn unmodelled_shape(spec: &str) -> Option<Unmodelled> {
    if !spec.chars().all(|c| (' '..='~').contains(&c)) {
        return Some(Unmodelled::NonAscii);
    }
    if spec.contains(['"', '<', '>', '|', ':']) {
        return Some(Unmodelled::WindowsReservedCharacter);
    }
    if spec.ends_with(['/', '\\']) {
        return Some(Unmodelled::TrailingSeparator);
    }
    for seg in spec.split(['/', '\\']) {
        if seg != "." && seg != ".." && seg.ends_with(['.', ' ']) {
            return Some(Unmodelled::TrailingDotOrSpace);
        }
    }
    None
}

/// Characters that make MSBuild reject a filespec outright
/// (`FileUtilities.InvalidPathChars`): `|`, NUL and the C0 controls.
fn is_invalid_path_char(c: char) -> bool {
    c == '|' || c < ' '
}

/// MSBuild's `FileMatcher.SplitFileSpec`: the fixed directory (up to the
/// last separator before the first wildcard), the wildcard directory part
/// (from there to the last separator), and the filename part. A filename
/// part of `**` moves into the directory part and leaves `*.*` behind, as
/// MSBuild's does.
pub(crate) fn split_filespec(spec: &str) -> (&str, String, String) {
    let is_sep = |c: char| c == '/' || c == '\\';
    let (dirs, filename) = match spec.rfind(is_sep) {
        Some(last_sep) => (&spec[..=last_sep], &spec[last_sep + 1..]),
        None => ("", spec),
    };
    let (fixed, mut wildcard_dir) = match dirs.find(['*', '?']) {
        None => (dirs, String::new()),
        Some(first_wild) => {
            let cut = dirs[..first_wild].rfind(is_sep).map_or(0, |i| i + 1);
            (&dirs[..cut], dirs[cut..].to_string())
        }
    };
    let mut filename = filename.to_string();
    if filename == "**" {
        wildcard_dir.push_str("**/");
        filename = "*.*".to_string();
    }
    (fixed, wildcard_dir, filename)
}

/// `FileMatcher.HasMisplacedRecursiveOperator`: a `**` that is not a whole
/// path segment.
fn has_misplaced_recursive_operator(part: &str) -> bool {
    let b = part.as_bytes();
    let is_slash = |c: u8| c == b'/' || c == b'\\';
    (0..b.len().saturating_sub(1)).any(|i| {
        b[i] == b'*'
            && b[i + 1] == b'*'
            && !((i == 0 || is_slash(b[i - 1])) && i + 2 < b.len() && is_slash(b[i + 2]))
    })
}

/// Whether MSBuild's file matcher accepts a **decoded** glob filespec at all:
/// `FileMatcher.RawFileSpecIsValid` and `IsLegalFileSpec`. It refuses a
/// filespec holding an invalid path character, a `...`, or a `:` anywhere but
/// the second character; and one whose wildcard directory part holds `..`, or
/// whose `**` is not a whole path segment (`a**b.fs`). What MSBuild then does
/// differs by caller — an illegal include is kept as a literal item, an
/// illegal exclude falls back to a literal comparison — so the resolver
/// declines rather than reproduce each fallback.
pub fn is_legal_filespec(spec: &str) -> bool {
    if !raw_filespec_is_valid(spec) {
        return false;
    }
    let (_, wildcard_dir, filename) = split_filespec(spec);
    !wildcard_dir.contains("..")
        && !has_misplaced_recursive_operator(&wildcard_dir)
        && !has_misplaced_recursive_operator(&filename)
}

/// `FileMatcher.RawFileSpecIsValid`: no invalid path character, no `...`, and
/// no `:` but the second character.
fn raw_filespec_is_valid(spec: &str) -> bool {
    !spec.chars().any(is_invalid_path_char)
        && !spec.contains("...")
        && spec.rfind(':').is_none_or(|colon| colon == 1)
}

/// Whether `EngineFileUtilities.GetFileList` finds a decoded spec to enumerate
/// a drive from its root (`FileMatcher.IsDriveEnumeratingWildcardPattern` of
/// its `GetFileSpecInfo` parts, on a Unix host): a fixed directory of nothing
/// but slashes before a wildcard directory part that starts with `**`, as
/// `/**/*.fs` has.
pub fn is_drive_enumerating_filespec(spec: &str) -> bool {
    if !raw_filespec_is_valid(spec) {
        return false;
    }
    let (fixed, wildcard_dir, _) = split_filespec(spec);
    !fixed.is_empty()
        && fixed.bytes().all(|b| b == b'/' || b == b'\\')
        && wildcard_dir.starts_with("**")
}

/// Whether a **literal** spelling is one MSBuild compares without normalising
/// it (`FileUtilities.PathIsInvalid`, consulted by
/// `NormalizePathForComparisonNoThrow`): one holding an invalid path
/// character, or whose filename part holds a character Windows forbids in a
/// filename (`"<>|:*?`, NUL, the C0 controls). Such a spelling is compared as
/// written, so `./a*b.fs`, `a*b.fs` and its absolute spelling are three
/// different items to an `Exclude`, while `./ab.fs` and `ab.fs` are one.
pub fn compares_unnormalised(spelling: &str) -> bool {
    if spelling.chars().any(is_invalid_path_char) {
        return true;
    }
    let filename = spelling.rsplit(['/', '\\']).next().unwrap_or(spelling);
    filename
        .chars()
        .any(|c| matches!(c, '"' | '<' | '>' | '|' | ':' | '*' | '?') || c < ' ')
}

/// Whether a decoded glob's fixed directory part has a `~` in a segment
/// after its first. MSBuild's file matcher takes such a segment for a
/// Windows short name (`FileMatcher.GetLongPathName`) and swaps it for the
/// one entry that matches it ignoring case, looked up relative to the
/// build's working directory, which is not observable here (oracle-pinned:
/// `sub/A~B/*.fs` finds `sub/a~b/x.fs` from the project directory and
/// nothing from its parent). The first segment is looked up in an empty
/// path, which finds nothing, so it stays as written.
pub fn has_tilde_after_first_fixed_segment(spec: &str) -> bool {
    let (fixed, _, _) = split_filespec(spec);
    fixed
        .split(['/', '\\'])
        .filter(|seg| !seg.is_empty())
        .skip(1)
        .any(|seg| seg.contains('~'))
}

/// Normalise a path/pattern fragment: backslashes to `/`, collapse runs
/// of `/`, drop empty and lone-`.` (current-directory) segments. Returns
/// the surviving segments. `..` is *not* resolved here — that needs the
/// base directory and is the filesystem layer's job (9b-2); candidates and
/// patterns reaching this matcher are expected base-relative without `..`.
pub fn split_segments(raw: &str) -> Vec<&str> {
    raw.split(['/', '\\'])
        .filter(|s| !s.is_empty() && *s != ".")
        .collect()
}

/// The length in bytes of the longest prefix all of `strings` share.
fn common_prefix_len(strings: &[String]) -> usize {
    let Some((first, rest)) = strings.split_first() else {
        return 0;
    };
    rest.iter().fold(first.len(), |len, s| {
        first.as_bytes()[..len]
            .iter()
            .zip(s.as_bytes())
            .take_while(|(a, b)| a == b)
            .count()
    })
}

/// `StringComparer.OrdinalIgnoreCase` restricted to ASCII: compare UTF-16 code
/// units after upper-casing. Upper, not lower, is load-bearing: `_` (0x5F)
/// sorts *after* `Z` (0x5A) but before `z` (0x7A).
fn ordinal_ignore_case(a: &str, b: &str) -> std::cmp::Ordering {
    a.bytes()
        .map(|c| c.to_ascii_uppercase())
        .cmp(b.bytes().map(|c| c.to_ascii_uppercase()))
}

/// Sort one fragment's matches the way MSBuild does, or decline where that
/// order is not reproducible (see [`GlobDecline::OrderTie`] and
/// [`GlobDecline::NonAsciiOrder`]). A single match has no order to get wrong.
///
/// The text every match shares — the glob root and the project directory
/// above it — cannot decide their order, so only what follows it must be
/// ASCII: a checkout under `/home/José/` still commits.
pub(crate) fn sort_like_msbuild(matched: &mut [String]) -> Result<(), GlobDecline> {
    if matched.len() < 2 {
        return Ok(());
    }
    let shared = common_prefix_len(matched);
    // A shared prefix ending inside a multi-byte character leaves the rest of
    // that character in every suffix, which then fails the ASCII check.
    if let Some(path) = matched.iter().find(|m| !m.as_bytes()[shared..].is_ascii()) {
        return Err(GlobDecline::NonAsciiOrder { path: path.clone() });
    }
    matched.sort_by(|a, b| ordinal_ignore_case(a, b));
    // Identical strings are interchangeable, so only *distinct* names that
    // compare equal leave the order open.
    if let Some(pair) = matched
        .windows(2)
        .find(|pair| pair[0] != pair[1] && ordinal_ignore_case(&pair[0], &pair[1]).is_eq())
    {
        return Err(GlobDecline::OrderTie {
            first: pair[0].clone(),
            second: pair[1].clone(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sort_orders_like_ordinal_ignore_case() {
        // Probed against `dotnet msbuild` (10.0.301): upper-case folding puts
        // `_` after `Z`; `-` < `.` < `/` keeps `ab-c.fs`, `ab.fs`, `ab/x.fs`
        // in that order. The generated differential pins it in general.
        let mut got: Vec<String> = [
            "_u.fs", "Zeta.fs", "alpha.fs", "ab/x.fs", "ab.fs", "ab-c.fs", "Beta.fs",
        ]
        .map(String::from)
        .to_vec();
        sort_like_msbuild(&mut got).unwrap();
        assert_eq!(
            got,
            [
                "ab-c.fs", "ab.fs", "ab/x.fs", "alpha.fs", "Beta.fs", "Zeta.fs", "_u.fs"
            ]
        );
    }

    #[test]
    fn a_non_ascii_prefix_shared_by_every_match_does_not_decline() {
        let mut got = vec![
            "/home/José/app/b.fs".to_string(),
            "/home/José/app/a.fs".to_string(),
        ];
        sort_like_msbuild(&mut got).unwrap();
        assert_eq!(got, ["/home/José/app/a.fs", "/home/José/app/b.fs"]);
        // Where the matches differ in a non-ASCII position, it still declines.
        let mut got = vec!["/home/José/a.fs".to_string(), "/home/Josa/a.fs".to_string()];
        let got = sort_like_msbuild(&mut got);
        assert!(
            matches!(got, Err(GlobDecline::NonAsciiOrder { .. })),
            "{got:?}"
        );
    }

    #[test]
    fn sort_declines_a_case_only_tie() {
        // Possible only on a case-sensitive filesystem: MSBuild's unstable sort
        // leaves the pair's order unspecified.
        let got = sort_like_msbuild(&mut ["a.fs".to_string(), "A.fs".to_string()]);
        assert!(matches!(got, Err(GlobDecline::OrderTie { .. })), "{got:?}");
    }

    #[test]
    fn sort_declines_non_ascii_order_but_not_a_lone_match() {
        let got = sort_like_msbuild(&mut ["é.fs".to_string(), "a.fs".to_string()]);
        assert!(
            matches!(got, Err(GlobDecline::NonAsciiOrder { .. })),
            "{got:?}"
        );
        // One match has no order to get wrong.
        assert_eq!(sort_like_msbuild(&mut ["é.fs".to_string()]), Ok(()));
    }

    /// `FileMatcher.GetLongPathName` looks up a `~` segment after the first.
    #[test]
    fn a_tilde_after_the_first_fixed_segment_is_found() {
        for found in ["sub/a~b/*.fs", "/home/u~/proj/*.fs", "a/b/c~/**/x.fs"] {
            assert!(has_tilde_after_first_fixed_segment(found), "{found}");
        }
        for not in ["a~b/*.fs", "/a~b/*.fs", "sub/*~.fs", "sub/a*/b~/x.fs", "~"] {
            assert!(!has_tilde_after_first_fixed_segment(not), "{not}");
        }
    }

    /// `FileMatcher.RawFileSpecIsValid` and `IsLegalFileSpec`, case by case
    /// from MSBuild's source.
    #[test]
    fn legality_follows_msbuilds_file_matcher() {
        for legal in [
            "*.fs",
            "**/*.fs",
            "src/**/x/*.fs",
            "**",
            "../shared/*.fs",
            "/abs/**/*.fs",
            "C:/x/*.fs",
            "a.fs",
        ] {
            assert!(is_legal_filespec(legal), "{legal}");
        }
        for illegal in [
            // `**` must be a whole segment.
            "a**b.fs",
            "**a/*.fs",
            "src/x**/*.fs",
            "*.fs**",
            // `..` may not follow a wildcard.
            "*/../x.fs",
            "**/../*.fs",
            // `...` anywhere, a `:` anywhere but second, an invalid char.
            "a.../*.fs",
            "ab:c*.fs",
            "a|b*.fs",
            "a\u{1}*.fs",
        ] {
            assert!(!is_legal_filespec(illegal), "{illegal}");
        }
    }

    /// `FileUtilities.PathIsInvalid`: only the filename part is checked for
    /// the characters Windows forbids in a filename.
    #[test]
    fn unnormalised_comparison_follows_path_is_invalid() {
        for raw in ["a*b.fs", "./a?b.fs", "/abs/a:b.fs", "x<y", "a|b/c.fs"] {
            assert!(compares_unnormalised(raw), "{raw}");
        }
        for normalised in ["ab.fs", "./ab.fs", "sub/../ab.fs", "a*b/c.fs", "a b.fs"] {
            assert!(!compares_unnormalised(normalised), "{normalised}");
        }
    }

    /// The allow-list admits the shapes the differentials verify and names
    /// the rule anything else breaks.
    #[test]
    fn the_allow_list_names_what_it_refuses() {
        for modelled in [
            "a.fs",
            "./a.fs",
            "../shared/*.fs",
            "/abs/**/*.fs",
            "a*b.fs",
            "a b.fs",
            "a;b.fs",
            "bin\\/**",
            "pct%.fs",
        ] {
            assert_eq!(unmodelled_shape(modelled), None, "{modelled}");
        }
        for (spec, shape) in [
            ("\u{dc}.fs", Unmodelled::NonAscii),
            ("\u{1f98b}?.fs", Unmodelled::NonAscii),
            ("a\u{1}.fs", Unmodelled::NonAscii),
            ("*.fs/", Unmodelled::TrailingSeparator),
            ("sub\\", Unmodelled::TrailingSeparator),
            ("*.fs.", Unmodelled::TrailingDotOrSpace),
            ("sub./a.fs", Unmodelled::TrailingDotOrSpace),
            ("a.fs ", Unmodelled::TrailingDotOrSpace),
            ("a:b.fs", Unmodelled::WindowsReservedCharacter),
            ("a<b.fs", Unmodelled::WindowsReservedCharacter),
            ("a\"b.fs", Unmodelled::WindowsReservedCharacter),
        ] {
            assert_eq!(unmodelled_shape(spec), Some(shape), "{spec}");
        }
    }
}
