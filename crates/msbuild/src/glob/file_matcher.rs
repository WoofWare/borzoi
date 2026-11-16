//! A port of MSBuild's file matcher (`src/Framework/Utilities/FileMatcher.cs`
//! of MSBuild 18.9, the `vs18.9` branch, which the installed SDK carries): the
//! walk a glob include is expanded by, and the regular expressions it and
//! `FileSpecMatcherTester` match paths with.
//!
//! Everything here is pure. The walk reads the file system only through a
//! [`Listing`] the caller took beforehand, and the one existence question
//! `GetFileSearchData` asks of a spec's fixed directory is answered by the
//! caller too ([`FileSpec::probe`], then [`FileSpec::search`]).
//!
//! The port follows the source's structure function by function, keeping its
//! names, so a reading of one can be checked against the other:
//!
//! - [`is_match`] is `FileMatcher.IsMatch`, the name matcher that folds ASCII
//!   case on every culture, ported loop for loop, its tail check included.
//! - [`FileSpecRegex`] is `RegularExpressionFromFileSpec` as a token list over
//!   the few constructs it emits (`[^/\\]*`, `.`, `[/\\]+`, `LeftDirs`,
//!   `MiddleDirs`, and the trailing-dot forms), matched with the case
//!   equivalence of the build's culture as a parameter ([`Culture`]): a .NET
//!   regular expression that ignores case keeps `i` and `I` apart under a
//!   Turkish culture.
//! - [`FileSpec`] is `GetFileSpecInfo` and `GetFileSearchData`.
//! - [`get_files`] is `GetFilesImplementation`, which places each exclude
//!   against the include's walk root (the three base-directory branches), and
//!   `GetFilesRecursive` with `GetFilesRecursiveStep`, `excludeNextSteps` and
//!   `searchesToExcludeInSubdirs`.
//!
//! Path strings are compared and built as .NET builds them on a Unix host:
//! `Path.Combine`, `Path.Join`, `Path.GetFileName` (whose only separator is
//! `/`), and the file matcher's own `Normalize`. Specs reach this module with
//! their backslashes already turned to `/`, as `FileUtilities.FixFilePath`
//! does.
//!
//! The walk filters each listing as the evaluation context's cache has the
//! file matcher filter it: listed without a pattern, then by
//! `IsFileNameMatch`, so neither the host's own pattern matching nor the
//! Linux-only branch of `GetFilesForStep` decides anything, and the walk is
//! the same on every host.
//!
//! What the port leaves to its caller: the symbolic-link skip at the head of
//! `GetFilesRecursive` (every file carries the link it was found through, if
//! any, and the caller declines where that could matter), and
//! `GetLongPathName`'s short-name lookup of a `~` segment.

use super::{is_legal_filespec, split_filespec};

/// How a .NET regular expression compiled with `RegexOptions.IgnoreCase`
/// compares letters, by the build's culture. MSBuild compiles the file
/// matcher's expressions under the culture the build runs in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Culture {
    /// The invariant culture, and every culture that compares ASCII letters as
    /// it does.
    Invariant,
    /// A Turkish or Azerbaijani culture: `i` pairs with `İ` and `I` with `ı`,
    /// so `i` and `I` are two letters.
    Turkish,
}

impl Culture {
    /// Every case equivalence a build can apply.
    pub const ALL: [Culture; 2] = [Culture::Invariant, Culture::Turkish];

    /// The key a regular expression compares a UTF-16 unit by under this
    /// culture: two units match when their keys are equal. Folds onto ASCII
    /// that `glob_resolver` declines rather than relies on (the Kelvin sign,
    /// `İ`) are kept, so this reads them as MSBuild does if one is ever met.
    fn regex_key(self, unit: u16) -> u32 {
        const DOTLESS_I: u32 = 0x131;
        match (self, unit) {
            (Culture::Turkish, 0x49) => DOTLESS_I,
            (_, 0x130) => u32::from(b'i'),
            (_, 0x212a) => u32::from(b'k'),
            (_, u) if u < 0x80 => u32::from(u8::try_from(u).unwrap_or(0).to_ascii_lowercase()),
            (_, u) => simple_lower(u),
        }
    }
}

/// A UTF-16 unit's simple lower-case mapping, where it has a one-unit one.
fn simple_lower(unit: u16) -> u32 {
    let Some(c) = char::from_u32(u32::from(unit)) else {
        return u32::from(unit);
    };
    let mut lower = c.to_lowercase();
    match (lower.next(), lower.next()) {
        (Some(l), None) if (l as u32) < 0x10000 => l as u32,
        _ => u32::from(unit),
    }
}

/// A UTF-16 unit's simple upper-case mapping, where it has a one-unit one:
/// how `StringComparison.OrdinalIgnoreCase` compares a unit.
fn simple_upper(unit: u16) -> u16 {
    if unit < 0x80 {
        return u16::from(u8::try_from(unit).unwrap_or(0).to_ascii_uppercase());
    }
    let Some(c) = char::from_u32(u32::from(unit)) else {
        return unit;
    };
    let mut upper = c.to_uppercase();
    match (upper.next(), upper.next()) {
        (Some(u), None) => u16::try_from(u as u32).unwrap_or(unit),
        _ => unit,
    }
}

fn utf16(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

/// `string.Equals(a, b, StringComparison.OrdinalIgnoreCase)`.
pub fn eq_ordinal_ignore_case(a: &str, b: &str) -> bool {
    let (a, b) = (utf16(a), utf16(b));
    a.len() == b.len()
        && a.iter()
            .zip(&b)
            .all(|(&x, &y)| simple_upper(x) == simple_upper(y))
}

/// `a.StartsWith(b, StringComparison.OrdinalIgnoreCase)`.
fn starts_with_ordinal_ignore_case(a: &[u16], b: &[u16]) -> bool {
    a.len() >= b.len()
        && a.iter()
            .zip(b)
            .all(|(&x, &y)| simple_upper(x) == simple_upper(y))
}

/// The key a `StringComparer.OrdinalIgnoreCase` dictionary files a string
/// under.
fn ordinal_ignore_case_key(s: &str) -> Vec<u16> {
    s.encode_utf16().map(simple_upper).collect()
}

fn is_any_slash(unit: u16) -> bool {
    unit == u16::from(b'/') || unit == u16::from(b'\\')
}

/// `Path.Combine(a, b)` on a Unix host, whose only separator is `/`.
pub fn path_combine(a: &str, b: &str) -> String {
    if b.is_empty() {
        a.to_string()
    } else if a.is_empty() || b.starts_with('/') {
        b.to_string()
    } else if a.ends_with('/') {
        format!("{a}{b}")
    } else {
        format!("{a}/{b}")
    }
}

/// `Path.Join(a, b)` on a Unix host.
fn path_join(a: &str, b: &str) -> String {
    if a.is_empty() {
        b.to_string()
    } else if b.is_empty() {
        a.to_string()
    } else if a.ends_with('/') || b.starts_with('/') {
        format!("{a}{b}")
    } else {
        format!("{a}/{b}")
    }
}

/// `Path.GetFileName` on a Unix host: what follows the last `/`.
pub fn file_name(path: &str) -> &str {
    path.rsplit('/').next().unwrap_or(path)
}

/// `Path.GetFullPath` of a rooted path on a Unix host: `.` segments and runs
/// of `/` dropped and `..` taking the segment before it, lexically (a `..` at
/// the root stays there). A trailing `/` is kept.
pub fn full_path(path: &str) -> String {
    debug_assert!(path.starts_with('/'), "{path} is rooted");
    let mut segs: Vec<&str> = Vec::new();
    for seg in path.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                segs.pop();
            }
            seg => segs.push(seg),
        }
    }
    let mut out = format!("/{}", segs.join("/"));
    if path.ends_with('/') && !out.ends_with('/') {
        out.push('/');
    }
    out
}

/// `FileMatcher.Normalize`: runs of slashes collapse to the host's separator,
/// a trailing run is dropped, and a leading root keeps its own spelling.
pub fn normalize(s: &str) -> String {
    if s.is_empty() {
        return String::new();
    }
    let b = s.as_bytes();
    let is_slash = |c: u8| c == b'/' || c == b'\\';
    let skip_slashes = |mut i: usize| {
        while i < b.len() && is_slash(b[i]) {
            i += 1;
        }
        i
    };
    let mut out = String::with_capacity(s.len());
    let mut index = 0;
    if b.len() >= 2 && b[1] == b':' && b[0].is_ascii_alphabetic() {
        out.push_str(&s[..2]);
        let i = skip_slashes(2);
        if index != i {
            out.push('\\');
        }
        index = i;
    } else if s.starts_with('/') {
        out.push('/');
        index = skip_slashes(1);
    } else if s.starts_with("\\\\") {
        out.push_str("\\\\");
        index = skip_slashes(2);
    } else if s.starts_with('\\') {
        out.push('\\');
        index = skip_slashes(1);
    }
    while index < b.len() {
        let after_slashes = skip_slashes(index);
        if after_slashes >= b.len() {
            break;
        } else if after_slashes > index {
            out.push('/');
        }
        let next_slash = b[after_slashes..]
            .iter()
            .position(|&c| is_slash(c))
            .map_or(b.len(), |i| after_slashes + i);
        out.push_str(&s[after_slashes..next_slash]);
        index = next_slash;
    }
    out
}

/// `String.TrimTrailingSlashes`.
fn trim_trailing_slashes(s: &str) -> &str {
    s.trim_end_matches(['/', '\\'])
}

/// `FileMatcher.IsRecursiveDirectoryMatch`.
pub fn is_recursive_directory_match(path: &str) -> bool {
    trim_trailing_slashes(path) == "**"
}

/// `FileMatcher.IsAllFilesWildcard`: `*` or `*.*`.
pub fn is_all_files_wildcard(pattern: &str) -> bool {
    pattern == "*" || pattern == "*.*"
}

/// `FileMatcher.IsFileNameMatch`: [`is_match`] on the path's file name.
pub fn is_file_name_match(path: &str, pattern: &str) -> bool {
    is_match(file_name(path), pattern)
}

/// `FileMatcher.IsMatch`: whether `input` matches the wildcard `pattern`
/// (`*` any run, `?` any one UTF-16 unit), ASCII letters compared ignoring
/// case and other units by `OrdinalIgnoreCase`. Ported loop for loop, so its
/// shortcuts (the tail check after a `*`, the skip to the next matching
/// character) answer as MSBuild's do. MSBuild refuses an empty input with an
/// internal error; no listing holds an empty name, so that is unreachable
/// here, and it answers `false`.
pub fn is_match(input: &str, pattern: &str) -> bool {
    let input = utf16(input);
    let pattern = utf16(pattern);
    debug_assert!(!input.is_empty(), "IsMatch is never handed an empty input");
    if input.is_empty() {
        return false;
    }
    let star = u16::from(b'*');
    let question = u16::from(b'?');
    let compare_ignore_case = |i: usize, p: usize| {
        let (ic, pc) = (input[i], pattern[p]);
        let ic_lower = ic | 0x20;
        if (u16::from(b'a')..=u16::from(b'z')).contains(&ic_lower) {
            return ic_lower == (pc | 0x20);
        }
        if ic < 128 || pc < 128 {
            return ic == pc;
        }
        simple_upper(ic) == simple_upper(pc)
    };
    let mut pattern_length = pattern.len();
    let mut input_length = input.len();
    let mut pattern_tmp: Option<usize> = None;
    let mut input_tmp = 0usize;
    let mut p = 0usize;
    let mut i = 0usize;
    let mut tail_checked = false;
    while i < input_length {
        if p < pattern_length {
            if pattern[p] == star {
                p += 1;
                while p < pattern_length && pattern[p] == star {
                    p += 1;
                }
                if p >= pattern_length {
                    return true;
                }
                if !tail_checked {
                    let mut input_tail = input_length;
                    let mut pattern_tail = pattern_length;
                    while p < pattern_tail && input_tail > i {
                        pattern_tail -= 1;
                        input_tail -= 1;
                        if pattern[pattern_tail] == star {
                            break;
                        }
                        if !compare_ignore_case(input_tail, pattern_tail)
                            && pattern[pattern_tail] != question
                        {
                            return false;
                        }
                        if p == pattern_tail {
                            return true;
                        }
                    }
                    input_length = input_tail + 1;
                    pattern_length = pattern_tail + 1;
                    tail_checked = true;
                }
                if pattern[p] != question {
                    while !compare_ignore_case(i, p) {
                        i += 1;
                        if i >= input_length {
                            return false;
                        }
                    }
                }
                pattern_tmp = Some(p);
                input_tmp = i;
                continue;
            }
            if compare_ignore_case(i, p) || pattern[p] == question {
                p += 1;
                i += 1;
                continue;
            }
        }
        let Some(tmp) = pattern_tmp else {
            return false;
        };
        p = tmp;
        i = input_tmp;
        input_tmp += 1;
    }
    while p < pattern_length && pattern[p] == star {
        p += 1;
    }
    p >= pattern_length
}

/// One construct of a file spec's regular expression
/// (`FileMatcher.FileSpecRegexParts`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegexTok {
    /// A literal UTF-16 unit, compared ignoring case by the culture.
    Unit(u16),
    /// `[^/\\]*`: any run without a separator.
    AnyNonSeparator,
    /// `[^\.]`: one unit that is not a dot (half of `AnySingleCharacterButDot`,
    /// `[^\.].`, whose other half is [`RegexTok::SingleCharacter`]).
    NotDot,
    /// `[^\.]*`: any run without a dot.
    AnythingButDot,
    /// `.`: one unit other than a line feed.
    SingleCharacter,
    /// `[/\\]+`: one or more separators.
    DirSeparator,
    /// `((.*/)|(.*\\)|())`: nothing, or a run ending in a separator.
    LeftDirs,
    /// `((/)|(\\)|(/.*/)|(/.*\\)|(\\.*\\)|(\\.*/))`: a separator, or two with
    /// a run between.
    MiddleDirs,
}

/// The regular expression `FileMatcher.RegularExpressionFromFileSpec` builds
/// for a split file spec, anchored at both ends, as the tokens it is made of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileSpecRegex {
    toks: Vec<RegexTok>,
}

/// `FileMatcher.LastIndexOfDirectorySequence`: from a separator, past every
/// further separator and `./` that follows it.
fn last_index_of_directory_sequence(s: &[u16], start: usize) -> usize {
    if start >= s.len() || !is_any_slash(s[start]) {
        return start;
    }
    let dot = u16::from(b'.');
    let mut i = start;
    loop {
        if i >= s.len() {
            break;
        }
        let is_separator = i + 1 < s.len() && is_any_slash(s[i + 1]);
        let is_relative_separator = i + 2 < s.len() && s[i + 1] == dot && is_any_slash(s[i + 2]);
        if is_separator {
            i += 1;
        } else if is_relative_separator {
            i += 2;
        } else {
            break;
        }
    }
    i
}

/// `FileMatcher.LastIndexOfDirectoryOrRecursiveSequence`: from a `**`, past
/// every `/**` and directory sequence that follows it; otherwise
/// [`last_index_of_directory_sequence`].
fn last_index_of_directory_or_recursive_sequence(s: &[u16], start: usize) -> usize {
    let star = u16::from(b'*');
    let is_recursive_sequence = start + 1 < s.len() && s[start] == star && s[start + 1] == star;
    if !is_recursive_sequence {
        return last_index_of_directory_sequence(s, start);
    }
    let mut i = start + 2;
    while i < s.len() {
        i = last_index_of_directory_sequence(s, i);
        let is_recursive_operator = i + 2 < s.len() && s[i + 1] == star && s[i + 2] == star;
        if is_recursive_operator {
            i += 3;
        } else {
            break;
        }
    }
    i + 1
}

impl FileSpecRegex {
    /// `RegularExpressionFromFileSpec(fixed, wildcard, filename)`.
    pub fn new(fixed: &str, wildcard: &str, filename: &str) -> FileSpecRegex {
        let mut toks = Vec::new();
        // `AppendRegularExpressionFromFixedDirectory`. A UNC prefix is a
        // Windows-only reading.
        let fixed = utf16(fixed);
        let mut i = last_index_of_directory_sequence(&fixed, 0);
        while i < fixed.len() {
            push_char(&mut toks, fixed[i]);
            i = last_index_of_directory_sequence(&fixed, i + 1);
        }
        // `AppendRegularExpressionFromWildcardDirectory`.
        let wild = utf16(wildcard);
        let star = u16::from(b'*');
        if wild.len() > 2 && wild[0] == star && wild[1] == star {
            toks.push(RegexTok::LeftDirs);
        }
        let mut i = last_index_of_directory_or_recursive_sequence(&wild, 0);
        while i < wild.len() {
            let is_recursive_operator =
                i + 2 < wild.len() && wild[i + 1] == star && wild[i + 2] == star;
            if is_recursive_operator {
                toks.push(RegexTok::MiddleDirs);
            } else {
                push_char(&mut toks, wild[i]);
            }
            i = last_index_of_directory_or_recursive_sequence(&wild, i + 1);
        }
        // `AppendRegularExpressionFromFilename`.
        let name = utf16(filename);
        let dot = u16::from(b'.');
        let has_trailing_dot = name.last() == Some(&dot);
        let part_length = if has_trailing_dot {
            name.len() - 1
        } else {
            name.len()
        };
        let mut i = 0;
        while i < part_length {
            let ch = name[i];
            if has_trailing_dot && ch == star {
                toks.push(RegexTok::AnythingButDot);
            } else if has_trailing_dot && ch == u16::from(b'?') {
                toks.extend([RegexTok::NotDot, RegexTok::SingleCharacter]);
            } else {
                push_char(&mut toks, ch);
            }
            if !has_trailing_dot
                && i + 2 < part_length
                && ch == star
                && name[i + 1] == dot
                && name[i + 2] == star
            {
                i += 2;
            }
            i += 1;
        }
        FileSpecRegex { toks }
    }

    /// `Regex.IsMatch` of this expression, compiled with
    /// `RegexOptions.IgnoreCase` under `culture`, against `input`.
    pub fn is_match(&self, input: &str, culture: Culture) -> bool {
        let input = utf16(input);
        let mut memo = vec![None; (self.toks.len() + 1) * (input.len() + 1)];
        self.match_at(&input, 0, 0, culture, &mut memo)
    }

    fn match_at(
        &self,
        input: &[u16],
        tok: usize,
        pos: usize,
        culture: Culture,
        memo: &mut [Option<bool>],
    ) -> bool {
        let slot = tok * (input.len() + 1) + pos;
        if let Some(answer) = memo[slot] {
            return answer;
        }
        let line_feed = u16::from(b'\n');
        let answer = match self.toks.get(tok) {
            // `$` matches at the end, or before a final line feed.
            None => pos == input.len() || (pos + 1 == input.len() && input[pos] == line_feed),
            Some(&t) => {
                let next = |memo: &mut [Option<bool>], p: usize| {
                    self.match_at(input, tok + 1, p, culture, memo)
                };
                match t {
                    RegexTok::Unit(u) => {
                        pos < input.len()
                            && culture.regex_key(input[pos]) == culture.regex_key(u)
                            && next(memo, pos + 1)
                    }
                    RegexTok::SingleCharacter => {
                        pos < input.len() && input[pos] != line_feed && next(memo, pos + 1)
                    }
                    RegexTok::NotDot => {
                        pos < input.len() && input[pos] != u16::from(b'.') && next(memo, pos + 1)
                    }
                    RegexTok::AnyNonSeparator => {
                        let run = input[pos..]
                            .iter()
                            .take_while(|&&u| !is_any_slash(u))
                            .count();
                        (pos..=pos + run).any(|p| next(memo, p))
                    }
                    RegexTok::AnythingButDot => {
                        let run = input[pos..]
                            .iter()
                            .take_while(|&&u| u != u16::from(b'.'))
                            .count();
                        (pos..=pos + run).any(|p| next(memo, p))
                    }
                    RegexTok::DirSeparator => {
                        let run = input[pos..]
                            .iter()
                            .take_while(|&&u| is_any_slash(u))
                            .count();
                        (pos + 1..=pos + run).any(|p| next(memo, p))
                    }
                    RegexTok::LeftDirs => {
                        // `.*` then a separator, or nothing.
                        let run = input[pos..].iter().take_while(|&&u| u != line_feed).count();
                        next(memo, pos)
                            || (pos..pos + run)
                                .filter(|&k| is_any_slash(input[k]))
                                .any(|k| next(memo, k + 1))
                    }
                    RegexTok::MiddleDirs => {
                        // A separator, or a separator, `.*` and a separator.
                        pos < input.len() && is_any_slash(input[pos]) && {
                            let run = input[pos + 1..]
                                .iter()
                                .take_while(|&&u| u != line_feed)
                                .count();
                            next(memo, pos + 1)
                                || (pos + 1..pos + 1 + run)
                                    .filter(|&k| is_any_slash(input[k]))
                                    .any(|k| next(memo, k + 1))
                        }
                    }
                }
            }
        };
        memo[slot] = Some(answer);
        answer
    }
}

/// `FileMatcher.AppendRegularExpressionFromChar`. An escaped special
/// character is its literal unit.
fn push_char(toks: &mut Vec<RegexTok>, ch: u16) {
    toks.push(if ch == u16::from(b'*') {
        RegexTok::AnyNonSeparator
    } else if ch == u16::from(b'?') {
        RegexTok::SingleCharacter
    } else if is_any_slash(ch) {
        RegexTok::DirSeparator
    } else {
        RegexTok::Unit(ch)
    });
}

/// What `GetFileSearchData` knows of a file spec, before the one question it
/// asks the file system: whether the spec's fixed directory exists. A spec
/// that enumerates a drive from its root never reaches it in an evaluation
/// (`EngineFileUtilities.GetFileList` stops first:
/// `glob::is_drive_enumerating_filespec`).
#[derive(Debug, Clone)]
pub struct FileSpec {
    /// The fixed directory as the spec spells it (`oldFixedDirectoryPart`).
    fixed: String,
    /// The fixed directory rooted at the project directory.
    rooted_fixed: String,
    wildcard: String,
    filename: String,
    strip_project_directory: bool,
}

impl FileSpec {
    /// `GetFileSpecInfo` of a decoded spec, rooted at `project_dir` as
    /// `GetFileSearchData` roots it, or `None` where the spec is illegal
    /// (`SearchAction.ReturnFileSpec`: MSBuild keeps an illegal include as a
    /// literal, and compares an illegal exclude by spelling).
    pub fn parse(project_dir: &str, spec: &str) -> Option<FileSpec> {
        if !is_legal_filespec(spec) {
            return None;
        }
        let (fixed, wildcard, filename) = split_filespec(spec);
        let rooted_fixed = path_combine(project_dir, fixed);
        let strip_project_directory = !eq_ordinal_ignore_case(&rooted_fixed, fixed);
        Some(FileSpec {
            fixed: fixed.to_string(),
            rooted_fixed,
            wildcard,
            filename,
            strip_project_directory,
        })
    }

    /// The directory whose existence `GetFileSearchData` asks
    /// (`Directory.Exists`, which resolves `.` and `..` lexically:
    /// [`full_path`]).
    pub fn probe(&self) -> &str {
        &self.rooted_fixed
    }

    /// `GetFileSearchData`, given whether [`Self::probe`] exists: the walk to
    /// run, or `None` where the fixed directory does not exist
    /// (`SearchAction.ReturnEmptyList`).
    pub fn search(&self, fixed_exists: bool) -> Option<Search> {
        if !self.rooted_fixed.is_empty() && !fixed_exists {
            return None;
        }
        let wildcard = trim_trailing_slashes(&self.wildcard);
        let b = wildcard.as_bytes();
        let n = b.len();
        let is_slash = |c: u8| c == b'/' || c == b'\\';
        let directory_pattern = (n > 6
            && b.starts_with(b"**")
            && is_slash(b[2])
            && is_slash(b[n - 3])
            && b.ends_with(b"**")
            && !b[3..n - 3].iter().copied().any(is_slash))
        .then(|| wildcard[3..n - 3].to_string());
        let match_with_regex = !self.wildcard.is_empty()
            && directory_pattern.is_none()
            && !is_recursive_directory_match(&self.wildcard);
        let data = SearchData {
            filespec: (!match_with_regex).then(|| self.filename.clone()),
            directory_pattern,
            regex: match_with_regex
                .then(|| FileSpecRegex::new(&self.fixed, &self.wildcard, &self.filename)),
            needs_recursion: !self.wildcard.is_empty(),
        };
        Some(Search {
            data,
            base_directory: normalize(&self.rooted_fixed),
            remaining_wildcard_directory: normalize(&self.wildcard),
            strip_project_directory: self.strip_project_directory,
        })
    }
}

/// `FileMatcher.FilesSearchData`.
#[derive(Debug, Clone)]
struct SearchData {
    /// The file-name pattern, unless the regular expression matches files.
    filespec: Option<String>,
    /// The `{name}` of a `**/{name}/**` wildcard directory part.
    directory_pattern: Option<String>,
    regex: Option<FileSpecRegex>,
    needs_recursion: bool,
}

/// A walk `GetFileSearchData` set up.
#[derive(Debug, Clone)]
pub struct Search {
    data: SearchData,
    base_directory: String,
    remaining_wildcard_directory: String,
    strip_project_directory: bool,
}

impl Search {
    /// The directory the walk starts in, as the walk spells it.
    pub fn base_directory(&self) -> &str {
        &self.base_directory
    }

    /// How many levels below its base directory the walk can list: the
    /// segments of its wildcard directory part, then the files. `None` when a
    /// `**` makes it unbounded.
    pub fn depth(&self) -> Option<usize> {
        let remaining = &self.remaining_wildcard_directory;
        if remaining.is_empty() {
            return Some(1);
        }
        let segs: Vec<&str> = remaining.split(['/', '\\']).collect();
        (!segs.contains(&"**")).then_some(segs.len() + 1)
    }

    fn initial_state(&self) -> RecursionState<'_> {
        RecursionState {
            base_directory: self.base_directory.clone(),
            remaining_wildcard_directory: self.remaining_wildcard_directory.clone(),
            is_inside_matching_directory: false,
            data: &self.data,
        }
    }
}

/// `FileMatcher.RecursionState`.
#[derive(Debug, Clone)]
struct RecursionState<'a> {
    base_directory: String,
    remaining_wildcard_directory: String,
    is_inside_matching_directory: bool,
    data: &'a SearchData,
}

impl RecursionState<'_> {
    fn is_looking_for_matching_directory(&self) -> bool {
        self.data.directory_pattern.is_some() && !self.is_inside_matching_directory
    }
}

/// `FileMatcher.RecursiveStepResult`.
#[derive(Debug, Clone, Default)]
struct RecursiveStepResult {
    remaining_wildcard_directory: String,
    consider_files: bool,
    needs_to_process_each_file: bool,
    directory_pattern: Option<String>,
    needs_directory_recursion: bool,
}

/// `FileMatcher.GetFilesRecursiveStep`.
fn get_files_recursive_step(state: &RecursionState<'_>) -> RecursiveStepResult {
    let mut ret = RecursiveStepResult::default();
    let remaining = &state.remaining_wildcard_directory;
    let consider_files = if state.data.directory_pattern.is_some() {
        state.is_inside_matching_directory
    } else {
        remaining.is_empty() || remaining.starts_with("**")
    };
    ret.consider_files = consider_files;
    if consider_files {
        ret.needs_to_process_each_file = state.data.filespec.is_none();
    }
    if state.data.needs_recursion && !remaining.is_empty() {
        let mut remaining = remaining.clone();
        let mut pattern = None;
        if !is_recursive_directory_match(&remaining) {
            let next_slash = remaining.find(['/', '\\']);
            let piece = next_slash.map_or(remaining.as_str(), |i| &remaining[..i]);
            if piece == "**" {
                remaining = "**".to_string();
            } else {
                pattern = Some(piece.to_string());
                remaining = next_slash.map_or(String::new(), |i| remaining[i + 1..].to_string());
            }
        }
        ret.needs_directory_recursion = true;
        ret.remaining_wildcard_directory = remaining;
        ret.directory_pattern = pattern;
    }
    ret
}

/// `FileMatcher.MatchFileRecursionStep`.
fn match_file_recursion_step(state: &RecursionState<'_>, file: &str, culture: Culture) -> bool {
    match (&state.data.filespec, &state.data.regex) {
        (Some(filespec), _) if is_all_files_wildcard(filespec) => true,
        (Some(filespec), _) => is_file_name_match(file, filespec),
        (None, Some(regex)) => regex.is_match(file, culture),
        (None, None) => unreachable!("a search has a file spec or a regular expression"),
    }
}

/// `FileMatcher.DirectoryEndsWithPattern`.
fn directory_ends_with_pattern(directory: &str, pattern: &str) -> bool {
    match directory.rfind(['/', '\\']) {
        Some(i) => is_match(&directory[i + 1..], pattern),
        None => false,
    }
}

/// `FileMatcher.IsSubdirectoryOf`, comparing `OrdinalIgnoreCase`.
fn is_subdirectory_of(possible_child: &str, possible_parent: &str) -> bool {
    if possible_parent.is_empty() {
        return true;
    }
    let (child, parent) = (utf16(possible_child), utf16(possible_parent));
    if !starts_with_ordinal_ignore_case(&child, &parent) {
        return false;
    }
    is_any_slash(parent[parent.len() - 1])
        || child.get(parent.len()).copied().is_some_and(is_any_slash)
}

/// `FileMatcher.RemoveProjectDirectory` of one path.
fn remove_project_directory(path: String, project_dir: &str) -> String {
    if !path.starts_with(project_dir) || project_dir.is_empty() {
        return path;
    }
    if project_dir.ends_with(['/', '\\']) {
        return path[project_dir.len()..].to_string();
    }
    match path.as_bytes().get(project_dir.len()) {
        Some(b'/' | b'\\') => path[project_dir.len() + 1..].to_string(),
        _ => path,
    }
}

/// The part of the file system a walk reads: one directory's listing, as the
/// evaluation's file system lists it (symbolic links classified by what they
/// point to), and its subdirectories' in turn.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Listing {
    /// The names of the files in the directory.
    pub files: Vec<String>,
    /// The subdirectories by name, each with its listing, or `None` where it
    /// was not read (below the depth a walk can reach).
    pub dirs: Vec<(String, Option<Listing>)>,
    /// The symbolic link to a directory this directory was found through:
    /// itself, or the outermost directory above it within the walk that is
    /// one.
    pub link: Option<String>,
}

/// A file the walk lists: its path as MSBuild spells it (relative to the
/// project directory where the spec is), and the link it was found through.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Found {
    pub path: String,
    pub link: Option<String>,
}

/// The walk needed a listing the [`Listing`] did not read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unlisted {
    pub dir: String,
}

/// `FileMatcher.GetFilesImplementation` for a spec whose search runs: the
/// files `include` lists below `root` (the listing of its base directory) and
/// no exclude takes, in no particular order, under `culture`. `excludes` are
/// the exclude specs' searches that run; `project_dir` is the project
/// directory as the evaluation spells it.
pub fn get_files(
    project_dir: &str,
    include: &Search,
    excludes: &[Search],
    root: &Listing,
    culture: Culture,
) -> Result<Vec<Found>, Unlisted> {
    let state = include.initial_state();
    let mut searches_to_exclude: Vec<RecursionState<'_>> = Vec::new();
    let mut in_subdirs: Vec<(Vec<u16>, RecursionState<'_>)> = Vec::new();
    for exclude in excludes {
        let mut exclude_state = exclude.initial_state();
        let exclude_base = exclude_state.base_directory.clone();
        let include_base = &state.base_directory;
        if !eq_ordinal_ignore_case(&exclude_base, include_base) {
            let (exclude_len, include_len) =
                (utf16(&exclude_base).len(), utf16(include_base).len());
            if exclude_len == include_len {
                continue;
            } else if exclude_len > include_len {
                if !is_subdirectory_of(&exclude_base, include_base) {
                    continue;
                }
                in_subdirs.push((ordinal_ignore_case_key(&exclude_base), exclude_state));
            } else {
                if !is_subdirectory_of(include_base, &exclude_base) {
                    continue;
                }
                if exclude_state.remaining_wildcard_directory.is_empty() {
                    continue;
                } else if is_recursive_directory_match(&exclude_state.remaining_wildcard_directory)
                {
                    exclude_state.base_directory = include_base.clone();
                } else {
                    exclude_state.base_directory = include_base.clone();
                    exclude_state.remaining_wildcard_directory = "**/".to_string();
                }
                searches_to_exclude.push(exclude_state);
            }
        } else {
            // Drop an exclude whose file name cannot end as the include's does.
            let include_filespec = utf16(state.data.filespec.as_deref().unwrap_or(""));
            let exclude_filespec = utf16(exclude_state.data.filespec.as_deref().unwrap_or(""));
            let literal_tail = |s: &[u16]| {
                s.len()
                    - s.iter()
                        .rposition(|&u| u == u16::from(b'*') || u == u16::from(b'?'))
                        .map_or(0, |i| i + 1)
            };
            let compare_length =
                literal_tail(&include_filespec).min(literal_tail(&exclude_filespec));
            let tail = |s: &[u16]| s[s.len() - compare_length..].to_vec();
            if starts_with_ordinal_ignore_case(&tail(&include_filespec), &tail(&exclude_filespec)) {
                searches_to_exclude.push(exclude_state);
            }
        }
    }
    let mut walk = Walk {
        project_dir,
        strip_project_directory: include.strip_project_directory,
        in_subdirs: &in_subdirs,
        culture,
        out: Vec::new(),
    };
    walk.get_files_recursive(state, Some(root), searches_to_exclude)?;
    Ok(walk.out)
}

/// `GetFilesRecursive`'s fixed inputs and its output.
struct Walk<'a, 'b> {
    project_dir: &'a str,
    strip_project_directory: bool,
    /// `searchesToExcludeInSubdirs`, keyed as its `OrdinalIgnoreCase`
    /// dictionary files them.
    in_subdirs: &'a [(Vec<u16>, RecursionState<'b>)],
    culture: Culture,
    out: Vec<Found>,
}

impl<'b> Walk<'_, 'b> {
    /// `FileMatcher.GetFilesRecursive`, at the directory `listing` lists.
    fn get_files_recursive(
        &mut self,
        state: RecursionState<'b>,
        listing: Option<&Listing>,
        searches_to_exclude: Vec<RecursionState<'b>>,
    ) -> Result<(), Unlisted> {
        let culture = self.culture;
        let mut exclude_next_steps = Vec::with_capacity(searches_to_exclude.len());
        for exclude in &searches_to_exclude {
            exclude_next_steps.push(get_files_recursive_step(exclude));
            // The exclude takes every file this search would list here.
            if !exclude.is_looking_for_matching_directory()
                && let Some(exclude_filespec) = &exclude.data.filespec
                && exclude.remaining_wildcard_directory == state.remaining_wildcard_directory
                && (is_all_files_wildcard(exclude_filespec)
                    || Some(exclude_filespec) == state.data.filespec.as_ref())
            {
                return Ok(());
            }
        }
        let next_step = get_files_recursive_step(&state);
        let unlisted = || Unlisted {
            dir: state.base_directory.clone(),
        };
        if next_step.consider_files {
            let listing = listing.ok_or_else(unlisted)?;
            // `GetFilesForStep`, through the evaluation context's cache: the
            // listing is filtered by the file spec unless it takes every file.
            for name in &listing.files {
                let full = path_join(&state.base_directory, name);
                if let Some(filespec) = &state.data.filespec
                    && !is_all_files_wildcard(filespec)
                    && !is_file_name_match(&full, filespec)
                {
                    continue;
                }
                let file = if self.strip_project_directory {
                    remove_project_directory(full, self.project_dir)
                } else {
                    full
                };
                if next_step.needs_to_process_each_file
                    && !match_file_recursion_step(&state, &file, culture)
                {
                    continue;
                }
                let excluded =
                    searches_to_exclude
                        .iter()
                        .zip(&exclude_next_steps)
                        .any(|(exclude, step)| {
                            step.consider_files
                                && match_file_recursion_step(exclude, &file, culture)
                        });
                if !excluded {
                    self.out.push(Found {
                        path: file,
                        link: listing.link.clone(),
                    });
                }
            }
        }
        if !next_step.needs_directory_recursion {
            return Ok(());
        }
        let listing = listing.ok_or_else(unlisted)?;
        for (name, child) in &listing.dirs {
            let subdir = path_join(&state.base_directory, name);
            if let Some(pattern) = &next_step.directory_pattern
                && !is_all_files_wildcard(pattern)
                && !is_file_name_match(&subdir, pattern)
            {
                continue;
            }
            let mut new_state = state.clone();
            new_state.base_directory = subdir.clone();
            new_state.remaining_wildcard_directory = next_step.remaining_wildcard_directory.clone();
            if new_state.is_looking_for_matching_directory()
                && directory_ends_with_pattern(
                    &subdir,
                    state.data.directory_pattern.as_deref().unwrap_or_default(),
                )
            {
                new_state.is_inside_matching_directory = true;
            }
            let mut new_searches_to_exclude = Vec::new();
            for (exclude, step) in searches_to_exclude.iter().zip(&exclude_next_steps) {
                if step.needs_directory_recursion
                    && step
                        .directory_pattern
                        .as_deref()
                        .is_none_or(|pattern| is_file_name_match(&subdir, pattern))
                {
                    let mut this_exclude_step = exclude.clone();
                    this_exclude_step.base_directory = subdir.clone();
                    this_exclude_step.remaining_wildcard_directory =
                        step.remaining_wildcard_directory.clone();
                    if this_exclude_step.is_looking_for_matching_directory()
                        && directory_ends_with_pattern(
                            &subdir,
                            this_exclude_step
                                .data
                                .directory_pattern
                                .as_deref()
                                .unwrap_or_default(),
                        )
                    {
                        this_exclude_step.is_inside_matching_directory = true;
                    }
                    new_searches_to_exclude.push(this_exclude_step);
                }
            }
            let key = ordinal_ignore_case_key(&subdir);
            new_searches_to_exclude.extend(
                self.in_subdirs
                    .iter()
                    .filter(|(base, _)| *base == key)
                    .map(|(_, exclude)| exclude.clone()),
            );
            self.get_files_recursive(new_state, child.as_ref(), new_searches_to_exclude)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
