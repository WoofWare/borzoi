//! MSBuild's unix-only path fixup, `MaybeAdjustFilePath`.
//!
//! Stage P0 of `docs/msbuild-unix-path-fixup-plan.md`. On a non-Windows host
//! MSBuild passes every expanded value through `FileUtilities.MaybeAdjustFilePath`
//! (`FileUtilities.cs:608`): a backslash-bearing value is rewritten `\`→`/` (and
//! its slash runs collapsed) **iff** the rewritten first segment exists as a
//! directory relative to the MSBuild process's working directory — a
//! cwd-dependent decision we cannot make.
//!
//! The response (later stages) is to *bracket the two worlds*: the value MSBuild
//! commits is one of exactly two — the raw text, or the rewrite — so a consumer
//! that agrees under both can commit, and one that disagrees declines. This
//! module is the eligibility half: [`worlds`] says whether the fixup can fire
//! and, if so, what the rewrite is.
//!
//! Everything here is a faithful port of the source, unit-pinned and (in
//! `tests/path_fixup_diff.rs`) differentially bracketed against `dotnet msbuild`
//! run from two directories.

/// The **rewrite** the fixup would apply if it fires, or `None` when the fixup
/// cannot fire at all (so the value is unambiguous — MSBuild returns it raw).
///
/// `Some(rewrite)` means the value MSBuild commits is one of `{value, rewrite}`,
/// decided by a filesystem probe against the process cwd. `None` means MSBuild
/// commits `value` regardless.
///
/// Ported from `MaybeAdjustFilePath`: the fixup is skipped for an empty value,
/// a `$(`/`@(` reference, a `\\` network prefix, or a value with no backslash
/// (its `ConvertToUnixSlashes` is then the identity, so both worlds coincide).
/// Otherwise the rewrite is `convert_to_unix_slashes`. We do **not** here
/// evaluate `LooksLikeUnixFilePath`'s probe — that is the cwd-dependent part we
/// cannot decide, and bracketing `{value, rewrite}` is conservative whether the
/// probe would hit or miss.
pub fn worlds(value: &str) -> Option<String> {
    // `MaybeAdjustFilePath` returns early on Windows (`IsWindows`), where MSBuild
    // uses `\` separators and does not touch them — so on a Windows host every
    // value is committed verbatim, unambiguously.
    if cfg!(windows)
        || value.is_empty()
        || value.starts_with("$(")
        || value.starts_with("@(")
        || value.starts_with("\\\\")
        || !value.contains('\\')
    {
        return None;
    }
    let rewrite = convert_to_unix_slashes(value);
    // `MaybeAdjustFilePath` also gates on the rewrite containing a `/`; a value
    // with a backslash always yields one, so this holds whenever we reach here.
    debug_assert!(rewrite.contains('/'));
    Some(rewrite)
}

/// What `LooksLikeUnixFilePath` (`FileUtilities.cs`) asks of the file system
/// to decide whether the fixup keeps `rewrite`, a [`worlds`] rewrite.
///
/// It drops one pair of enclosing quotes, then takes the first segment: up to
/// the first `/` after the first character. That segment is probed with
/// `Directory.Exists(Path.Combine(baseDirectory, segment))`, where
/// `baseDirectory` is the process's working directory for every expansion an
/// evaluation makes (`CurrentThreadWorkingDirectory` is set only in
/// multithreaded builds, and then to a directory too). With no `/` after the
/// first character, a value that starts with `/` is probed with
/// `FileOrDirectoryExists`, and any other is no path.
///
/// The probe is text: an escaped `%2e` is the three characters, as MSBuild
/// sees it, upstream of unescaping.
#[derive(Debug, PartialEq, Eq)]
pub enum UnixPathProbe<'a> {
    /// The first segment is `.` or `..`, a directory under any working
    /// directory: the fixup keeps the rewrite.
    Exists,
    /// No `/` at all, so nothing to probe: the fixup returns the value as it
    /// was. A rewrite always holds a `/`, so this answers only other text.
    Absent,
    /// `Directory.Exists` of this absolute path.
    Directory(&'a str),
    /// `File.Exists || Directory.Exists` of this absolute path.
    FileOrDirectory(&'a str),
    /// A directory named relative to the MSBuild process's working directory,
    /// which nothing in the evaluation's inputs determines: `dotnet build` run
    /// from two directories evaluates the same project two ways.
    WorkingDirectory,
}

/// The probe that decides whether the fixup keeps `rewrite`.
pub fn unix_path_probe(rewrite: &str) -> UnixPathProbe<'_> {
    // `RemoveQuotes`: a matching pair around at least one character. The
    // quotes are ASCII, so counting bytes counts what UTF-16 counts here.
    let bytes = rewrite.as_bytes();
    let quoted =
        bytes.len() > 2 && matches!(bytes[0], b'\'' | b'"') && bytes[bytes.len() - 1] == bytes[0];
    let value = if quoted {
        &rewrite[1..rewrite.len() - 1]
    } else {
        rewrite
    };
    // `value.Slice(1).IndexOf('/') + 1`: a `/` is never part of a multi-unit
    // character, so searching the bytes after the first finds the same one.
    let Some(at) = value
        .as_bytes()
        .iter()
        .skip(1)
        .position(|&b| b == b'/')
        .map(|at| at + 1)
    else {
        return if value.starts_with('/') {
            UnixPathProbe::FileOrDirectory(value)
        } else {
            UnixPathProbe::Absent
        };
    };
    match &value[..at] {
        "." | ".." => UnixPathProbe::Exists,
        // `Path.Combine` returns a rooted second argument whole.
        segment if segment.starts_with('/') => UnixPathProbe::Directory(segment),
        _ => UnixPathProbe::WorkingDirectory,
    }
}

/// `\`→`/`, then collapse every run of slashes to one — a faithful port of
/// `ConvertToUnixSlashes`/`CollapseSlashes` (`Regex.Replace(s, "[\\/]+", "/")`).
/// MSBuild only reaches this when the value contains a backslash, so the
/// collapse (which the identity path skips) is always in effect here.
pub fn convert_to_unix_slashes(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut prev_slash = false;
    for ch in value.chars() {
        let is_slash = ch == '\\' || ch == '/';
        if !(is_slash && prev_slash) {
            out.push(if ch == '\\' { '/' } else { ch });
        }
        prev_slash = is_slash;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_backslash_is_unambiguous() {
        // The fixup's `ConvertToUnixSlashes` is the identity without a backslash,
        // so both worlds coincide — even a forward-slash path, and even a `//`
        // run (which is *not* collapsed absent a backslash).
        assert_eq!(worlds(""), None);
        assert_eq!(worlds("obj/Debug/"), None);
        assert_eq!(worlds("a//b"), None);
        assert_eq!(worlds("plain"), None);
    }

    #[test]
    fn references_and_network_prefixes_are_skipped() {
        // `$(`/`@(` references and a `\\` network prefix are excluded verbatim,
        // even though they contain a backslash.
        assert_eq!(worlds("$(Foo)\\bar"), None);
        assert_eq!(worlds("@(Item)\\bar"), None);
        assert_eq!(worlds("\\\\server\\share"), None);
    }

    #[test]
    #[cfg(windows)]
    fn the_fixup_is_inert_on_windows() {
        // MSBuild does not adjust separators on Windows, so every value is
        // unambiguous there.
        assert_eq!(worlds("obj\\Debug\\"), None);
        assert_eq!(worlds("\\x"), None);
    }

    #[test]
    #[cfg(not(windows))]
    fn a_backslash_value_brackets_the_rewrite() {
        // The canonical case: `obj\Debug\` could stay raw or become `obj/Debug/`
        // (cwd-dependent), so the two worlds are exactly those.
        assert_eq!(worlds("obj\\Debug\\").as_deref(), Some("obj/Debug/"));
        // A single leading backslash becomes an absolute `/…` (whose probe is
        // cwd-*independent*, but bracketing is still correct).
        assert_eq!(worlds("\\x").as_deref(), Some("/x"));
        // Slash runs collapse only once a backslash is present.
        assert_eq!(worlds("a\\\\b").as_deref(), Some("a/b"));
        assert_eq!(worlds("a\\/b").as_deref(), Some("a/b"));
        assert_eq!(worlds("a//\\b").as_deref(), Some("a/b"));
    }

    /// `LooksLikeUnixFilePath` as `FileUtilities.cs` writes it, over UTF-16-like
    /// `char`s, with the file system's two questions answered by the caller.
    fn looks_like_unix_file_path(
        value: &str,
        directory_exists: &mut dyn FnMut(&str) -> bool,
        file_or_directory_exists: &mut dyn FnMut(&str) -> bool,
    ) -> bool {
        let chars: Vec<char> = value.chars().collect();
        let end = chars.len().wrapping_sub(1);
        let unquoted: &[char] = if chars.len() > 2
            && ((chars[0] == '\'' && chars[end] == '\'') || (chars[0] == '"' && chars[end] == '"'))
        {
            &chars[1..end]
        } else {
            &chars
        };
        let directory_length = unquoted
            .iter()
            .skip(1)
            .position(|&c| c == '/')
            .map_or(0, |at| at + 1);
        let should_check_directory = directory_length != 0;
        let should_check_file_or_directory =
            !should_check_directory && unquoted.first() == Some(&'/');
        let directory: String = unquoted[..directory_length].iter().collect();
        (should_check_directory && directory_exists(&directory))
            || (should_check_file_or_directory
                && file_or_directory_exists(&unquoted.iter().collect::<String>()))
    }

    /// Every string up to `len` characters over `alphabet`.
    fn all_strings(alphabet: &[char], len: usize) -> Vec<String> {
        let mut all = vec![String::new()];
        let mut layer = vec![String::new()];
        for _ in 0..len {
            layer = layer
                .iter()
                .flat_map(|prefix| {
                    alphabet.iter().map(move |c| {
                        let mut s = prefix.clone();
                        s.push(*c);
                        s
                    })
                })
                .collect();
            all.extend(layer.iter().cloned());
        }
        all
    }

    /// `unix_path_probe` names the question `LooksLikeUnixFilePath` asks of
    /// every rewrite, and the answer it settles to: under every file system
    /// (the working directory holding any relative segment or not, the root
    /// holding any absolute path or not), the reference's answer is the one
    /// the probe's question gets, and an absolute question is the very path
    /// the reference asks about.
    #[test]
    fn the_probe_is_looks_like_unix_file_path() {
        let alphabet = ['.', '\\', '/', 'a', '\'', '"', 'é'];
        let mut kinds = [0usize; 5];
        for value in all_strings(&alphabet, 6) {
            if !value.contains('\\') || value.starts_with(r"\\") {
                continue;
            }
            let rewrite = convert_to_unix_slashes(&value);
            let probe = unix_path_probe(&rewrite);
            kinds[match probe {
                UnixPathProbe::Exists => 0,
                UnixPathProbe::Absent => 1,
                UnixPathProbe::Directory(_) => 2,
                UnixPathProbe::FileOrDirectory(_) => 3,
                UnixPathProbe::WorkingDirectory => 4,
            }] += 1;
            for (cwd_holds, root_holds) in
                [(false, false), (false, true), (true, false), (true, true)]
            {
                let mut asked = Vec::new();
                let mut asked_any = Vec::new();
                let reference = looks_like_unix_file_path(
                    &rewrite,
                    &mut |segment| {
                        asked.push(segment.to_string());
                        if segment.starts_with('/') {
                            root_holds
                        } else {
                            matches!(segment, "." | "..") || cwd_holds
                        }
                    },
                    &mut |path| {
                        asked_any.push(path.to_string());
                        assert!(path.starts_with('/'), "{value:?}: relative {path:?}");
                        root_holds
                    },
                );
                let ours = match probe {
                    UnixPathProbe::Exists => true,
                    UnixPathProbe::Absent => false,
                    UnixPathProbe::Directory(dir) => {
                        assert_eq!(asked, [dir], "{value:?}");
                        root_holds
                    }
                    UnixPathProbe::FileOrDirectory(path) => {
                        assert_eq!(asked_any, [path], "{value:?}");
                        root_holds
                    }
                    UnixPathProbe::WorkingDirectory => cwd_holds,
                };
                assert_eq!(
                    ours, reference,
                    "{value:?} ({cwd_holds}, {root_holds}): {probe:?}"
                );
            }
        }
        // A rewrite holds a `/`, so it always has a question to ask.
        assert_eq!(kinds[1], 0, "{kinds:?}");
        assert!(
            [0, 2, 3, 4].iter().all(|&k| kinds[k] > 100),
            "every probe is reached: {kinds:?}"
        );
    }

    #[test]
    fn convert_matches_the_collapse_rule() {
        assert_eq!(convert_to_unix_slashes("a\\b\\c"), "a/b/c");
        assert_eq!(convert_to_unix_slashes("a\\\\\\b"), "a/b");
        assert_eq!(convert_to_unix_slashes("\\a"), "/a");
        assert_eq!(convert_to_unix_slashes("a\\"), "a/");
    }
}
