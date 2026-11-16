use super::*;
use proptest::prelude::*;

// ----- `IsMatch` -----

/// Naive wildcard match over characters, ASCII case folded: `*` any run, `?`
/// any one character.
fn wildcard_naive(input: &[char], pattern: &[char]) -> bool {
    match pattern.split_first() {
        None => input.is_empty(),
        Some(('*', rest)) => (0..=input.len()).any(|i| wildcard_naive(&input[i..], rest)),
        Some(('?', rest)) => !input.is_empty() && wildcard_naive(&input[1..], rest),
        Some((c, rest)) => {
            input.first().is_some_and(|i| i.eq_ignore_ascii_case(c))
                && wildcard_naive(&input[1..], rest)
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// `IsMatch`'s shortcuts (the tail check, the skip to the next matching
    /// character) answer as a plain wildcard match does, case folded.
    #[test]
    fn is_match_is_a_case_folded_wildcard_match(
        input in "[abAB.]{1,7}",
        pattern in "[abAB.*?]{0,7}",
    ) {
        let i: Vec<char> = input.chars().collect();
        let p: Vec<char> = pattern.chars().collect();
        prop_assert_eq!(is_match(&input, &pattern), wildcard_naive(&i, &p));
    }
}

#[test]
fn is_match_folds_ascii_letters_only() {
    assert!(is_match("A.FS", "a.fs"));
    assert!(!is_match("a[b", "a{b"));
    assert!(!is_match("\u{212a}.fs", "k.fs"));
    assert!(is_match("abc", "*"));
    assert!(!is_match("abc", "*.*"));
    assert!(is_match("a.b", "*.*"));
}

// ----- `Normalize` and the path helpers -----

#[test]
fn normalize_collapses_slashes_and_trims_the_end() {
    assert_eq!(normalize("/p//q/"), "/p/q");
    assert_eq!(normalize("a/./b//"), "a/./b");
    assert_eq!(normalize("**/"), "**");
    assert_eq!(normalize("/"), "/");
    assert_eq!(normalize(""), "");
}

#[test]
fn path_helpers_follow_dotnet_on_unix() {
    assert_eq!(path_combine("/p", "sub/"), "/p/sub/");
    assert_eq!(path_combine("/p/", "sub/"), "/p/sub/");
    assert_eq!(path_combine("/p", ""), "/p");
    assert_eq!(path_combine("/p", "/abs/"), "/abs/");
    assert_eq!(path_join("/p", "a.fs"), "/p/a.fs");
    assert_eq!(path_join("/", "a.fs"), "/a.fs");
    assert_eq!(full_path("/p/sub/../x/./y/"), "/p/x/y/");
    assert_eq!(full_path("/../a"), "/a");
    assert_eq!(file_name("sub/a.fs"), "a.fs");
    assert_eq!(
        remove_project_directory("/p/sub/a.fs".into(), "/p"),
        "sub/a.fs"
    );
    assert_eq!(
        remove_project_directory("/px/a.fs".into(), "/p"),
        "/px/a.fs"
    );
    assert!(is_subdirectory_of("/P/Sub", "/p"));
    assert!(!is_subdirectory_of("/px", "/p"));
}

// ----- `RegularExpressionFromFileSpec` -----

fn regex(spec: &str) -> FileSpecRegex {
    let (fixed, wildcard, filename) = split_filespec(spec);
    FileSpecRegex::new(fixed, &wildcard, &filename)
}

fn regex_matches(spec: &str, path: &str) -> bool {
    regex(spec).is_match(path, Culture::Invariant)
}

/// The readings of `AppendRegularExpressionFromFilename` and
/// `AppendRegularExpressionFromChar` that a path pattern does not have
/// (oracle-pinned where noted in `glob_resolver`'s tests).
#[test]
fn the_regular_expression_reads_as_msbuild_builds_it() {
    // The `.*` of `*.*` is dropped, so `a*.*` takes a name with no dot.
    assert!(regex_matches("s*/a*.*", "sub/ab"));
    assert!(regex_matches("s*/*.*", "sub/noext"));
    assert!(!regex_matches("s*/*.*.*", "sub/noext"));
    // `?` is any character, a separator included.
    assert!(regex_matches("s*/a?b.fs", "sub/a/b.fs"));
    // `/./` and runs of separators collapse in the fixed directory.
    assert!(regex_matches("sub/./*/*", "sub/a/b.fs"));
    assert!(!regex_matches("sub/./*/*", "sub/./a/b.fs"));
    // `**` at the start is any leading directories; in the middle, a
    // separator or two around any run.
    assert!(regex_matches("**/x/*.fs", "x/a.fs"));
    assert!(regex_matches("**/x/*.fs", "q/r/x/a.fs"));
    assert!(regex_matches("s*/**/a.fs", "sub/a.fs"));
    assert!(regex_matches("s*/**/a.fs", "sub/p/q/a.fs"));
    assert!(!regex_matches("s*/**/a.fs", "sub"));
    // A `.` segment in the wildcard part is dropped (before a `**`, it is the
    // walk, looking for a directory named `.`, that finds nothing).
    assert!(regex_matches("**/./*.fs", "sub/a.fs"));
    assert!(regex_matches("*/./**/*.fs", "sub/a.fs"));
    // `$` matches before a final line feed.
    assert!(regex_matches("s*/a", "sub/a\n"));
}

#[test]
fn a_turkish_culture_keeps_i_apart_in_a_regular_expression() {
    let r = regex("s*/BI.fs");
    assert!(r.is_match("sub/bi.fs", Culture::Invariant));
    assert!(!r.is_match("sub/bi.fs", Culture::Turkish));
    assert!(r.is_match("sub/bI.fs", Culture::Turkish));
    assert!(
        r.is_match("SUB/BA.FS", Culture::Turkish) == r.is_match("SUB/BA.FS", Culture::Invariant)
    );
}

/// A backtracking reading of the expression, construct by construct, as a
/// reference for the automaton [`FileSpecRegex::is_match`] simulates.
fn regex_reference(toks: &[RegexTok], input: &[u16], culture: Culture) -> bool {
    let line_feed = u16::from(b'\n');
    let Some((&tok, rest)) = toks.split_first() else {
        return input.is_empty() || input == [line_feed];
    };
    let next = |at: usize| regex_reference(rest, &input[at..], culture);
    let run = |stop: &dyn Fn(u16) -> bool, from: usize| {
        input[from..].iter().take_while(|&&u| !stop(u)).count()
    };
    match tok {
        RegexTok::Unit(u) => {
            input
                .first()
                .is_some_and(|&c| culture.regex_key(c) == culture.regex_key(u))
                && next(1)
        }
        RegexTok::SingleCharacter => input.first().is_some_and(|&c| c != line_feed) && next(1),
        RegexTok::NotDot => input.first().is_some_and(|&c| c != u16::from(b'.')) && next(1),
        RegexTok::AnyNonSeparator => (0..=run(&|u| is_any_slash(u), 0)).any(next),
        RegexTok::AnythingButDot => (0..=run(&|u| u == u16::from(b'.'), 0)).any(next),
        RegexTok::DirSeparator => (1..=run(&|u| !is_any_slash(u), 0)).any(next),
        RegexTok::LeftDirs => {
            next(0)
                || (0..run(&|u| u == line_feed, 0))
                    .filter(|&k| is_any_slash(input[k]))
                    .any(|k| next(k + 1))
        }
        RegexTok::MiddleDirs => {
            input.first().copied().is_some_and(is_any_slash)
                && (next(1)
                    || (1..1 + run(&|u| u == line_feed, 1))
                        .filter(|&k| is_any_slash(input[k]))
                        .any(|k| next(k + 1)))
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// The automaton accepts exactly what the backtracking reading does, on
    /// specs over every construct and inputs over the units they treat apart.
    #[test]
    fn the_automaton_is_the_backtracking_reading(
        fixed in "(/|a|\\./|//)*",
        wildcard in "((\\*\\*|\\*|\\?|a|\\.)/){0,4}",
        filename in "[a.*?I]{0,5}",
        input in "[a/.\\\\iI\n]{0,9}",
    ) {
        let regex = FileSpecRegex::new(&fixed, &wildcard, &filename);
        let units = utf16(&input);
        for culture in Culture::ALL {
            prop_assert_eq!(
                regex.is_match(&input, culture),
                regex_reference(&regex.toks, &units, culture),
                "{:?} {:?} {:?} {:?}", fixed, wildcard, filename, input
            );
        }
    }
}

/// Long inputs neither recurse per unit nor allocate per pair of positions.
#[test]
fn the_regular_expression_matches_long_inputs_on_a_small_stack() {
    let spec = format!("{}*", "a".repeat(4000));
    let input = "a".repeat(4000);
    let answer = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            regex(&format!("s*/{spec}")).is_match(&format!("sub/{input}"), Culture::Invariant)
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(answer);
}

/// Naive whole-path glob over segments: `**` any run of segments, `*` any run
/// within one, case folded.
fn path_glob_naive(pattern: &[&str], path: &[&str]) -> bool {
    match pattern.split_first() {
        None => path.is_empty(),
        Some((&"**", rest)) => (0..=path.len()).any(|i| path_glob_naive(rest, &path[i..])),
        Some((p, rest)) => {
            !path.is_empty() && {
                let pc: Vec<char> = p.chars().collect();
                let sc: Vec<char> = path[0].chars().collect();
                wildcard_naive(&sc, &pc) && path_glob_naive(rest, &path[1..])
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// Without `?`, `*.*` or `.` segments, the regular expression is the
    /// plain path glob.
    #[test]
    fn the_regular_expression_is_a_path_glob_on_plain_specs(
        dirs in prop::collection::vec(prop::sample::select(vec!["a", "b*", "*", "**", "Ab"]), 1..4),
        name in prop::sample::select(vec!["a", "*", "*b", "a*"]),
        path in prop::collection::vec(prop::sample::select(vec!["a", "ab", "b", "AB", "x"]), 1..5),
    ) {
        let spec = format!("{}/{name}", dirs.join("/"));
        let path = path.join("/");
        let mut pattern: Vec<&str> = dirs.clone();
        pattern.push(name);
        let segs: Vec<&str> = path.split('/').collect();
        prop_assert_eq!(regex_matches(&spec, &path), path_glob_naive(&pattern, &segs), "{} {}", spec, path);
    }
}

// ----- The walk -----

/// A listing from `/`-separated file paths below the walk root, every
/// directory read.
fn listing(files: &[&str]) -> Listing {
    let mut root = Listing::default();
    for file in files {
        let segs: Vec<&str> = file.split('/').collect();
        let mut node = &mut root;
        for dir in &segs[..segs.len() - 1] {
            let i = match node.dirs.iter().position(|(n, _)| n == dir) {
                Some(i) => i,
                None => {
                    node.dirs.push((dir.to_string(), Some(Listing::default())));
                    node.dirs.len() - 1
                }
            };
            node = node.dirs[i].1.as_mut().unwrap();
        }
        node.files.push(segs[segs.len() - 1].to_string());
    }
    root
}

const PROJ: &str = "/p/proj";

/// The files `include` lists under `excludes` on a project directory holding
/// `files`, every fixed directory existing where `files` has it, sorted.
fn walk(files: &[&str], include: &str, excludes: &[&str]) -> Vec<String> {
    let exists = |dir: &str| {
        let dir = full_path(dir);
        let below = dir.trim_end_matches('/').strip_prefix(PROJ);
        match below {
            Some("") => true,
            Some(rel) => files
                .iter()
                .any(|f| f.starts_with(&format!("{}/", &rel[1..]))),
            None => dir == "/p/" || dir == "/" || dir == "/p",
        }
    };
    let search = |spec: &str| FileSpec::parse(PROJ, spec).and_then(|s| s.search(exists(s.probe())));
    let Some(include) = search(include) else {
        return Vec::new();
    };
    let excludes: Vec<Search> = excludes.iter().filter_map(|e| search(e)).collect();
    // The listing of the include's base directory.
    let base = include.base_directory().to_string();
    let rel = full_path(&format!("{base}/"))
        .trim_end_matches('/')
        .to_string();
    let rel = rel.strip_prefix(PROJ).unwrap_or("").trim_start_matches('/');
    let mut root = listing(files);
    for seg in rel.split('/').filter(|s| !s.is_empty()) {
        root = root
            .dirs
            .into_iter()
            .find(|(n, _)| n == seg)
            .and_then(|(_, l)| l)
            .unwrap_or_default();
    }
    let mut out: Vec<String> = get_files(PROJ, &include, &excludes, &root, Culture::Invariant)
        .expect("every directory is listed")
        .into_iter()
        .map(|f| f.path)
        .collect();
    out.sort();
    out
}

/// The walk's readings the full-path approximation got wrong, each pinned
/// against MSBuild (`fsproj_glob_case_generative_diff`'s corners).
#[test]
fn the_walk_reads_the_shapes_a_full_path_pattern_does_not() {
    // `**/**/**` is the directory-name shape with a name of `**`: one
    // directory, never none.
    assert_eq!(
        walk(&["sub/a.fs", "sub/x/b.fs"], "sub/**/**/**", &[]),
        ["sub/x/b.fs"]
    );
    // A `.` segment is a directory the walk looks for before a `**`, and is
    // dropped by the regular expression after one.
    assert_eq!(
        walk(&["sub/a.fs"], "*/./**/*.fs", &[]),
        Vec::<String>::new()
    );
    assert_eq!(walk(&["sub/a.fs"], "**/./*.fs", &[]), ["sub/a.fs"]);
    // A `.` segment in the fixed directory stays in what the walk lists, which
    // the regular expression, having collapsed it, then refuses.
    assert_eq!(
        walk(&["sub/a/b.fs"], "sub/./*/*", &[]),
        Vec::<String>::new()
    );
    assert_eq!(walk(&["sub/a/b.fs"], "sub/./a/*", &[]), ["sub/./a/b.fs"]);
    assert_eq!(walk(&["sub/a.fs"], "sub/./*.fs", &[]), ["sub/./a.fs"]);
    // A `**/{name}/**` exclude never matches the walk root's own ancestors.
    assert_eq!(
        walk(&["sub/deep/d.fs"], "sub/deep/*.fs", &["**/deep/**"]),
        ["sub/deep/d.fs"]
    );
    assert_eq!(
        walk(&["sub/deep/d.fs"], "sub/**/*.fs", &["**/deep/**"]),
        Vec::<String>::new()
    );
    // An exclude based above the walk root is matched by its regular
    // expression alone, whose `?` crosses a separator.
    assert_eq!(
        walk(&["sub/a/b.fs"], "sub/**/B.fs", &["s*/a?b.fs"]),
        Vec::<String>::new()
    );
    // An exclude spelt with `./` is based elsewhere, and takes nothing.
    assert_eq!(walk(&["a.fs"], "*.fs", &["./a.fs"]), ["a.fs"]);
    assert_eq!(walk(&["a.fs"], "./*.fs", &["a.fs"]), ["./a.fs"]);
    // An exclude anchored unlike the include is matched against what the
    // include's walk lists, which it never spells.
    assert_eq!(
        walk(&["sub/a.fs"], "s*/*.fs", &["/p/proj/s*/*.fs"]),
        ["sub/a.fs"]
    );
}

/// The walk asks for no listing below the depth its wildcard part reaches.
#[test]
fn the_walk_needs_no_listing_past_its_depth() {
    let mut root = listing(&["sub/a.fs"]);
    root.dirs[0]
        .1
        .as_mut()
        .unwrap()
        .dirs
        .push(("deeper".into(), None));
    let include = FileSpec::parse(PROJ, "*/*.fs")
        .unwrap()
        .search(true)
        .unwrap();
    assert_eq!(include.depth(), Some(2));
    assert_eq!(
        get_files(PROJ, &include, &[], &root, Culture::Invariant).map(|f| f.len()),
        Ok(1)
    );
    let recursive = FileSpec::parse(PROJ, "**/*.fs")
        .unwrap()
        .search(true)
        .unwrap();
    assert_eq!(recursive.depth(), None);
    assert!(get_files(PROJ, &recursive, &[], &root, Culture::Invariant).is_err());
}
