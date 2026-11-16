//! Differential test: the **walker's evaluated property table** vs the real
//! MSBuild evaluator, over whole `.fsproj` documents.
//!
//! The crate already diffs conditions (`condition_diff.rs`) and property-value
//! expansion (`property_expr_diff.rs`) against the oracle. Both take their
//! input *after* MSBuild's XML layer has run: the expansion harness hands
//! MSBuild a property **body**, anchored between non-whitespace sentinels
//! precisely so the XML layer is the identity. That makes both harnesses
//! structurally blind to everything the XML layer does — insignificant
//! whitespace, entity decoding, CDATA, comment-split text — which is exactly
//! where a run of hand-found wrong-commits lived (PR #890, review rounds 6-9:
//! a whitespace-only `<P> </P>` stored as `" "` where MSBuild has `""`, so
//! `'$(P)' == ''` committed the wrong branch).
//!
//! This harness closes that hole by handing **the document itself** to both
//! sides, byte for byte, and comparing the evaluated property table.
//!
//! The contract is the walker's, and it is the usual one:
//!
//! - We **committed** a property (it is in `ParsedProject::properties`) ⟹
//!   MSBuild must evaluate the same document to the byte-identical value.
//! - We **dropped** it (an unmodellable body, an unevaluable expansion) ⟹ no
//!   claim. Partiality is the fail-safe superset.
//! - MSBuild **rejects** the document ⟹ we must not have committed anything
//!   for it.
//!
//! Inputs are deterministic (a fixed-seed SplitMix64 over an adversarial body
//! alphabet, plus the hand corner list), so a failure reproduces exactly.

mod common;

use std::collections::HashMap;
use std::path::Path;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::test_support::{ReadProbe, parse_fsproj_reads};
use borzoi_msbuild::{PropertyRead, RejectionCertainty, parse_fsproj};
use common::{
    CONTROLLED_PROPERTY_NAMES, Oracle, SplitMix64, breaks_inside_quote, gen_bool_expr, gen_props,
    respell_whitespace,
};
use tempfile::TempDir;

/// Property names the generator may define. Disjoint from MSBuild reserved
/// names and from anything the process environment is likely to hold — MSBuild
/// folds the environment in as properties, and a collision would make the two
/// sides disagree for reasons unrelated to the XML layer.
const NAMES: &[&str] = &["Alpha", "Beta", "Gamma", "Delta"];

/// The body alphabet. This is the whole point of the harness, so it reaches
/// well past what the walker models — under certain-implies-exact a decline is
/// free, and only a *wrong commit* fails, so there is no reason to restrict the
/// inputs to shapes we understand.
///
/// `%XX` escapes are deliberately included: MSBuild unescapes them in the
/// evaluated value, and whether the walker models that or degrades, committing
/// the raw text would be a wrong commit — which is exactly the kind of thing
/// this harness exists to catch.
const BODIES: &[&str] = &[
    // Plain content, and the whitespace shapes the XML layer treats specially.
    "",
    "x",
    "a b",
    " ",
    "  ",
    "\t",
    "\r\n  ",
    "  x  ",
    // Comment-split text: MSBuild drops each whitespace-only text *node*, so
    // this is `x`, not `  x` — a per-node rule a whole-value collapse gets
    // wrong.
    "  <!-- c -->x",
    "a<!-- c --> ",
    "<!-- c --> <!-- d -->",
    "A<!-- c -->B",
    // Entity-encoded text. MSBuild is self-inconsistent on whitespace here
    // (`&#32;` is kept, `&#x20;` is dropped), so those must degrade.
    "&#32;",
    "&#x20;",
    "&#9;",
    "&#160;",
    "&amp;",
    "a&amp;b",
    "&lt;x&gt;",
    // CDATA: content is verbatim, and adjacent literal whitespace is still
    // insignificant. Beside other text it is read as the body's text when it
    // comes first, and as the body's inner XML otherwise.
    "<![CDATA[ ]]>",
    "<![CDATA[x]]>",
    " <![CDATA[ ]]> ",
    "<![CDATA[a<b]]>",
    "<![CDATA[]]>",
    "x<![CDATA[y]]>",
    "<![CDATA[y]]>x",
    "<!-- c --><![CDATA[y]]>",
    "x>&amp;<![CDATA[<y/>]]>",
    "&#160;<![CDATA[$(Alpha)]]>",
    "&#x20;<![CDATA[y]]>",
    "<![CDATA[100%]]>",
    // Line ends, which MSBuild reads as written and roxmltree folds: in a
    // node, split by a comment, spelt as references, and in CDATA.
    "a\r\nb",
    "a\rb",
    "\r\n  x\r\n",
    "a\r<!-- c -->\nb",
    "a&#13;&#10;b",
    "&#13;",
    "<![CDATA[a\r\nb]]>",
    // Substitution, including into the shapes above.
    "$(Alpha)",
    "x$(Alpha)y",
    " $(Alpha) ",
    "$(Undefined)",
    "$(Alpha.Length)",
    "$([System.IO.Path]::Combine('a','$(Alpha)'))",
    // Percent escapes: MSBuild unescapes; raw text would be a wrong commit.
    "%20",
    "a%20b",
    "%2f",
    "100%",
    "a%zb",
    // Quote characters (inert in a body, but they flow into later expressions).
    "a'b",
    "a`b",
    "a\"b",
    // Non-ASCII, incl. a non-BMP scalar (UTF-16-unit semantics downstream).
    "caf\u{e9}",
    "o\u{17f}x",
    "\u{1d11e}",
];

fn xml_escape_body(body: &str) -> String {
    // The bodies are *already* XML source fragments (they contain comments,
    // CDATA and entities on purpose), so they are emitted verbatim. Only the
    // generator is trusted to keep them well-formed; a malformed one would make
    // both sides fail to parse, which the harness reports rather than hides.
    body.to_string()
}

/// Build a project document from `(name, body)` writes, in order.
fn project_xml(writes: &[(&str, &str)]) -> String {
    let mut xml = String::from("<Project>\n  <PropertyGroup>\n");
    for (name, body) in writes {
        xml.push_str(&format!("    <{name}>{}</{name}>\n", xml_escape_body(body)));
    }
    xml.push_str("  </PropertyGroup>\n</Project>\n");
    xml
}

/// The differential contract for one document. Returns the number of properties
/// we committed (for the anti-vacuity floor).
fn check_property_table_certain_implies_exact(oracle: &mut Oracle, xml: &str) -> usize {
    check_at_path(oracle, xml, None)
}

/// As above, but the document is evaluated *at a real path* by both sides, so
/// MSBuild's reserved path derivatives (`MSBuildProjectDirectory`, …) agree with
/// the ones our walker seeds — the only way to diff anything they feed.
fn check_property_table_at_path(oracle: &mut Oracle, xml: &str, dir: &Path) -> usize {
    check_at_path(oracle, xml, Some(dir))
}

fn check_at_path(oracle: &mut Oracle, xml: &str, dir: Option<&Path>) -> usize {
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_string()).collect();
    check_names_at_path(oracle, xml, &names, dir).len()
}

/// [`check_at_path`] over a caller's set of names, returning those we
/// committed.
fn check_names_at_path(
    oracle: &mut Oracle,
    xml: &str,
    names: &[String],
    dir: Option<&Path>,
) -> Vec<String> {
    let owned;
    let project_path: &Path = match dir {
        Some(dir) => {
            owned = dir.join("Demo.fsproj");
            &owned
        }
        None => Path::new("/repo/proj/Demo.fsproj"),
    };
    let Ok(parsed) = parse_fsproj(
        xml,
        project_path,
        &HashMap::new(),
        &common::oracle_environment(),
    ) else {
        // Malformed XML: both sides reject, nothing to compare.
        return Vec::new();
    };

    // The walker's contract, not a stricter one — and it is **per property**.
    // A name whose write leaned on an undefined reference, or on a body we
    // declined to model, is still stored (MSBuild's unset-is-empty rule means
    // we have *a* value), but the walker marks its provenance untrusted and
    // consumers degrade on it (`ParsedProject::property` reads it untrusted).
    // Those names make no claim.
    //
    // Everything *else* in the same document still does. Skipping the whole
    // document whenever any diagnostic fired — which is what this used to do —
    // hid exactly the interesting case: a degraded `Alpha` next to a clean but
    // wrongly-evaluated `Beta` was never compared at all.
    let ours: Vec<(String, String)> = names
        .iter()
        .filter(|n| !parsed.property(n).untrusted_cause().is_some())
        .filter_map(|n| parsed.properties.get(n).map(|v| (n.clone(), v.clone())))
        .collect();

    let Some(theirs) = oracle.project(xml, names, dir.map(|_| project_path), &[]) else {
        assert!(
            ours.is_empty(),
            "certain-implies-exact violated: MSBuild rejects this project, but we \
             committed {ours:?}\n--- xml ---\n{xml}"
        );
        return Vec::new();
    };
    assert_ne!(
        parsed.rejection.as_ref().map(|r| r.certainty),
        Some(RejectionCertainty::Certain),
        "certain-implies-exact violated: we claim MSBuild rejects this project, and it \
         evaluates it\n--- xml ---\n{xml}"
    );

    for (name, our_value) in &ours {
        let their_value = theirs
            .get(name)
            .expect("oracle answers for every requested name");
        assert_eq!(
            our_value, their_value,
            "certain-implies-exact violated for ${{{name}}}: we evaluate it to \
             {our_value:?}, MSBuild to {their_value:?}\n--- xml ---\n{xml}"
        );
    }
    ours.into_iter().map(|(name, _)| name).collect()
}

/// Every body in the alphabet, on its own — the corner list. A failure here
/// names the exact shape.
#[test]
fn every_body_shape_is_exact_or_declined() {
    let mut oracle = Oracle::spawn();
    let mut committed = 0usize;
    for body in BODIES {
        let xml = project_xml(&[("Alpha", body)]);
        committed += check_property_table_certain_implies_exact(&mut oracle, &xml);
    }
    eprintln!("body corners: {committed} of {} committed", BODIES.len());
    // Anti-vacuity: a harness that declined everything would pass while testing
    // nothing on the committed side.
    assert!(
        committed >= 15,
        "too few committed body shapes ({committed}) — the walker may have \
         started declining everything, which passes vacuously"
    );
}

/// Bodies that *read* earlier properties, so an XML-layer mistake in the first
/// write propagates into a second one's expansion — the way it does in a real
/// chain (`<P> </P>` then `'$(P)' == ''`).
///
/// This cross product is what caught the composed-escape wrong-commit: with
/// `Alpha=100%` (a body that is *individually* fine — a bare `%` is literal in
/// MSBuild) the reader `$(Alpha)$(Alpha)` yields `100%100%`, in which MSBuild
/// reads `%10` as an escape and unescapes it to U+0010. Neither ingredient is
/// suspicious alone, and the guard in `substitute` was originally written
/// against the *input* rather than the composed result, so it missed exactly
/// this. Keep both ingredients in their pools.
#[test]
fn bodies_reading_earlier_writes_are_exact_or_declined() {
    let mut oracle = Oracle::spawn();
    let readers = [
        "$(Alpha)",
        "[$(Alpha)]",
        "$(Alpha.Length)",
        // Splices `Alpha` twice, so a value ending in a bare `%` can compose an
        // escape across the boundary. See the doc comment.
        "$(Alpha)$(Alpha)",
    ];
    let mut committed = 0usize;
    for body in BODIES {
        for reader in readers {
            let xml = project_xml(&[("Alpha", body), ("Beta", reader)]);
            committed += check_property_table_certain_implies_exact(&mut oracle, &xml);
        }
    }
    eprintln!("reader pairs: {committed} committed");
    assert!(committed >= 30, "too few committed ({committed})");
}

/// Bodies that read the **reserved path derivatives**, with the project living
/// at adversarial paths — including a directory whose name literally contains
/// `%20`.
///
/// This is the dimension the in-memory checks structurally cannot see: they hand
/// our parser a fake path while MSBuild evaluates a pathless document, so
/// anything `$(MSBuildProjectDirectory)` feeds is incomparable. It matters
/// because a `%XX` in a path-derived value is *not* an escape — MSBuild stores
/// reserved values pre-escaped, so a project in `…/a%20b/` really does resolve
/// `$(MSBuildProjectDirectory)/Foo.fs` to `…/a%20b/Foo.fs`. A guard that scans
/// only the composed result would drop that item; a reviewer caught exactly that
/// on this branch, and this test is how the machine catches it next time.
#[test]
fn reserved_path_properties_are_exact_or_declined() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dirs = [
        tmp.path().join("plain"),
        // A literal percent-two-hex in the directory name.
        tmp.path().join("a%20b"),
        // A trailing bare `%`, so the *next* characters in a body can compose an
        // escape across the boundary — that one really is an escape.
        tmp.path().join("pct%"),
        tmp.path().join("dot.ted"),
        // The other **eight** reserved characters MSBuild escapes when it seeds
        // a reserved path (`EscapingUtilities.cs:310` — `% * ? @ $ ( ) ; '`).
        // Tracking only `%` is what made a `;` in the project's own directory a
        // live wrong commit: the seed is escaped, so the `;` cannot split an
        // item list, the parens cannot open an expression, and the `*`/`?`
        // cannot glob. A generator over document *text* can never find this —
        // the input lives in the project's path, not in its XML.
        tmp.path().join("semi;colon"),
        tmp.path().join("paren(s)"),
        tmp.path().join("star*glob"),
        tmp.path().join("quest?ion"),
        tmp.path().join("at@sign"),
        tmp.path().join("dollar$sign"),
        tmp.path().join("quo'te"),
    ];
    let readers = [
        "$(MSBuildProjectDirectory)/Foo.fs",
        "$(MSBuildProjectDirectory)20b",
        "$(MSBuildProjectName)",
        "$(MSBuildProjectDirectory)$(MSBuildProjectExtension)",
        "$(MSBuildProjectDirectory)/$(Alpha)",
    ];
    let mut committed = 0usize;
    for dir in &dirs {
        std::fs::create_dir_all(dir).unwrap();
        for reader in readers {
            for body in ["x", "100%", " ", "%20"] {
                let xml = project_xml(&[("Alpha", body), ("Beta", reader)]);
                committed += check_property_table_at_path(&mut oracle, &xml, dir);
            }
        }
    }
    eprintln!("reserved-path readers: {committed} committed");
    assert!(committed >= 10, "too few committed ({committed})");
}

/// Bodies MSBuild reads apart from roxmltree's text (#642, #787, #855): an
/// element, a processing instruction or a CDATA section, which may make it
/// read the body's inner XML, and a carriage return, which it keeps where
/// roxmltree folds it. Each body's
/// value is pinned to MSBuild's, and whether we commit it is pinned too, so
/// that a reader which starts declining a body it reads exactly fails here
/// rather than passing the differential vacuously. Each is diffed alone and
/// read back by a later write, evaluated from text and from a file.
#[test]
fn bodies_msbuild_reads_as_inner_xml_or_unfolded_are_exact_or_declined() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_string()).collect();
    for (body, msbuild, committed) in [
        ("a<x/>b", "a<x />b", false),
        ("a<?p q?>b", "a<?p q?>b", false),
        ("a<?p q?>\r\nb", "a<?p q?>\r\nb", false),
        // A line end in content is read as written.
        ("a\r\nb", "a\r\nb", true),
        ("a\rb", "a\rb", true),
        ("a\r\r\nb", "a\r\r\nb", true),
        ("a\n\rb", "a\n\rb", true),
        ("\r\n  a;\r\n  b\r\n", "\r\n  a;\r\n  b\r\n", true),
        ("a&amp;\r\nb", "a&\r\nb", true),
        ("a\r\u{85}\u{2028}b", "a\r\u{85}\u{2028}b", true),
        // Spelt as references, the same.
        ("a&#13;b", "a\rb", true),
        ("a&#xD;&#10;b", "a\r\nb", true),
        ("&#13;a", "\ra", true),
        ("a&#13;\nb", "a\r\nb", true),
        // Each text node split by a comment keeps its own; a whitespace-only
        // one drops, line ends and all.
        ("a\r<!-- c -->\nb", "a\r\nb", true),
        ("a\r<!-- c -->", "a\r", true),
        ("\r\n<!-- c -->b", "b", true),
        ("a<!-- c\r\n -->b", "ab", true),
        ("\r\n", "", true),
        ("\r", "", true),
        // Whitespace spelt as a reference, which MSBuild keeps or drops by
        // its spelling.
        ("&#13;", "\r", false),
        ("&#x20;<![CDATA[x]]>", "x", false),
        ("&#32;<![CDATA[x]]>", " x", false),
        // CDATA: its content verbatim, line ends and all, and read as the
        // body's text when it is all of it or comes first (after Unicode
        // whitespace), as the body's inner XML otherwise.
        ("<![CDATA[a\r\nb]]>", "a\r\nb", true),
        ("<![CDATA[\r]]>", "\r", true),
        (" <![CDATA[\r\n]]> ", "\r\n", true),
        ("<![CDATA[]]>", "", true),
        ("<![CDATA[y]]>x<![CDATA[z]]>", "yxz", true),
        ("<![CDATA[]]>x<![CDATA[z]]>", "xz", true),
        ("<![CDATA[a]]><!--c-->b", "ab", true),
        ("\r\n  <![CDATA[a]]>\r\n  <!--c-->\r\n", "a", true),
        ("&#160;<![CDATA[a]]>x", "\u{a0}ax", true),
        ("\u{85}\u{2003}<![CDATA[a]]>x", "\u{85}\u{2003}ax", true),
        ("\u{200b}<![CDATA[a]]>x", "\u{200b}<![CDATA[a]]>x", true),
        ("<![CDATA[<a/>&amp;]]>", "<a/>&amp;", true),
        ("<![CDATA[]]]]><![CDATA[>]]>", "]]>", true),
        ("x<![CDATA[a\r\nb]]>y", "x<![CDATA[a\r\nb]]>y", true),
        ("x<![CDATA[]]>", "x<![CDATA[]]>", true),
        ("<!--c--><![CDATA[a]]>", "<!--c--><![CDATA[a]]>", true),
        (
            "a<!--c--> <![CDATA[z]]> <!--d-->b",
            "a<!--c--><![CDATA[z]]><!--d-->b",
            true,
        ),
        // Inner XML spells each text afresh: `>` and every reference to one
        // of `&`, `<` and `>` as an entity, every other character as itself.
        (
            "x>y&#38;&lt;&quot;'&#65;\t\r\n<![CDATA[z]]>",
            "x&gt;y&amp;&lt;\"'A\t\r\n<![CDATA[z]]>",
            true,
        ),
        (
            "x&#x1D11E;\u{e9}<![CDATA[a]]>",
            "x\u{1d11e}\u{e9}<![CDATA[a]]>",
            true,
        ),
        (
            "a<!-- c\r\n d -->b<![CDATA[z]]>",
            "a<!-- c\r\n d -->b<![CDATA[z]]>",
            true,
        ),
        // Expansion runs on what the XML layer reads, CDATA content included.
        ("<![CDATA[%41]]>", "A", true),
        ("x<![CDATA[%41]]>", "x<![CDATA[A]]>", true),
    ] {
        let xml = project_xml(&[("Alpha", body), ("Beta", "[$(Alpha)]")]);
        for at in [None, Some(dir.as_path())] {
            let path = at.map(|dir| dir.join("Demo.fsproj"));
            let theirs = oracle
                .project(&xml, &names, path.as_deref(), &[])
                .expect("MSBuild evaluates the document");
            assert_eq!(
                theirs["Alpha"], msbuild,
                "MSBuild's reading moved: {body:?} at {path:?}"
            );
            let ours = check_names_at_path(&mut oracle, &xml, &names, at);
            assert_eq!(
                ours.iter().any(|n| n == "Alpha"),
                committed,
                "the commitment moved: {body:?} at {path:?}"
            );
        }
    }
}

/// A project file written with CRLF line ends throughout, as on Windows: a
/// multi-line body keeps every CRLF, and its padding, where MSBuild does.
#[test]
fn a_crlf_project_reads_a_multi_line_body_as_written() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_string()).collect();
    let xml = project_xml(&[
        ("Alpha", "\n      a;\n      b\n    "),
        ("Beta", "$(Alpha.Length)"),
    ])
    .replace('\n', "\r\n");
    let theirs = oracle
        .project(&xml, &names, Some(&dir.join("Demo.fsproj")), &[])
        .expect("MSBuild evaluates the document");
    assert_eq!(theirs["Alpha"], "\r\n      a;\r\n      b\r\n    ");
    assert_eq!(theirs["Beta"], "25");
    let ours = check_names_at_path(&mut oracle, &xml, &names, Some(&dir));
    assert_eq!(ours, ["Alpha", "Beta"], "{xml:?}");
}

/// **Anti-degradation.** Certain-implies-exact is a one-sided contract: it
/// catches a wrong *commit*, and a diagnostic silently withdraws the claim — so
/// a spurious *decline* passes every check above vacuously. That is a real
/// failure mode (it is what a reviewer caught on this branch: a `%XX` in the
/// project's own directory name is *not* an escape, but a result-only escape
/// scan degraded the item anyway, quietly losing a Compile item MSBuild
/// resolves fine).
///
/// So: shapes that must **commit** are asserted to commit, with MSBuild's value.
/// Shapes that must **degrade** are asserted to degrade. Both directions, or the
/// harness only measures half of what it claims to.
#[test]
fn reserved_path_shapes_commit_or_degrade_as_pinned() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();

    // (directory name, body of `Beta`, must-commit?, MSBuild's value — with
    // `{dir}` standing for the project directory).
    //
    // **Every row's expected value is asserted against MSBuild**, degrade rows
    // included. That is deliberate: my first attempt at this table pinned the
    // `pct%` row the wrong way round, from the model I had just built rather
    // than from the oracle, and it passed. An expectation I reasoned out is
    // exactly as untrustworthy as the code I reasoned out.
    let cases: &[(&str, &str, bool, &str)] = &[
        (
            "plain",
            "$(MSBuildProjectDirectory)/Foo.fs",
            true,
            "{dir}/Foo.fs",
        ),
        ("plain", "$(MSBuildProjectName)", true, "Demo"),
        // The percent sequence comes from the project's own directory name,
        // where MSBuild treats it as literal text (it stores reserved values
        // pre-escaped). We must commit, not degrade.
        (
            "a%20b",
            "$(MSBuildProjectDirectory)/Foo.fs",
            true,
            "{dir}/Foo.fs",
        ),
        ("a%20b", "$(MSBuildProjectDirectory)", true, "{dir}"),
        // Provenance follows the **percent**, not the whole sequence: a trusted
        // `%` cannot introduce an escape even when the XML supplies the two hex
        // digits after it, so this is the literal `…/pct%20b`.
        ("pct%", "$(MSBuildProjectDirectory)20b", true, "{dir}20b"),
        // An escape authored in the XML is unescaped at the point of use, and
        // we now model that rather than degrading: MSBuild yields `a b`, and so
        // do we — in a plain directory and in one whose own name carries a `%`
        // (whose escape is a *different* percent, and stays inert).
        ("plain", "a%20b", true, "a b"),
        ("a%20b", "a%20b", true, "a b"),
        // A bare `%` authored in the XML can still compose an escape with
        // XML-authored hex digits: `100%` + `20b` → `%20` → a space. Composition
        // happens inside the escaped domain, so the leaf decodes what MSBuild
        // decodes.
        ("plain", "$(Pct)20b", true, "100 b"),
        // Trust must survive being laundered through an ordinary property write
        // (`Base` holds the reserved directory): still literal, still committed.
        ("a%20b", "$(Base)/Foo.fs", true, "{dir}/Foo.fs"),
        ("pct%", "$(Base)/Foo.fs", true, "{dir}/Foo.fs"),
        // A property-function *result* is escaped by MSBuild on the way out, so
        // its percent cannot introduce an escape — the exact opposite of the
        // plain `$(Pct)20b` splice two rows above, on the very same value.
        ("plain", "$(Pct.ToString())20b", true, "100%20b"),
        ("plain", "$(Pct.TrimStart('z'))20b", true, "100%20b"),
        // `TrimEnd` is not in our dispatch table, so this declines for an
        // unrelated reason — pinned so the row is not mistaken for an escape
        // failure if someone adds the member later.
        ("plain", "$(Pct.TrimEnd('z'))20b", false, "100%20b"),
        // A string indexer's `Char` is the one expression result MSBuild does
        // *not* escape, so its `%` still composes with the XML's hex digits and
        // is unescaped. The domain models that as the single raw entrance
        // (`Escaped::push_unescaped_raw`), so the value is right rather than
        // declined — and treating every result as escaped would commit `%20b`.
        ("plain", "$(Pct[3])20b", true, " b"),
        ("plain", "$(Pct[3])", true, "%"),
        // A reserved character in the project's own directory survives the seed's
        // escape and the leaf's unescape unchanged. Note what this does *not*
        // prove: `-getProperty` unescapes at the read, so the old raw-text seed
        // agreed here too. The escape only becomes observable where the value is
        // *scanned* — an item spec splitting on `;` — which is why the guard for
        // that lives in `fsproj_msbuild_diff.rs`
        // (`a_reserved_character_in_the_project_directory_does_not_split_items`).
        // Kept anyway: it pins the seed → value round trip these rows depend on.
        ("semi;colon", "$(MSBuildProjectDirectory)", true, "{dir}"),
        ("paren(s)", "$(MSBuildProjectDirectory)", true, "{dir}"),
        ("star*glob", "$(MSBuildProjectDirectory)", true, "{dir}"),
    ];

    for (dir_name, body, must_commit, expected) in cases {
        let dir = tmp.path().join(dir_name);
        std::fs::create_dir_all(&dir).unwrap();
        let project_path = dir.join("Demo.fsproj");
        // Preludes: `Pct` is XML-authored text ending in a bare `%` (so it *can*
        // compose an escape with XML hex digits), and `Base` launders a trusted
        // reserved value through an ordinary property write — whose provenance
        // must survive, or `$(Base)/Foo.fs` under `…/a%20b/` would wrongly
        // degrade (codex found precisely that).
        let xml = project_xml(&[
            ("Pct", "100%"),
            ("Base", "$(MSBuildProjectDirectory)"),
            ("Beta", body),
        ]);
        let parsed = parse_fsproj(
            &xml,
            &project_path,
            &HashMap::new(),
            &common::oracle_environment(),
        )
        .expect("well-formed");
        let names = vec!["Beta".to_string()];
        let theirs = oracle
            .project(&xml, &names, Some(&project_path), &[])
            .expect("MSBuild evaluates these documents");
        let theirs = theirs.get("Beta").expect("oracle answers for Beta");

        // Every row's expectation is checked against MSBuild — including the
        // degrade rows, whose whole justification is that MSBuild's value is
        // *not* the raw text we would otherwise have committed.
        let want = expected.replace("{dir}", &dir.to_string_lossy());
        assert_eq!(
            theirs, &want,
            "in {dir_name}/, body {body:?}: the pinned MSBuild value is wrong"
        );

        let committed = parsed.diagnostics.is_empty() && parsed.properties.contains_key("Beta");
        assert_eq!(
            committed, *must_commit,
            "in {dir_name}/, body {body:?}: expected must_commit={must_commit}, got \
             committed={committed} (diagnostics: {:?})",
            parsed.diagnostics
        );
        if *must_commit {
            assert_eq!(
                parsed.properties.get("Beta").map(String::as_str),
                Some(theirs.as_str()),
                "in {dir_name}/, body {body:?}"
            );
        }
    }
}

/// Duplicate imports. MSBuild registers every performed import in a
/// per-evaluation seen-set (`Evaluator._importsSeen`,
/// `StringComparer.OrdinalIgnoreCase` over the lexically-normalised path —
/// **no symlink resolution**) *before* walking the imported file, and skips
/// any later import that resolves to a seen path with warning MSB4011
/// (MSB4210 when the target is the entry project). The evaluation succeeds,
/// so the walker must both skip the duplicate and stay non-partial:
/// re-running an imported body silently doubles an accumulator property
/// (`$(Order)a` → `aa` vs MSBuild's `a`) in a result that claims exactness.
///
/// Every cluster's expected value is read from the oracle evaluating the same
/// on-disk file cluster, never hand-pinned; each cluster gets its own
/// directory so the wildcard case cannot see its neighbours' props files.
#[test]
fn duplicate_imports_are_skipped_exactly() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();

    const ACCUMULATE_A: &str =
        r#"<Project><PropertyGroup><Order>$(Order)a</Order></PropertyGroup></Project>"#;
    let entry = |imports: &str| {
        format!(
            "<Project>\n{imports}\n  <PropertyGroup>\n    <R>[$(Order)]</R>\n  </PropertyGroup>\n</Project>"
        )
    };

    struct Cluster {
        name: &'static str,
        entry: String,
        files: Vec<(&'static str, &'static str)>,
    }
    let mut cases = vec![
        Cluster {
            name: "dup-segment",
            entry: entry(r#"  <Import Project="a.props;a.props" />"#),
            files: vec![("a.props", ACCUMULATE_A)],
        },
        Cluster {
            name: "repeated-elements",
            entry: entry("  <Import Project=\"a.props\" />\n  <Import Project=\"a.props\" />"),
            files: vec![("a.props", ACCUMULATE_A)],
        },
        Cluster {
            name: "wildcard-overlap",
            entry: entry(r#"  <Import Project="a.props;*.props" />"#),
            files: vec![("a.props", ACCUMULATE_A)],
        },
        Cluster {
            name: "respelt",
            entry: entry(r#"  <Import Project="a.props;sub/../a.props;A.PROPS" />"#),
            files: vec![("a.props", ACCUMULATE_A), ("sub/.keep", "")],
        },
        Cluster {
            name: "cycle",
            entry: entry(r#"  <Import Project="a.props" />"#),
            files: vec![
                (
                    "a.props",
                    "<Project>\n  <PropertyGroup><Order>$(Order)a</Order></PropertyGroup>\n  <Import Project=\"b.props\" />\n</Project>",
                ),
                (
                    "b.props",
                    "<Project>\n  <PropertyGroup><Order>$(Order)b</Order></PropertyGroup>\n  <Import Project=\"a.props\" />\n</Project>",
                ),
            ],
        },
        Cluster {
            name: "unicode-distinct",
            // Dotted capital İ vs plain i: .NET's OrdinalIgnoreCase keeps
            // the pair distinct (its ordinal casing table carves out the
            // Turkish-I family), so MSBuild imports both — and so do we,
            // with certainty, because Unicode's fold also keeps İ
            // distinct. Pins the fuzzy tier against over-widening.
            entry: entry("  <Import Project=\"\u{130}.props;i.props\" />"),
            files: vec![
                ("\u{130}.props", ACCUMULATE_A),
                (
                    "i.props",
                    r#"<Project><PropertyGroup><Order>$(Order)b</Order></PropertyGroup></Project>"#,
                ),
            ],
        },
        Cluster {
            name: "self-import",
            entry: "<Project>\n  <PropertyGroup><Order>$(Order)x</Order></PropertyGroup>\n  <Import Project=\"Demo.fsproj\" />\n  <PropertyGroup>\n    <R>[$(Order)]</R>\n  </PropertyGroup>\n</Project>".to_string(),
            files: vec![],
        },
    ];
    // A symlink alias is a *distinct* import — MSBuild's key never resolves
    // symlinks, so the body genuinely runs twice. Guards the dedup key's
    // domain: keying on the canonicalised path would skip this one and
    // diverge in the opposite direction.
    #[cfg(unix)]
    cases.push(Cluster {
        name: "symlink-alias",
        entry: entry(r#"  <Import Project="a.props;link.props" />"#),
        files: vec![("a.props", ACCUMULATE_A)],
    });

    for Cluster {
        name: cluster,
        entry: xml,
        files,
    } in &cases
    {
        let dir = tmp.path().join(cluster);
        std::fs::create_dir_all(&dir).unwrap();
        for (name, contents) in files {
            let path = dir.join(name);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, contents).unwrap();
        }
        #[cfg(unix)]
        if *cluster == "symlink-alias" {
            std::os::unix::fs::symlink(dir.join("a.props"), dir.join("link.props")).unwrap();
        }
        let project_path = dir.join("Demo.fsproj");
        // On disk for our walker too: the self-import cluster follows an
        // import *of the entry file itself*, which must be readable.
        std::fs::write(&project_path, xml).unwrap();

        let parsed = parse_fsproj_with_imports(
            xml,
            &project_path,
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed");
        let names = vec!["R".to_string()];
        let theirs = oracle
            .project(xml, &names, Some(&project_path), &[])
            .expect("MSBuild evaluates every duplicate-import cluster (the skip is a warning)");
        let theirs = theirs.get("R").expect("oracle answers for R");

        // Must-commit, not just exact-if-committed: a walker that degraded
        // these shapes would pass a one-sided check vacuously, and MSBuild
        // treats every one of them as an ordinary clean evaluation.
        assert!(
            !parsed.is_partial,
            "{cluster}: duplicate imports are a clean skip in MSBuild, not a \
             degrade (diagnostics: {:?})",
            parsed.diagnostics
        );
        assert_eq!(
            parsed.properties.get("R").map(String::as_str),
            Some(theirs.as_str()),
            "{cluster}: certain-implies-exact violated (diagnostics: {:?})",
            parsed.diagnostics
        );
    }
}

/// `text` escaped as an attribute value, its whitespace left as written: a tab,
/// line feed or carriage return reaches MSBuild as itself (#750).
fn raw_attribute(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// An attribute value from [`raw_attribute`] with, now and then, a tab, line
/// feed or carriage return spelt as a character reference (decimal or hex) and
/// a `'` as `&apos;`. Both readers decode each to the character it names, and
/// neither normalises a character a reference spells.
fn entity_spelt(rng: &mut SplitMix64, attribute: &str) -> String {
    let mut out = String::with_capacity(attribute.len());
    for c in attribute.chars() {
        match c {
            '\t' | '\n' | '\r' if rng.below(2) == 0 => {
                let code = u32::from(c);
                if rng.below(2) == 0 {
                    out.push_str(&format!("&#{code};"));
                } else {
                    out.push_str(&format!("&#x{code:X};"));
                }
            }
            '\'' if rng.below(4) == 0 => out.push_str("&apos;"),
            c => out.push(c),
        }
    }
    out
}

/// How many places [`conditioned_document`] can put a condition.
const CONDITION_SITES: usize = 3;

/// A document that sets `props`, then writes `R` as `TRUE` exactly when the
/// condition attribute `attribute` holds, read at site `site` (below
/// [`CONDITION_SITES`]): on the write, on its group, or on a `<When>`.
fn conditioned_document(props: &[(String, String)], attribute: &str, site: usize) -> String {
    let mut xml = String::from("<Project>\n  <PropertyGroup>\n");
    for (name, value) in props {
        xml.push_str(&format!("    <{name}>{value}</{name}>\n"));
    }
    xml.push_str("  </PropertyGroup>\n");
    xml.push_str(&match site {
        0 => format!(
            "  <PropertyGroup>\n    <R>FALSE</R>\n    \
             <R Condition=\"{attribute}\">TRUE</R>\n  </PropertyGroup>\n"
        ),
        1 => format!(
            "  <PropertyGroup>\n    <R>FALSE</R>\n  </PropertyGroup>\n  \
             <PropertyGroup Condition=\"{attribute}\">\n    <R>TRUE</R>\n  </PropertyGroup>\n"
        ),
        _ => format!(
            "  <Choose>\n    <When Condition=\"{attribute}\">\n      \
             <PropertyGroup><R>TRUE</R></PropertyGroup>\n    </When>\n    <Otherwise>\n      \
             <PropertyGroup><R>FALSE</R></PropertyGroup>\n    </Otherwise>\n  </Choose>\n"
        ),
    });
    xml.push_str("</Project>\n");
    xml
}

/// The probe of #750: a line break inside a quoted string of a condition is a
/// character, and outside one it is whitespace, because MSBuild reads a
/// project's attributes without XML's attribute-value normalisation. Each
/// verdict is pinned as well as diffed, since a document both sides misread
/// alike would pass the differential alone, and so is whether we commit. (The
/// property-function evaluator declines a line break in a string argument.)
#[test]
fn a_line_break_in_a_condition_is_read_as_written() {
    let mut oracle = Oracle::spawn();
    let props = [("Foo".to_string(), "x y".to_string())];
    let names = ["R".to_string()];
    for (attribute, msbuild, commits) in [
        ("'$(Foo)' == 'x\ny'", "FALSE", true),
        ("'$(Foo)' ==\n 'x y'", "TRUE", true),
        ("'$(Foo)' == 'x\ty'", "FALSE", true),
        ("'$(Foo)' == 'x\r\ny'", "FALSE", true),
        ("'$(Foo)' == 'x\ry'", "FALSE", true),
        ("'$(Foo)'\r==\t'x y'", "TRUE", true),
        ("'$(Foo)' == 'x&#10;y'", "FALSE", true),
        ("'$(Foo)' == 'x&#x9;y'", "FALSE", true),
        ("'$(Foo)' == 'x&#32;y'", "TRUE", true),
        ("&apos;$(Foo)&apos; == 'x y'", "TRUE", true),
        ("$(Foo.Contains('x\ny'))", "FALSE", false),
        ("$(Foo.Contains('x\r\ny'))", "FALSE", false),
        ("$(Foo.Contains('x\ry'))", "FALSE", false),
        ("$(Foo.Contains('x y'))", "TRUE", true),
    ] {
        for site in 0..CONDITION_SITES {
            let xml = conditioned_document(&props, attribute, site);
            let theirs = oracle
                .project(&xml, &names, None, &[])
                .expect("MSBuild evaluates the document");
            assert_eq!(theirs["R"], msbuild, "MSBuild's verdict moved\n{xml:?}");
            let ours = check_names_at_path(&mut oracle, &xml, &names, None);
            assert_eq!(
                !ours.is_empty(),
                commits,
                "whether we commit R moved\n{xml:?}"
            );
        }
    }
}

/// `text` with each space respelt as a space, tab, line feed, carriage return
/// or CRLF. Unlike [`respell_whitespace`] it inserts none, so a bare token
/// stays whole and the condition stays legal.
fn respell_spaces(rng: &mut SplitMix64, text: &str) -> String {
    const WHITESPACE: [&str; 5] = [" ", "\t", "\n", "\r", "\r\n"];
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if c == ' ' {
            out.push_str(rng.pick(&WHITESPACE));
        } else {
            out.push(c);
        }
    }
    out
}

/// The value of `$(Spaced)`, which [`gen_spaced_condition`] compares against
/// quoted strings holding spaces: where a respelt space inside a quote decides
/// the verdict.
const SPACED_VALUES: &[&str] = &["a b", " a b ", "a  b", "ab", ""];

/// Comparisons whose quoted strings hold spaces, joined by `And`/`Or`.
fn gen_spaced_condition(rng: &mut SplitMix64) -> String {
    const OPERANDS: &[&str] = &[
        "'$(Spaced)'",
        "'a b'",
        "' a b '",
        "'a  b'",
        "'ab'",
        "''",
        "'$(Spaced) '",
        "'$([System.String]::Copy(' a b ').Trim())'",
        "$([System.String]::Copy('a b').Length)",
        "3",
    ];
    let mut condition = String::new();
    for i in 0..1 + rng.below(2) {
        if i > 0 {
            condition.push_str(if rng.below(2) == 0 { " And " } else { " Or " });
        }
        let op = if rng.below(2) == 0 { "==" } else { "!=" };
        condition.push_str(&format!(
            "{} {op} {}",
            rng.pick(OPERANDS),
            rng.pick(OPERANDS)
        ));
    }
    condition
}

/// How many documents [`conditions_with_raw_whitespace_are_exact_or_declined`]
/// generates that MSBuild rejects for a condition the walk reads as
/// unmodelled rather than illegal (#783).
const RAW_WHITESPACE_REJECTED_UNMODELLED: usize = 121;

/// The whitespace axis at the XML layer (#750): conditions, generated and
/// built around quoted strings holding spaces, with their spaces respelt as
/// raw tabs, line feeds, carriage returns and CRLFs (and, now and then,
/// whitespace inserted), half of them with some of those spelt as character
/// references, read from a document at each condition site.
/// `condition_diff`'s whitespace axis grades the evaluator on such text; this
/// grades the walk's reading of it from the attribute.
#[test]
fn conditions_with_raw_whitespace_are_exact_or_declined() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x0750_a771_b0de);
    let names: Vec<String> = ["R", "Spaced"]
        .into_iter()
        .chain(CONTROLLED_PROPERTY_NAMES.iter().copied())
        .map(str::to_string)
        .collect();
    const CASES: usize = 1500;
    let mut decided = 0usize;
    let mut decided_inside_quote = 0usize;
    let mut rejected = 0usize;
    let mut rejected_unmodelled = 0usize;
    for _ in 0..CASES {
        let mut props = gen_props(&mut rng);
        props.push(("Spaced".to_string(), rng.pick(SPACED_VALUES).to_string()));
        let condition = if rng.below(2) == 0 {
            gen_spaced_condition(&mut rng)
        } else {
            let depth = rng.below(3) as u32;
            gen_bool_expr(&mut rng, depth)
        };
        let condition = if rng.below(4) == 0 {
            respell_whitespace(&mut rng, &condition)
        } else {
            respell_spaces(&mut rng, &condition)
        };
        let mut attribute = raw_attribute(&condition);
        if rng.below(2) == 0 {
            attribute = entity_spelt(&mut rng, &attribute);
        }
        let site = rng.below(CONDITION_SITES);
        let xml = conditioned_document(&props, &attribute, site);
        // A condition MSBuild finds illegal (whitespace inserted inside a bare
        // token makes many) rejects the whole project. One the walk finds
        // illegal withdraws everything, which is graded as for every document;
        // one it calls unmodelled keeps the writes around it, and grades
        // nothing here. Those are counted, and the count pinned: it moves only
        // when the evaluator classifies more of MSBuild's rejections (#783).
        if oracle.project(&xml, &names, None, &[]).is_none() {
            rejected += 1;
            let parsed = parse_fsproj(
                &xml,
                Path::new("/repo/proj/Demo.fsproj"),
                &HashMap::new(),
                &common::oracle_environment(),
            )
            .expect("well-formed");
            if parsed.rejection.is_some() {
                check_names_at_path(&mut oracle, &xml, &names, None);
            } else {
                rejected_unmodelled += 1;
            }
            continue;
        }
        if check_names_at_path(&mut oracle, &xml, &names, None).contains(&names[0]) {
            decided += 1;
            decided_inside_quote += usize::from(breaks_inside_quote(&condition));
        }
    }
    eprintln!(
        "raw-whitespace conditions: {decided} of {CASES} decided, \
         {decided_inside_quote} with a break inside a quote, {rejected} rejected by MSBuild, \
         {rejected_unmodelled} of them read as unmodelled"
    );
    assert_eq!(
        rejected_unmodelled, RAW_WHITESPACE_REJECTED_UNMODELLED,
        "the rejected documents whose condition the walk reads as unmodelled moved: \
         pin the new count if the evaluator now classifies more of them as illegal"
    );
    assert!(decided >= 500, "only {decided} of {CASES} decided");
    assert!(
        decided_inside_quote >= 100,
        "only {decided_inside_quote} decided with a break inside a quote"
    );
}

/// An `<Import>`'s `Project`, and the `Exists` its condition probes, read with
/// a tab as written (#750): the file named with a tab is the one MSBuild
/// imports, not its neighbour named with a space.
#[test]
fn an_import_path_holding_a_tab_is_read_as_written() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    for (name, value) in [("a b.props", "space"), ("a\tb.props", "tab")] {
        std::fs::write(
            dir.join(name),
            format!("<Project><PropertyGroup><Alpha>{value}</Alpha></PropertyGroup></Project>"),
        )
        .unwrap();
    }
    let project_path = dir.join("Demo.fsproj");
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_string()).collect();
    for import in [
        "<Import Project=\"a\tb.props\" />",
        "<Import Project=\"$(MSBuildProjectDirectory)/a\tb.props\" Condition=\"Exists('a\tb.props')\" />",
        "<Import Project=\"a&#9;b.props\" />",
    ] {
        let xml = format!("<Project>\n  {import}\n</Project>\n");
        std::fs::write(&project_path, &xml).unwrap();
        let parsed = parse_fsproj_with_imports(
            &xml,
            &project_path,
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed");
        let theirs = oracle
            .project(&xml, &names, Some(&project_path), &[])
            .expect("MSBuild evaluates the document");
        assert_eq!(theirs["Alpha"], "tab", "MSBuild's import moved\n{xml}");
        if !parsed.property("Alpha").untrusted_cause().is_some() {
            assert_eq!(
                parsed.properties.get("Alpha").map(String::as_str),
                Some("tab"),
                "certain-implies-exact violated\n{xml}"
            );
        }
    }
}

/// Fixed-seed sweep over multi-write documents: several properties, adversarial
/// bodies, later ones reading earlier ones.
#[test]
fn fixed_seed_document_sweep() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x5eed_1a7e_d0c5);

    const CASES: usize = 1500;
    let mut committed = 0usize;
    for _ in 0..CASES {
        let count = 1 + rng.below(4);
        let writes: Vec<(&str, &str)> = (0..count)
            .map(|i| (NAMES[i % NAMES.len()], *rng.pick(BODIES)))
            .collect();
        let xml = project_xml(&writes);
        committed += check_property_table_certain_implies_exact(&mut oracle, &xml);
    }
    eprintln!("document sweep: {committed} committed over {CASES} documents");
    assert!(
        committed >= 500,
        "too few committed ({committed}) over {CASES} documents"
    );
}

/// Text pieces of a generated CDATA-bearing body, as element content spells
/// them: plain text, XML whitespace (insignificant alone), Unicode whitespace
/// that is not XML's (which .NET's `TrimStart` skips before a CDATA section),
/// whitespace spelt as a reference (which MSBuild keeps or drops by its
/// spelling), the characters inner XML re-spells, and what expansion reads.
const CDATA_TEXT: &[&str] = &[
    "x",
    "a b",
    " ",
    "\r\n  ",
    "\t",
    "\r",
    "\u{a0}",
    "&#160;",
    "\u{85}\u{2003}",
    "\u{200b}",
    "&#32;",
    "&#x20;",
    "&#13;",
    ">",
    "&gt;",
    "&amp;",
    "&lt;",
    "&quot;'",
    "&#65;",
    "\u{1d11e}",
    "$(Alpha)",
    "%41",
    "a;b",
];

/// Comments of a generated body, one holding what looks like a CDATA section.
const CDATA_COMMENTS: &[&str] = &[
    "<!-- c -->",
    "<!---->",
    "<!--<![CDATA[x]]>-->",
    "<!--\r\n-->",
];

/// CDATA section contents: nothing, whitespace and line ends (verbatim, and
/// never insignificant), markup-like text (an element, a comment, an entity,
/// a section opening, `]]`), and what expansion reads.
const CDATA_CONTENTS: &[&str] = &[
    "",
    " ",
    "x",
    "a\r\nb",
    "\r",
    "<a/>",
    "<!-- c -->",
    "&amp;",
    "<![CDATA[",
    "]]",
    "]",
    ">",
    "\u{a0}",
    "$(Alpha)",
    "%41",
    "100%",
    "a;b",
];

/// A body of one to five pieces (text, comment or CDATA section, CDATA the
/// likeliest), as element content spells it, holding at least one CDATA
/// section.
fn gen_cdata_body(rng: &mut SplitMix64) -> String {
    loop {
        let mut body = String::new();
        let mut has_cdata = false;
        for _ in 0..1 + rng.below(5) {
            match rng.below(5) {
                0 | 1 => body.push_str(rng.pick(CDATA_TEXT)),
                2 => body.push_str(rng.pick(CDATA_COMMENTS)),
                _ => {
                    has_cdata = true;
                    body.push_str(&format!("<![CDATA[{}]]>", rng.pick(CDATA_CONTENTS)));
                }
            }
        }
        // Text holding `]]>` is not well formed, so only a body free of it
        // outside its sections tests anything.
        let outside: String = body
            .split("<![CDATA[")
            .map(|s| s.rsplit("]]>").next().unwrap_or(s))
            .collect();
        if has_cdata && !outside.contains("]]>") {
            return body;
        }
    }
}

/// Start-tag attributes for an element whose body is generated: none, or a
/// condition holding a `>` and quotes of either kind, which a reader of the
/// body must not take for the end of the start tag.
const CDATA_CONDITIONS: &[&str] = &[
    "",
    " Condition=\"'>' != '&quot;'\"",
    " Condition = '&apos;\"&gt;&apos; != &apos;>&apos;' ",
];

/// `body`, element content, spelt as an attribute value whose reading is
/// `body` itself.
fn attribute_spelling(body: &str) -> String {
    body.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('"', "&quot;")
}

/// What a generated CDATA sweep committed: property bodies, and metadata
/// written as an element's content and as an attribute.
#[derive(Default, Debug)]
struct CdataTally {
    properties: usize,
    content: usize,
    attribute: usize,
}

/// One generated CDATA-bearing document: `body` as a property's body (read
/// back by a later write), as a metadatum's element content, and, spelt as an
/// attribute, as a metadatum MSBuild stores as element content and reads back
/// (`SetXmlNodeInnerContents`). Every value we commit must be MSBuild's.
fn check_cdata_document(oracle: &mut Oracle, body: &str, condition: &str, tally: &mut CdataTally) {
    let attribute = attribute_spelling(body);
    let xml = format!(
        "<Project>\n  <PropertyGroup>\n    <Alpha{condition}>{body}</Alpha>\n    <Beta>[$(Alpha)]</Beta>\n  \
         </PropertyGroup>\n  <ItemGroup>\n    <Helper Include=\"a\" Attr=\"{attribute}\">\n      \
         <Content{condition}>{body}</Content>\n    </Helper>\n  </ItemGroup>\n</Project>\n"
    );
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_string()).collect();
    let committed = check_names_at_path(oracle, &xml, &names, None);
    tally.properties += usize::from(committed.iter().any(|n| n == "Alpha"));

    let dir = TempDir::new().unwrap();
    let path = borzoi_msbuild::observed::host_fs::canonicalize(dir.path())
        .unwrap()
        .join("p.fsproj");
    let probe = ReadProbe {
        item_types: vec!["Helper".to_owned()],
        ..ReadProbe::default()
    };
    let (_, reads) = parse_fsproj_reads(
        &xml,
        &path,
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
        &probe,
    )
    .expect("the generated document parses");
    let read = &reads.items["Helper"];
    let Some(theirs) = oracle.items_meta(&xml, &path, "Helper", &["Attr", "Content"]) else {
        assert!(
            !read.exact,
            "MSBuild rejects the project, and we read its items\n{xml}"
        );
        return;
    };
    if !read.exact {
        return;
    }
    let [row] = read.items.as_deref().unwrap_or_default() else {
        panic!("one Helper item, not {:?}\n{xml}", read.items);
    };
    assert_eq!(theirs.len(), 1, "{xml}");
    for (name, key, count) in [
        ("Attr", "attr", &mut tally.attribute),
        ("Content", "content", &mut tally.content),
    ] {
        if row.uncertain_metadata.iter().any(|n| n == key) {
            continue;
        }
        let Some(ours) = row.metadata.get(key) else {
            continue;
        };
        assert_eq!(
            ours, &theirs[0].1[name],
            "certain-implies-exact violated for %({name}): we read {ours:?}, MSBuild {:?}\n{xml}",
            theirs[0].1[name]
        );
        *count += 1;
    }
}

/// Generated bodies holding CDATA sections among text, comments and entities,
/// with markup-like text inside the sections, in each position MSBuild reads
/// a body: a property, a metadatum's element content, and a metadatum's
/// attribute (whose value MSBuild parses as XML when it holds a `<`). Every
/// committed value must be MSBuild's, and enough commit in each position that
/// the claim is not vacuous.
#[test]
fn generated_cdata_bodies_are_exact_or_declined() {
    cdata_sweep(0xcda7_a5ec_7105, 500);
}

/// [`generated_cdata_bodies_are_exact_or_declined`] from a fresh seed, at a
/// volume `BORZOI_MSBUILD_SOAK_CASES` sets.
#[test]
#[ignore = "soak: fresh seed"]
fn generated_cdata_bodies_soak() {
    let (seed, cases) = common::soak_parameters("generated_cdata_bodies", 5000);
    cdata_sweep(seed, cases);
}

fn cdata_sweep(seed: u64, cases: usize) {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let mut tally = CdataTally::default();
    for _ in 0..cases {
        let body = gen_cdata_body(&mut rng);
        let condition = *rng.pick(CDATA_CONDITIONS);
        check_cdata_document(&mut oracle, &body, condition, &mut tally);
    }
    eprintln!("generated CDATA bodies: {tally:?} committed over {cases} documents");
    for (position, committed) in [
        ("property", tally.properties),
        ("element content", tally.content),
        ("attribute", tally.attribute),
    ] {
        assert!(
            committed * 4 >= cases,
            "too few {position} bodies committed ({committed} of {cases})"
        );
    }
}

/// `<Choose>` nesting around MSBuild's ceiling. MSBuild's loader refuses a
/// `<Choose>` nested more than `ProjectParser.MaximumChooseNesting` (50) deep
/// (`ChooseOverflow`), so the whole project fails to load; one level less
/// evaluates normally. Each depth is pinned to the verdict MSBuild gives it as
/// well as diffed, since a fixture both sides misjudge alike passes the
/// differential alone.
#[test]
fn choose_nesting_around_msbuilds_ceiling_is_exact() {
    let mut oracle = Oracle::spawn();
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_string()).collect();
    for (depth, msbuild_loads) in [(1, true), (49, true), (50, true), (51, false), (52, false)] {
        // Writes at the outermost and innermost levels: an evaluator that
        // checked the ceiling only once it had walked in would commit the first.
        let xml = format!(
            "<Project>\n{}<PropertyGroup><Beta>inner</Beta></PropertyGroup>{}\n</Project>\n",
            "<Choose><When Condition=\"'$(Gamma)' == ''\">\
             <PropertyGroup><Alpha>outer</Alpha></PropertyGroup>"
                .repeat(depth),
            "</When></Choose>".repeat(depth),
        );
        let theirs = oracle.project(&xml, &names, None, &[]);
        assert_eq!(
            theirs.is_some(),
            msbuild_loads,
            "MSBuild's verdict on {depth} nested Chooses moved"
        );
        let committed = check_property_table_certain_implies_exact(&mut oracle, &xml);
        assert_eq!(
            committed,
            if msbuild_loads { 2 } else { 0 },
            "{depth} nested Chooses: we committed {committed} of Alpha, Beta"
        );
    }
}

/// An undecided `<Choose>` — one whose `<When>` sits outside the condition
/// grammar — hides exactly the property writes its still-possible branches
/// hold, name by name. Items are pass-3 content and write no property, so a
/// branch holding only items hides nothing: later reads of never-written names
/// stay exact. Each row is diffed with MSBuild taking the branch and with it
/// skipping the branch, and pinned to the number of properties we commit, since
/// a model that declined after every undecided `<Choose>` would pass the
/// differential alone.
#[test]
fn an_undecided_choose_hides_only_the_names_its_branches_write() {
    let mut oracle = Oracle::spawn();
    // (branch body, whether it writes `Gamma`).
    let rows: &[(&str, bool)] = &[
        (r#"<ItemGroup><None Include="x.txt" /></ItemGroup>"#, false),
        (
            r#"<ItemGroup><Compile Include="A.fs" /></ItemGroup>"#,
            false,
        ),
        (
            r#"<ItemGroup><PackageReference Include="P" Version="1.0.0" /></ItemGroup>"#,
            false,
        ),
        (
            r#"<ItemGroup><ProjectReference Include="../A/A.fsproj" /><ProjectReference Remove="../B/B.fsproj" /></ItemGroup>"#,
            false,
        ),
        (
            r#"<Choose><When Condition="'a' == 'a'"><ItemGroup><Helper Include="h" /></ItemGroup></When></Choose>"#,
            false,
        ),
        (
            r#"<PropertyGroup><Gamma>g</Gamma></PropertyGroup><ItemGroup><None Include="x.txt" /></ItemGroup>"#,
            true,
        ),
        (
            r#"<ItemGroup><None Include="x.txt" /></ItemGroup><Choose><When Condition="'a' == 'b'"><PropertyGroup><Gamma>g</Gamma></PropertyGroup></When></Choose>"#,
            true,
        ),
    ];
    for (branch, writes_gamma) in rows {
        for gate in ["==", "!="] {
            let xml = format!(
                "<Project>\n  <Choose>\n    <When Condition=\"'$([System.Guid]::NewGuid())' {gate} ''\">\n      \
                 {branch}\n    </When>\n  </Choose>\n  <PropertyGroup>\n    \
                 <Alpha Condition=\"'$(Gamma)' == ''\">a</Alpha>\n    \
                 <Beta Condition=\"'$(Delta)' == ''\">b</Beta>\n  </PropertyGroup>\n</Project>\n"
            );
            let committed = check_property_table_certain_implies_exact(&mut oracle, &xml);
            // `Beta` reads a name nothing writes; `Alpha` reads one only some
            // branches write. `Gamma` itself is never committed (unset, or
            // written under the undecided gate), nor is the unwritten `Delta`.
            let expected = if *writes_gamma { 1 } else { 2 };
            assert_eq!(
                committed, expected,
                "undecided branch {branch} (gate {gate}): committed {committed}\n{xml}"
            );
        }
    }
}

/// Imports MSBuild may fail to load (#820, #845): a missing file, a directory,
/// a dangling link, malformed XML, an empty path, and a path the walk cannot
/// compute, each under a gate the walk decides either way, cannot decide, or
/// that requires the file. MSBuild rejects the whole project when it attempts
/// one (MSB4019, MSB4025, MSB4020/MSB4035), so the writes before and after it
/// are graded too: a project MSBuild rejects must commit nothing, and one it
/// evaluates must commit only its values. The cross product is the sweep, so
/// the undecided gates meet every target.
#[test]
fn import_failures_commit_nothing_for_a_project_msbuild_rejects() {
    const UNDECIDED_TRUE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";
    const UNDECIDED_FALSE: &str = "$([System.String]::IsNullOrWhiteSpace('no'))";
    // `{p}` is the import's own `Project` text.
    const PROBES_ITS_OWN_FILE_OR_IS_FALSE: &[&str] = &[
        "'a' == 'b'",
        "Exists('{p}')",
        "UNDECIDED_TRUE And Exists('{p}')",
    ];
    let gates = [
        "",
        "'a' == 'a'",
        "'a' == 'b'",
        UNDECIDED_TRUE,
        UNDECIDED_FALSE,
        "Exists('{p}')",
        "UNDECIDED_TRUE Or Exists('{p}')",
        "UNDECIDED_FALSE Or Exists('{p}')",
        "UNDECIDED_TRUE And Exists('{p}')",
    ];
    // `(Project text, a write before the import that the text reads)`.
    let targets: &[(&str, &str)] = &[
        ("there.props", ""),
        ("missing.props", ""),
        ("sub", ""),
        ("bad.props", ""),
        ("$(Nothing)", ""),
        ("none/*.props", ""),
        ("there.props;missing.props", ""),
        // A case respelling of an import already made: MSBuild skips it
        // unloaded, whatever the file system holds.
        ("THERE.props", "<Import Project=\"there.props\" />"),
        ("there.props;THERE.props", ""),
        // A path that names an existing file whichever write MSBuild keeps.
        (
            "$(Where)",
            "<PropertyGroup><Where>there.props</Where><Where Condition=\"UNDECIDED_TRUE\">there.props</Where></PropertyGroup>",
        ),
        (
            "$(Where)",
            "<PropertyGroup><Where Condition=\"UNDECIDED_TRUE\">there.props</Where></PropertyGroup>",
        ),
        (
            "$(Where)",
            "<PropertyGroup><Where Condition=\"UNDECIDED_TRUE\">missing.props</Where></PropertyGroup>",
        ),
        #[cfg(unix)]
        ("dangling.props", ""),
    ];
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(
        dir.join("there.props"),
        "<Project><PropertyGroup><Gamma>there</Gamma></PropertyGroup></Project>",
    )
    .unwrap();
    std::fs::write(dir.join("bad.props"), "<Project>").unwrap();
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    std::fs::write(dir.join("sub/x.props"), "<Project />").unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink("gone.props", dir.join("dangling.props")).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let names: Vec<String> = ["Alpha", "Beta", "Gamma"].map(String::from).to_vec();
    let (mut rejected, mut committed, mut certain) = (0usize, 0usize, 0usize);
    // The gate sits on the import, or on an `<ImportGroup>` around it, which
    // gates it as much.
    for (gate_template, in_group) in gates
        .iter()
        .flat_map(|gate| [(*gate, false), (*gate, true)])
    {
        for (project, before) in targets {
            let gate = gate_template
                .replace("UNDECIDED_TRUE", UNDECIDED_TRUE)
                .replace("UNDECIDED_FALSE", UNDECIDED_FALSE)
                .replace("{p}", project);
            let condition = if gate.is_empty() {
                String::new()
            } else {
                format!(" Condition=\"{gate}\"")
            };
            let before = before.replace("UNDECIDED_TRUE", UNDECIDED_TRUE);
            let import = if in_group {
                format!("<ImportGroup{condition}><Import Project=\"{project}\" /></ImportGroup>")
            } else {
                format!("<Import Project=\"{project}\"{condition} />")
            };
            let xml = format!(
                "<Project>\n  <PropertyGroup><Alpha>a</Alpha></PropertyGroup>\n  {before}\n  \
                 {import}\n  \
                 <PropertyGroup><Beta>b</Beta></PropertyGroup>\n</Project>\n"
            );
            std::fs::write(&project_path, &xml).unwrap();
            let parsed = parse_fsproj_with_imports(
                &xml,
                &project_path,
                &HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed");
            let ours: Vec<(&String, String)> = names
                .iter()
                .filter_map(|name| match parsed.property(name) {
                    // MSBuild reads an undefined name as empty.
                    PropertyRead::Unset => Some((name, String::new())),
                    read => read.value().map(|v| (name, v.to_owned())),
                })
                .collect();
            let claims_rejection =
                parsed.rejection.as_ref().map(|r| r.certainty) == Some(RejectionCertainty::Certain);
            certain += usize::from(claims_rejection);
            let Some(theirs) = oracle.project(&xml, &names, Some(&project_path), &[]) else {
                rejected += 1;
                assert!(
                    ours.is_empty(),
                    "certain-implies-exact violated: MSBuild rejects this project, but we \
                     committed {ours:?}\n--- xml ---\n{xml}"
                );
                continue;
            };
            assert!(
                !claims_rejection,
                "certain-implies-exact violated: we claim MSBuild rejects this project, and it \
                 evaluates it\n--- xml ---\n{xml}"
            );
            for (name, value) in &ours {
                committed += 1;
                assert_eq!(
                    Some(value),
                    theirs.get(*name),
                    "certain-implies-exact violated for {name}\n--- xml ---\n{xml}"
                );
            }
            // The other direction, for the gates that rule the import out
            // whenever it would fail: a gate decided false, and one that
            // requires the file, MSBuild's `Exists` of which is false where
            // nothing is. Withdrawing there is a decline MSBuild gives no cause
            // for.
            if PROBES_ITS_OWN_FILE_OR_IS_FALSE.contains(&gate_template) {
                assert_eq!(
                    parsed.rejection, None,
                    "MSBuild evaluates the project, and the gate rules the import out \
                     whenever it fails\n--- xml ---\n{xml}"
                );
            }
        }
    }
    eprintln!(
        "import failures: {rejected} rejected by MSBuild, {certain} of them claimed, \
         {committed} values committed"
    );
    // Anti-vacuity: both sides of the contract are exercised, and the claim.
    assert!(certain >= 10, "only {certain} rejections claimed");
    assert!(rejected >= 20, "only {rejected} rejected");
    assert!(committed >= 40, "only {committed} committed");
}

/// Conditions MSBuild throws on (#783), in every position a condition takes:
/// where MSBuild evaluates it, where it never does, and where only a gate the
/// walk cannot decide says which; each position also after content the walk
/// did not see, and inside an imported file. MSBuild rejects the whole project
/// when it evaluates one, so a project it rejects must commit nothing, one it
/// evaluates must commit only its values, and a rejection the walk claims
/// ([`RejectionCertainty::Certain`]) must be MSBuild's. Where nothing the walk
/// cannot decide stands between the condition and a position MSBuild never
/// evaluates, the walk must not withdraw either.
#[test]
fn illegal_conditions_reject_exactly_where_msbuild_evaluates_them() {
    const UNDECIDED_TRUE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";
    const UNDECIDED_FALSE: &str = "$([System.String]::IsNullOrWhiteSpace('no'))";
    // MSBuild's parser rejects each, whatever the values.
    let by_syntax = [
        "tr ue",
        // Whitespace alone is MSB4092, not the empty condition's `true`.
        " ",
        "'a' = 'a'",
        "$( Word ) == ''",
        "(true",
        "false and (tr ue)",
    ];
    // Ill typed on the values written: `Word` holds `abc` for certain,
    // `Maybe` under a gate the walk cannot decide.
    let by_value = ["1 &lt; abc", "$(Word) &gt; 1", "$(Word)", "$(Maybe) &gt; 1"];
    // Ill typed exactly where `Exists` resolves against the project's
    // directory, which holds `flag`, or exactly where it resolves against the
    // imported file's, which does not: each position's `Exists` directory,
    // graded in the imported context.
    let by_directory = [
        "Exists('flag') And 1 &lt; abc",
        "!Exists('flag') And 1 &lt; abc",
    ];
    let legal = [
        "'a' == 'a'",
        "'a' == 'b'",
        "false and 1 &lt; abc",
        UNDECIDED_TRUE,
    ];
    // `(template, never)`: `{c}` is the condition, and `never` says MSBuild
    // evaluates it in no build, the walk deciding every gate that says so.
    let positions: &[(&str, bool)] = &[
        (
            "<PropertyGroup><Alpha Condition=\"{c}\">x</Alpha></PropertyGroup>",
            false,
        ),
        (
            "<PropertyGroup Condition=\"{c}\"><Alpha>x</Alpha></PropertyGroup>",
            false,
        ),
        (
            "<PropertyGroup Condition=\"false\"><Alpha Condition=\"{c}\">x</Alpha></PropertyGroup>",
            true,
        ),
        (
            "<PropertyGroup Condition=\"UNDECIDED_TRUE\"><Alpha Condition=\"{c}\">x</Alpha></PropertyGroup>",
            false,
        ),
        (
            "<PropertyGroup Condition=\"UNDECIDED_FALSE\"><Alpha Condition=\"{c}\">x</Alpha></PropertyGroup>",
            false,
        ),
        (
            "<Import Project=\"there.props\" Condition=\"{c}\" />",
            false,
        ),
        (
            "<ImportGroup Condition=\"{c}\"><Import Project=\"there.props\" /></ImportGroup>",
            false,
        ),
        (
            "<ImportGroup Condition=\"false\"><Import Project=\"there.props\" Condition=\"{c}\" /></ImportGroup>",
            true,
        ),
        (
            "<ImportGroup Condition=\"UNDECIDED_TRUE\"><Import Project=\"there.props\" Condition=\"{c}\" /></ImportGroup>",
            false,
        ),
        (
            "<Choose><When Condition=\"{c}\"><PropertyGroup><Alpha>x</Alpha></PropertyGroup></When></Choose>",
            false,
        ),
        (
            "<Choose><When Condition=\"true\" /><When Condition=\"{c}\" /></Choose>",
            true,
        ),
        (
            "<Choose><When Condition=\"UNDECIDED_FALSE\" /><When Condition=\"{c}\" /></Choose>",
            false,
        ),
        (
            "<Choose><When Condition=\"false\"><PropertyGroup><Alpha Condition=\"{c}\">x</Alpha></PropertyGroup></When>\
             <Otherwise><PropertyGroup><Alpha>y</Alpha></PropertyGroup></Otherwise></Choose>",
            true,
        ),
        (
            "<Choose><When Condition=\"false\" /><Otherwise><PropertyGroup><Alpha Condition=\"{c}\">x</Alpha>\
             </PropertyGroup></Otherwise></Choose>",
            false,
        ),
        (
            "<Choose><When Condition=\"UNDECIDED_TRUE\" /><Otherwise><ItemGroup><I Include=\"x\" Condition=\"{c}\" />\
             </ItemGroup></Otherwise></Choose>",
            false,
        ),
        (
            "<ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup>",
            false,
        ),
        (
            "<ItemGroup Condition=\"false\"><I Include=\"x\" Condition=\"{c}\" /></ItemGroup>",
            false,
        ),
        (
            "<ItemGroup><I Include=\"x\" Condition=\"false\"><M Condition=\"{c}\">m</M></I></ItemGroup>",
            false,
        ),
        (
            "<ItemGroup><I Update=\"x\"><M Condition=\"{c}\">m</M></I></ItemGroup>",
            false,
        ),
        // Metadata evaluated item by item, for no item and for one.
        (
            "<ItemGroup><I Include=\"$(Missing)\"><O>%(Filename)</O><M Condition=\"{c}\">m</M></I></ItemGroup>",
            false,
        ),
        (
            "<ItemGroup><I Include=\"x\"><O>%(Filename)</O><M Condition=\"{c}\">m</M></I></ItemGroup>",
            false,
        ),
        ("<ItemDefinitionGroup Condition=\"{c}\" />", false),
        (
            "<ItemDefinitionGroup Condition=\"false\"><I Condition=\"{c}\" /></ItemDefinitionGroup>",
            true,
        ),
        (
            "<ItemDefinitionGroup><I Condition=\"false\"><M Condition=\"{c}\">m</M></I></ItemDefinitionGroup>",
            true,
        ),
        (
            "<ItemDefinitionGroup><I><M Condition=\"{c}\">m</M></I></ItemDefinitionGroup>",
            false,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Condition=\"{c}\" />",
            false,
        ),
        ("<Target Name=\"T\" Condition=\"{c}\" />", true),
        (
            "<Target Name=\"T\"><PropertyGroup><Alpha Condition=\"{c}\">x</Alpha></PropertyGroup></Target>",
            true,
        ),
    ];
    #[derive(Clone, Copy, PartialEq)]
    enum Context {
        Plain,
        AfterHiddenContent,
        Imported,
    }
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    // The imported context's file sits in `sub`, beside its own `there.props`,
    // and `flag` beside the project alone.
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    for there in [dir.join("there.props"), dir.join("sub/there.props")] {
        std::fs::write(
            there,
            "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
        )
        .unwrap();
    }
    std::fs::write(dir.join("flag"), "").unwrap();
    let project_path = dir.join("Demo.fsproj");
    let names: Vec<String> = ["Alpha", "Beta", "Gamma", "Delta"]
        .map(String::from)
        .to_vec();
    let (mut rejected, mut committed, mut certain, mut possible) = (0usize, 0, 0, 0);
    let conditions = by_syntax
        .iter()
        .chain(&by_value)
        .chain(&by_directory)
        .chain(&legal);
    for (condition, &(template, never)) in
        conditions.flat_map(|c| positions.iter().map(move |p| (c, p)))
    {
        for context in [
            Context::Plain,
            Context::AfterHiddenContent,
            Context::Imported,
        ] {
            let position = template
                .replace("{c}", condition)
                .replace("UNDECIDED_TRUE", UNDECIDED_TRUE)
                .replace("UNDECIDED_FALSE", UNDECIDED_FALSE);
            let mut inner = String::new();
            let (before, site) = match context {
                Context::Plain => (String::new(), position),
                Context::AfterHiddenContent => (
                    format!("<Import Project=\"there.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
                    position,
                ),
                Context::Imported => {
                    inner = format!("<Project>{position}</Project>");
                    std::fs::write(dir.join("sub/inner.props"), &inner).unwrap();
                    (
                        String::new(),
                        "<Import Project=\"sub/inner.props\" />".to_owned(),
                    )
                }
            };
            let xml = format!(
                "<Project>\n  <PropertyGroup><Word>abc</Word>\
                 <Maybe Condition=\"{UNDECIDED_TRUE}\">abc</Maybe><Beta>b</Beta></PropertyGroup>\n  \
                 {before}\n  {site}\n  <PropertyGroup><Gamma>g</Gamma></PropertyGroup>\n</Project>\n"
            );
            std::fs::write(&project_path, &xml).unwrap();
            let parsed = parse_fsproj_with_imports(
                &xml,
                &project_path,
                &HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed");
            let ours: Vec<(&String, String)> = names
                .iter()
                .filter_map(|name| match parsed.property(name) {
                    PropertyRead::Unset => Some((name, String::new())),
                    read => read.value().map(|v| (name, v.to_owned())),
                })
                .collect();
            let describe = || {
                format!(
                    "--- xml ---\n{xml}--- sub/inner.props ---\n{inner}\n{:#?}",
                    parsed.rejection
                )
            };
            match parsed.rejection.as_ref().map(|r| r.certainty) {
                Some(RejectionCertainty::Certain) => certain += 1,
                Some(RejectionCertainty::Possible) => possible += 1,
                None => {}
            }
            let Some(theirs) = oracle.project(&xml, &names, Some(&project_path), &[]) else {
                rejected += 1;
                assert!(
                    ours.is_empty(),
                    "certain-implies-exact violated: MSBuild rejects this project, but we \
                     committed {ours:?}\n{}",
                    describe()
                );
                continue;
            };
            assert_ne!(
                parsed.rejection.as_ref().map(|r| r.certainty),
                Some(RejectionCertainty::Certain),
                "certain-implies-exact violated: we claim MSBuild rejects this project, and \
                 it evaluates it\n{}",
                describe()
            );
            for (name, value) in &ours {
                committed += 1;
                assert_eq!(
                    Some(value),
                    theirs.get(*name),
                    "certain-implies-exact violated for {name}\n{}",
                    describe()
                );
            }
            // Nothing the walk cannot decide stands between the condition and
            // a position MSBuild never evaluates: no doubt to withdraw for.
            let decided = context != Context::AfterHiddenContent
                && !condition.contains("Maybe")
                && !condition.contains("IsNullOrWhiteSpace");
            if never && decided {
                assert_eq!(
                    parsed.rejection,
                    None,
                    "MSBuild never evaluates the condition\n{}",
                    describe()
                );
            }
        }
    }
    eprintln!(
        "illegal conditions: {rejected} rejected by MSBuild; we claim {certain} rejections \
         and allow {possible} more; {committed} values committed"
    );
    // Anti-vacuity: each side of the contract is exercised, the claim too.
    assert!(certain >= 150, "only {certain} rejections claimed");
    assert!(possible >= 50, "only {possible} rejections allowed");
    assert!(rejected >= 200, "only {rejected} rejected");
    assert!(committed >= 400, "only {committed} committed");
}

/// Constructs MSBuild refuses when it loads the file holding them (#888): a
/// reserved property name, an item without a usable `Include`, `Update` or
/// `Remove`, an `<Import>` with no `Project`, a malformed `<Choose>`, beside
/// shapes it loads. Each sits in every container that holds it: one MSBuild
/// evaluates, one under a false gate, one under a gate the walk cannot decide,
/// an unchosen `<When>`, a `<Target>`, and a `<ProjectExtensions>`, which
/// MSBuild does not parse. Each of those in the project, after content the
/// walk did not see, in a file the project imports, and in one it does not
/// import. MSBuild rejects the whole project for each refused construct in a
/// file it loads, so the property table is held to certain-implies-exact and a
/// claimed rejection to MSBuild's; where nothing the walk cannot decide is in
/// play and MSBuild evaluates the project, the walk must not withdraw.
#[test]
fn load_time_errors_reject_exactly_where_msbuild_loads_them() {
    const UNDECIDED_TRUE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";
    let properties = [
        "MSBuildProjectDirectory",
        "msbuildthisfile",
        "MSBuildToolsPath",
        "MSBuildNodeCount",
        "MSBuildDisableFeaturesFromVersion",
        "When",
        "Target",
        "ImportGroup",
        "MSBuildExtensionsPath",
        "choose",
        "Import",
        "Zeta",
    ]
    .map(|name| format!("<{name}>x</{name}>"));
    let items = [
        "<I Include=\"\" />",
        "<I Include=\"\" Condition=\"false\" />",
        "<I Remove=\"\" />",
        "<I Update=\"\" />",
        "<I />",
        "<I Include=\" \" />",
        "<I Include=\"$(Nothing)\" />",
        "<I Include=\"x\" />",
    ];
    let imports = [
        "<Import />",
        "<Import Project=\"\" />",
        "<Import Project=\"\" Condition=\"false\" />",
        "<Import Condition=\"false\" />",
        "<Import Project=\" \" />",
        "<Import Project=\"$(Nothing)\" Condition=\"false\" />",
        "<Import Project=\"there.props\" />",
    ];
    let chooses = [
        "<Choose />",
        "<Choose><Otherwise /></Choose>",
        "<Choose><When Condition=\"true\" /><Otherwise /><Otherwise /></Choose>",
        "<Choose><Otherwise /><When Condition=\"true\" /></Choose>",
        "<Choose><When /></Choose>",
        "<Choose><When Condition=\"true\"><Foo /></When></Choose>",
        "<Choose><When Condition=\"true\" /><When Condition=\" \" /></Choose>",
        "<Choose><When Condition=\" \" /></Choose>",
        // The loader's attribute and child rules, each side of each.
        "<Choose><When Condition=\"true\"><ItemDefinitionGroup /></When></Choose>",
        "<Choose><When Condition=\"true\" Foo=\"bar\" Label=\"l\" /></Choose>",
        "<Choose><When Condition=\"true\" /><Otherwise Label=\"l\" /></Choose>",
        "<Choose Label=\"l\"><When Condition=\"true\" /></Choose>",
        "<Choose><When Condition=\"true\"><Import Project=\"x\" /></When></Choose>",
        "<Choose><When Condition=\"true\"><When Condition=\"true\" /></When></Choose>",
        "<Choose><When Condition=\"true\" /><Foo /></Choose>",
        "<Choose><When Condition=\"true\" />text</Choose>",
        "<Choose><When Condition=\"true\">text</When></Choose>",
        "<Choose><When Condition=\"true\"><!-- c --></When></Choose>",
        "<Choose>&#160;<When Condition=\"true\">&#160;&#x2003;</When><Otherwise>&#xA0;</Otherwise></Choose>",
        "<Choose><When Condition=\"true\">&#233;</When></Choose>",
        "<Choose><When Condition=\"true\"><![CDATA[ ]]></When></Choose>",
        "<Choose><When Condition=\"true\"><![CDATA[x]]></When></Choose>",
        "<Choose><When Condition=\"true\">&#x200B;</When></Choose>",
        "<Choose>&#x85;&#9;&#x3000;<When Condition=\"true\" /></Choose>",
        "<Choose><When Condition=\"false\"><Choose><Otherwise /></Choose></When></Choose>",
        "<Choose><When Condition=\"false\"><Choose><When Condition=\"true\" Foo=\"bar\" /></Choose></When></Choose>",
        "<Choose><When Condition=\"true\"><PropertyGroup><Zeta>z</Zeta></PropertyGroup></When></Choose>",
    ];
    let property_containers = [
        "<PropertyGroup>{x}</PropertyGroup>",
        "<PropertyGroup Condition=\"false\">{x}</PropertyGroup>",
        "<PropertyGroup Condition=\"UNDECIDED_TRUE\">{x}</PropertyGroup>",
        "<Choose><When Condition=\"false\"><PropertyGroup>{x}</PropertyGroup></When></Choose>",
        "<Target Name=\"T\"><PropertyGroup>{x}</PropertyGroup></Target>",
        "<ProjectExtensions><PropertyGroup>{x}</PropertyGroup></ProjectExtensions>",
    ];
    let item_containers = [
        "<ItemGroup>{x}</ItemGroup>",
        "<ItemGroup Condition=\"false\">{x}</ItemGroup>",
        "<ItemGroup Condition=\"UNDECIDED_TRUE\">{x}</ItemGroup>",
        "<Choose><When Condition=\"false\"><ItemGroup>{x}</ItemGroup></When></Choose>",
        "<Target Name=\"T\"><ItemGroup>{x}</ItemGroup></Target>",
        "<ProjectExtensions><ItemGroup>{x}</ItemGroup></ProjectExtensions>",
    ];
    let import_containers = [
        "{x}",
        "<ImportGroup>{x}</ImportGroup>",
        "<ImportGroup Condition=\"false\">{x}</ImportGroup>",
        "<ImportGroup Condition=\"UNDECIDED_TRUE\">{x}</ImportGroup>",
        "<ProjectExtensions>{x}</ProjectExtensions>",
    ];
    let choose_containers = [
        "{x}",
        "<Choose><When Condition=\"false\">{x}</When></Choose>",
        "<Choose><When Condition=\"UNDECIDED_TRUE\">{x}</When></Choose>",
        "<ProjectExtensions>{x}</ProjectExtensions>",
    ];
    let sites: Vec<String> = [
        (&properties[..], &property_containers[..]),
        (&items.map(String::from)[..], &item_containers[..]),
        (&imports.map(String::from)[..], &import_containers[..]),
        (&chooses.map(String::from)[..], &choose_containers[..]),
    ]
    .into_iter()
    .flat_map(|(constructs, containers)| {
        constructs
            .iter()
            .flat_map(|c| containers.iter().map(move |k| k.replace("{x}", c)))
            .collect::<Vec<_>>()
    })
    .map(|site| site.replace("UNDECIDED_TRUE", UNDECIDED_TRUE))
    .collect();
    #[derive(Clone, Copy, PartialEq)]
    enum Context {
        Plain,
        AfterHiddenContent,
        Imported,
        NotImported,
    }
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    for there in [dir.join("there.props"), dir.join("sub/there.props")] {
        std::fs::write(
            there,
            "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
        )
        .unwrap();
    }
    let project_path = dir.join("Demo.fsproj");
    let names: Vec<String> = ["Alpha", "Beta", "Gamma", "Delta", "Zeta"]
        .map(String::from)
        .to_vec();
    let (mut rejected, mut committed, mut certain, mut evaluated) = (0usize, 0, 0, 0);
    for site in &sites {
        for context in [
            Context::Plain,
            Context::AfterHiddenContent,
            Context::Imported,
            Context::NotImported,
        ] {
            let mut inner = String::new();
            let (before, at) = match context {
                Context::Plain => (String::new(), site.clone()),
                Context::AfterHiddenContent => (
                    format!("<Import Project=\"there.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
                    site.clone(),
                ),
                Context::Imported | Context::NotImported => {
                    inner = format!("<Project>{site}</Project>");
                    std::fs::write(dir.join("sub/inner.props"), &inner).unwrap();
                    let gate = if context == Context::Imported {
                        "true"
                    } else {
                        "false"
                    };
                    (
                        String::new(),
                        format!("<Import Project=\"sub/inner.props\" Condition=\"{gate}\" />"),
                    )
                }
            };
            let xml = format!(
                "<Project>\n  <PropertyGroup><Beta>b</Beta></PropertyGroup>\n  {before}\n  \
                 {at}\n  <PropertyGroup><Gamma>g</Gamma></PropertyGroup>\n</Project>\n"
            );
            std::fs::write(&project_path, &xml).unwrap();
            let parsed = parse_fsproj_with_imports(
                &xml,
                &project_path,
                &HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed");
            let ours: Vec<(&String, String)> = names
                .iter()
                .filter_map(|name| match parsed.property(name) {
                    PropertyRead::Unset => Some((name, String::new())),
                    read => read.value().map(|v| (name, v.to_owned())),
                })
                .collect();
            let describe = || {
                format!(
                    "--- xml ---\n{xml}--- sub/inner.props ---\n{inner}\n{:#?}",
                    parsed.rejection
                )
            };
            let claimed =
                parsed.rejection.as_ref().map(|r| r.certainty) == Some(RejectionCertainty::Certain);
            certain += usize::from(claimed);
            let Some(theirs) = oracle.project(&xml, &names, Some(&project_path), &[]) else {
                rejected += 1;
                assert!(
                    ours.is_empty(),
                    "certain-implies-exact violated: MSBuild rejects this project, but we \
                     committed {ours:?}\n{}",
                    describe()
                );
                continue;
            };
            evaluated += 1;
            assert!(
                !claimed,
                "certain-implies-exact violated: we claim MSBuild rejects this project, and \
                 it evaluates it\n{}",
                describe()
            );
            for (name, value) in &ours {
                committed += 1;
                assert_eq!(
                    Some(value),
                    theirs.get(*name),
                    "certain-implies-exact violated for {name}\n{}",
                    describe()
                );
            }
            if context != Context::AfterHiddenContent && !site.contains("IsNullOrWhiteSpace") {
                assert_eq!(
                    parsed.rejection,
                    None,
                    "MSBuild evaluates the project, and nothing the walk cannot decide is in \
                     play\n{}",
                    describe()
                );
            }
        }
    }
    eprintln!(
        "load-time errors: {rejected} rejected by MSBuild, {certain} of them claimed; \
         {evaluated} evaluated, {committed} values committed"
    );
    // Anti-vacuity: each side of the contract is exercised, the claim too.
    assert!(certain >= 250, "only {certain} rejections claimed");
    assert!(rejected >= 250, "only {rejected} rejected");
    assert!(evaluated >= 300, "only {evaluated} evaluated");
    assert!(committed >= 1000, "only {committed} committed");
}

/// MSBuild's loader schema (#917), from tables rather than hand-picked
/// cases: every element `ProjectParser` parses, each given every attribute of
/// a table (each name any element takes, some in another case, and names none
/// does) and, separately, every child of a table (each element MSBuild knows,
/// property-, item- and metadata-like ones, text, CDATA, a comment and a
/// processing instruction). MSBuild refuses a file that breaks its loader, so
/// the property table is held to certain-implies-exact, a claimed rejection to
/// MSBuild's, and a project MSBuild evaluates must not be withdrawn.
#[test]
fn the_loader_schema_rejects_exactly_what_msbuild_refuses() {
    // `{a}` is where an attribute goes, `{c}` where a child goes.
    let subjects: &[(&str, &str)] = &[
        ("project", "{c}"),
        ("PropertyGroup", "<PropertyGroup{a}>{c}</PropertyGroup>"),
        (
            "property",
            "<PropertyGroup><Zeta{a}>z{c}</Zeta></PropertyGroup>",
        ),
        ("ItemGroup", "<ItemGroup{a}>{c}</ItemGroup>"),
        ("item", "<ItemGroup><I Include=\"x\"{a}>{c}</I></ItemGroup>"),
        (
            "item in a target",
            "<Target Name=\"T\"><ItemGroup><I Include=\"x\"{a}>{c}</I></ItemGroup></Target>",
        ),
        (
            "metadatum",
            "<ItemGroup><I Include=\"x\"><M{a}>m{c}</M></I></ItemGroup>",
        ),
        (
            "removing item",
            "<ItemGroup><I Remove=\"x\"{a}>{c}</I></ItemGroup>",
        ),
        (
            "updating item",
            "<ItemGroup><I Update=\"x\"{a}>{c}</I></ItemGroup>",
        ),
        // An item operation MSBuild builds in a group it evaluates, under a
        // false condition too, but not in a `<When>` it does not choose.
        (
            "removing item under a false group",
            "<ItemGroup Condition=\"false\"><I Remove=\"x\"{a}>{c}</I></ItemGroup>",
        ),
        (
            "removing item in a chosen When",
            "<Choose><When Condition=\"true\"><ItemGroup><I Remove=\"x\"{a}>{c}</I>\
             </ItemGroup></When></Choose>",
        ),
        (
            "removing item in an unchosen When",
            "<Choose><When Condition=\"false\"><ItemGroup><I Remove=\"x\"{a}>{c}</I>\
             </ItemGroup></When></Choose>",
        ),
        (
            "removing references",
            "<ItemGroup><I Remove=\"@(J); @(K)\"{a}>{c}</I></ItemGroup>",
        ),
        ("ImportGroup", "<ImportGroup{a}>{c}</ImportGroup>"),
        ("Import", "<Import Project=\"there.props\"{a}>{c}</Import>"),
        (
            "ItemDefinitionGroup",
            "<ItemDefinitionGroup{a}>{c}</ItemDefinitionGroup>",
        ),
        (
            "item definition",
            "<ItemDefinitionGroup><I{a}>{c}</I></ItemDefinitionGroup>",
        ),
        (
            "definition metadatum",
            "<ItemDefinitionGroup><I><M{a}>m{c}</M></I></ItemDefinitionGroup>",
        ),
        (
            "Choose",
            "<Choose{a}><When Condition=\"true\" />{c}</Choose>",
        ),
        (
            "When",
            "<Choose><When Condition=\"true\"{a}>{c}</When></Choose>",
        ),
        (
            "Otherwise",
            "<Choose><When Condition=\"false\" /><Otherwise{a}>{c}</Otherwise></Choose>",
        ),
        ("Target", "<Target Name=\"T\"{a}>{c}</Target>"),
        (
            "task",
            "<Target Name=\"T\"><Message Text=\"m\"{a}>{c}</Message></Target>",
        ),
        (
            "Output",
            "<Target Name=\"T\"><Message Text=\"m\"><Output TaskParameter=\"Text\" \
             PropertyName=\"Q\"{a}>{c}</Output></Message></Target>",
        ),
        (
            "OnError",
            "<Target Name=\"T\"><OnError ExecuteTargets=\"T\"{a}>{c}</OnError></Target>",
        ),
        (
            "UsingTask",
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\"{a}>{c}</UsingTask>",
        ),
        (
            "ParameterGroup",
            "<UsingTask TaskName=\"X\" TaskFactory=\"F\" AssemblyFile=\"y.dll\">\
             <ParameterGroup{a}>{c}</ParameterGroup></UsingTask>",
        ),
        (
            "parameter",
            "<UsingTask TaskName=\"X\" TaskFactory=\"F\" AssemblyFile=\"y.dll\">\
             <ParameterGroup><P{a}>{c}</P></ParameterGroup></UsingTask>",
        ),
        (
            "task body",
            "<UsingTask TaskName=\"X\" TaskFactory=\"F\" AssemblyFile=\"y.dll\">\
             <Task{a}>{c}</Task></UsingTask>",
        ),
        (
            "ProjectExtensions",
            "<ProjectExtensions{a}>{c}</ProjectExtensions>",
        ),
    ];
    let attributes: &[(&str, &str)] = &[
        ("Condition", "true"),
        ("Label", "l"),
        ("Include", "i"),
        ("Exclude", "e"),
        ("Remove", "r"),
        ("Update", "u"),
        ("KeepMetadata", "k"),
        ("RemoveMetadata", "k"),
        ("KeepDuplicates", "true"),
        ("MatchOnMetadata", "k"),
        ("MatchOnMetadata", "; "),
        ("MatchOnMetadataOptions", "CaseSensitive"),
        ("Project", "there.props"),
        ("Version", "1.0"),
        ("MinimumVersion", "1.0"),
        ("TaskName", "Y"),
        ("AssemblyFile", "z.dll"),
        ("AssemblyName", "Z"),
        ("TaskFactory", "F"),
        ("Architecture", "*"),
        ("Runtime", "*"),
        ("RequiredPlatform", "*"),
        ("RequiredRuntime", "4.0"),
        ("Override", "true"),
        ("Name", "N"),
        ("Inputs", "i"),
        ("Outputs", "o"),
        ("KeepDuplicateOutputs", "true"),
        ("DependsOnTargets", "T"),
        ("BeforeTargets", "T"),
        ("AfterTargets", "T"),
        ("Returns", "r"),
        ("ExecuteTargets", "T"),
        ("TaskParameter", "Text"),
        ("ItemName", "J"),
        ("PropertyName", "R"),
        ("ParameterType", "System.String"),
        ("Output", "true"),
        ("Required", "true"),
        ("Evaluate", "true"),
        ("ContinueOnError", "false"),
        ("MSBuildRuntime", "*"),
        ("MSBuildArchitecture", "*"),
        ("condition", "true"),
        ("include", "i"),
        ("continueOnError", "false"),
        ("Foo", "f"),
        ("_Foo", "f"),
        ("Foo-Bar", "f"),
        ("FullPath", "f"),
        ("filename", "f"),
        ("Choose", "c"),
        ("Import", "i"),
        (
            "xmlns",
            "http://schemas.microsoft.com/developer/msbuild/2003",
        ),
    ];
    let children = [
        "<PropertyGroup />",
        "<ItemGroup />",
        "<ImportGroup />",
        "<Import Project=\"there.props\" />",
        "<ItemDefinitionGroup />",
        "<Choose><When Condition=\"true\" /></Choose>",
        "<When Condition=\"true\" />",
        "<Otherwise />",
        "<Target Name=\"U\" />",
        "<UsingTask TaskName=\"Y\" AssemblyFile=\"z.dll\" />",
        "<ProjectExtensions />",
        "<OnError ExecuteTargets=\"T\" />",
        "<Output TaskParameter=\"Text\" PropertyName=\"R\" />",
        "<ParameterGroup />",
        "<Task />",
        "<Message Text=\"m\" />",
        "<Error Text=\"e\" />",
        "<Foo />",
        "<Zeta>z</Zeta>",
        "<J Include=\"j\" />",
        "<FullPath>f</FullPath>",
        "<x:Foo xmlns:x=\"urn:x\" />",
        "text",
        "&#160;",
        "<![CDATA[x]]>",
        "<!-- c -->",
        "<?pi x?>",
        "@(I)",
        "@<x />(I)",
        "@(I);<!-- c -->",
    ];
    let mut cases: Vec<String> = Vec::new();
    for (subject, template) in subjects {
        if template.contains("{a}") {
            for (name, value) in attributes {
                // A name the template writes already would be a duplicate
                // attribute, which is no XML at all.
                if template.contains(&format!(" {name}=")) {
                    continue;
                }
                let _ = subject;
                // Each name with its value, and empty, which a required or
                // exclusive attribute refuses.
                for value in [*value, ""] {
                    // MSBuild crashes on an `Include` beside an empty `Remove`
                    // (a null reference in `ParseProjectItemElement`, MSB1025
                    // from `dotnet msbuild`), which the oracle reports as an
                    // error, not a rejection; a unit test pins the rejection.
                    if *name == "Remove" && value.is_empty() && template.contains(" Include=") {
                        continue;
                    }
                    cases.push(
                        template
                            .replace("{a}", &format!(" {name}=\"{value}\""))
                            .replace("{c}", ""),
                    );
                }
            }
        }
        for child in children {
            cases.push(template.replace("{a}", "").replace("{c}", child));
        }
    }
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    for there in [dir.join("there.props"), dir.join("sub/there.props")] {
        std::fs::write(
            there,
            "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
        )
        .unwrap();
    }
    let project_path = dir.join("Demo.fsproj");
    let names: Vec<String> = ["Beta", "Gamma", "Delta"].map(String::from).to_vec();
    let (mut rejected, mut certain, mut possible, mut evaluated) = (0usize, 0, 0, 0);
    let mut failures: Vec<String> = Vec::new();
    // Each case in the project, and in a file it imports.
    for (site, imported) in cases.iter().flat_map(|site| [(site, false), (site, true)]) {
        let at = if imported {
            std::fs::write(
                dir.join("sub/inner.props"),
                format!("<Project>{site}</Project>"),
            )
            .unwrap();
            "<Import Project=\"sub/inner.props\" />"
        } else {
            site.as_str()
        };
        let site = format!("{}{site}", if imported { "(imported) " } else { "" });
        let xml = format!(
            "<Project>\n  <PropertyGroup><Beta>b</Beta></PropertyGroup>\n  {at}\n  \
             <PropertyGroup><Gamma>g</Gamma></PropertyGroup>\n</Project>\n"
        );
        std::fs::write(&project_path, &xml).unwrap();
        let parsed = parse_fsproj_with_imports(
            &xml,
            &project_path,
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed");
        let ours: Vec<(&String, String)> = names
            .iter()
            .filter_map(|name| match parsed.property(name) {
                PropertyRead::Unset => Some((name, String::new())),
                read => read.value().map(|v| (name, v.to_owned())),
            })
            .collect();
        let claimed =
            parsed.rejection.as_ref().map(|r| r.certainty) == Some(RejectionCertainty::Certain);
        match parsed.rejection.as_ref().map(|r| r.certainty) {
            Some(RejectionCertainty::Certain) => certain += 1,
            Some(RejectionCertainty::Possible) => possible += 1,
            None => {}
        }
        let verdict = format!(
            "{:?}",
            parsed.rejection.as_ref().map(|r| (&r.certainty, &r.cause))
        );
        let Some(theirs) = oracle.project(&xml, &names, Some(&project_path), &[]) else {
            rejected += 1;
            if !ours.is_empty() {
                failures.push(format!("MSBuild rejects, we committed {ours:?}: {site}"));
            }
            continue;
        };
        evaluated += 1;
        if claimed {
            failures.push(format!("MSBuild evaluates, we claim {verdict}: {site}"));
        } else if parsed.rejection.is_some() {
            failures.push(format!("MSBuild evaluates, we withdraw {verdict}: {site}"));
        }
        for (name, value) in &ours {
            if Some(value) != theirs.get(*name) {
                failures.push(format!(
                    "{name}: ours {value:?}, theirs {:?}: {site}",
                    theirs.get(*name)
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} cases disagree:\n{}",
        failures.len(),
        2 * cases.len(),
        failures.join("\n")
    );
    eprintln!(
        "loader schema: {} cases; {rejected} rejected by MSBuild, {certain} claimed, \
         {possible} more withdrawn; {evaluated} evaluated",
        2 * cases.len()
    );
    // Anti-vacuity: both verdicts occur in numbers, and the claim covers most
    // of MSBuild's refusals.
    assert!(rejected >= 4000, "only {rejected} rejected");
    assert!(evaluated >= 1800, "only {evaluated} evaluated");
    assert!(
        certain * 20 >= rejected * 19,
        "only {certain} of {rejected} claimed"
    );
}
