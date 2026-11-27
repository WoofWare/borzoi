//! An evaluation MSBuild may reject (#820, #845): an `<Import>` the build may
//! make names no file it can load, so MSBuild fails the whole project
//! (MSB4019, MSB4025, MSB4020/MSB4035). The walk keeps going, for the read set
//! and the diagnostics, and publishes nothing as the build's: every property
//! read is inexact and every item facet uncertain
//! ([`ParsedProject::rejection`]). Each MSBuild verdict below was read off the
//! import-graph and property-table differentials' oracle, which grade the
//! same shapes.

use super::*;
use tempfile::TempDir;

/// A condition conjunct MSBuild finds true and the walk cannot evaluate.
const UNDECIDED_TRUE: &str = "'É' == 'é'";

/// Whether the walk published nothing as the build's, for a rejection it may
/// make: the facets and reads a rejected evaluation withdraws.
fn assert_withdrawn(parsed: &ParsedProject, names: &[&str]) {
    assert_withdrawn_as(parsed, names, RejectionCertainty::Possible);
}

/// [`assert_withdrawn`] for a rejection the walk claims MSBuild makes.
fn assert_rejected(parsed: &ParsedProject, names: &[&str]) {
    assert_withdrawn_as(parsed, names, RejectionCertainty::Certain);
}

/// [`assert_withdrawn`], the rejection held as `certainty`.
fn assert_withdrawn_as(parsed: &ParsedProject, names: &[&str], certainty: RejectionCertainty) {
    let rejection = parsed
        .rejection
        .as_ref()
        .unwrap_or_else(|| panic!("no rejection: {:#?}", parsed.diagnostics));
    assert_eq!(rejection.certainty, certainty, "{rejection:#?}");
    for name in names {
        let read = parsed.property(name);
        assert!(!read.is_exact(), "{name} reads {read:?}");
    }
    assert!(!parsed.property("NeverWritten").is_exact());
    assert!(parsed.items_uncertain);
    assert!(parsed.define_constants_uncertain);
    assert!(parsed.project_references_uncertain);
    assert!(parsed.package_references_uncertain);
    assert_eq!(parsed.target_name, ItemMetadataValue::Unknown);
    assert!(parsed.hidden_content.is_some());
    let may_be_rejected = |kind: &DiagnosticKind| match certainty {
        RejectionCertainty::Possible => matches!(kind, DiagnosticKind::MayBeRejected { .. }),
        RejectionCertainty::Certain => matches!(kind, DiagnosticKind::Rejected { .. }),
    };
    assert!(parsed.compile_item_uncertainties.iter().any(
        |c| matches!(&c.kind, CompileItemUncertaintyCauseKind::Diagnostic(k) if may_be_rejected(k))
    ));
    assert!(
        parsed
            .define_constants_uncertainties
            .iter()
            .any(|c| matches!(&c.kind, DefineConstantsUncertaintyCauseKind::Diagnostic(k) if may_be_rejected(k)))
    );
    assert!(
        parsed
            .package_reference_uncertainties
            .iter()
            .any(|c| matches!(&c.kind, PackageReferenceUncertaintyCauseKind::Diagnostic(k) if may_be_rejected(k)))
    );
    assert!(parsed.diagnostics.iter().any(|d| may_be_rejected(&d.kind)));
}

/// `proj/p.fsproj` with `body`, after writing `files` beside it.
fn project(tmp: &TempDir, body: &str, files: &[(&str, &str)]) -> PathBuf {
    for (name, text) in files {
        write_at(tmp.path(), name, text);
    }
    write_at(
        tmp.path(),
        "proj/p.fsproj",
        &format!(
            "<Project>\n  <PropertyGroup><Before>1</Before></PropertyGroup>\n{body}\n  \
             <PropertyGroup><After>1</After></PropertyGroup>\n  \
             <ItemGroup><Compile Include=\"body.fs\" /></ItemGroup>\n</Project>\n"
        ),
    )
}

#[test]
fn an_undecided_import_of_a_missing_file_may_be_rejected() {
    // #820's reproduction: MSBuild takes the gate and fails (MSB4019).
    let tmp = TempDir::new().unwrap();
    let props = format!(
        "<Project>\n  <Import Project=\"$(MSBuildProjectDirectory)/missing.props\" \
         Condition=\"{UNDECIDED_TRUE} Or Exists('$(MSBuildProjectDirectory)/missing.props')\" />\n  \
         <PropertyGroup><After>1</After></PropertyGroup>\n</Project>\n"
    );
    let (sdk_dir, props, targets) =
        write_synthetic_sdk(tmp.path(), "Custom", &props, "<Project />");
    let project_path = write_at(
        tmp.path(),
        "proj/p.fsproj",
        "<Project Sdk=\"Custom\">\n  <ItemGroup><Compile Include=\"body.fs\" /></ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk(&project_path, |name| {
        if name == "Custom" {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert_withdrawn(&parsed, &["After"]);
}

#[test]
fn an_undecided_import_that_requires_its_own_file_is_not_rejected() {
    // The gate is false whenever the file is missing, so MSBuild never
    // attempts it.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <Import Project=\"missing.props\" Condition=\"{UNDECIDED_TRUE} And Exists('missing.props')\" />"
        ),
        &[],
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
    assert_eq!(parsed.property("After"), PropertyRead::Value("1".into()));
}

#[test]
fn an_undecided_import_of_a_file_that_loads_is_not_rejected() {
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"there.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[("proj/there.props", "<Project />")],
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
}

#[test]
fn an_undecided_import_of_a_wildcard_may_be_rejected() {
    // Under a gate the walk cannot decide, it does not settle what a wildcard
    // matches, nor whether each match loads (matching by UTF-16 unit, a match
    // a link names, a spelling MSBuild collapses), so even one matching nothing
    // may be rejected.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"none/*.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_undecided_import_of_a_missing_file_skipped_by_the_walk_may_be_rejected() {
    // The walk skips an import whose gate it cannot evaluate; MSBuild may
    // take it.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"missing.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_undecided_import_of_a_directory_may_be_rejected() {
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"sub\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[("proj/sub/x.props", "<Project />")],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_undecided_import_with_an_empty_path_may_be_rejected() {
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"$(Nothing)\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_undecided_import_of_an_untrusted_path_may_be_rejected() {
    // `Where` is written under a gate the walk cannot decide, so the path
    // MSBuild imports may be another, or none.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup><Where Condition=\"{UNDECIDED_TRUE}\">there.props</Where></PropertyGroup>\n  \
             <Import Project=\"$(Where)\" Condition=\"{UNDECIDED_TRUE}\" />"
        ),
        &[("proj/there.props", "<Project />")],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn a_decided_import_of_a_missing_file_is_rejected() {
    // #845: MSB4019. What the walk bound before the import is no more the
    // build's than what it bound after.
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, "  <Import Project=\"missing.props\" />", &[]);
    assert_rejected(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn a_decided_import_of_an_untrusted_path_may_be_rejected() {
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup><Where Condition=\"{UNDECIDED_TRUE}\">there.props</Where></PropertyGroup>\n  \
             <Import Project=\"$(Where)\" />"
        ),
        &[("proj/there.props", "<Project />")],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn a_decided_import_of_malformed_xml_may_be_rejected() {
    // MSB4025.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <Import Project=\"bad.props\" />",
        &[("proj/bad.props", "<Project>")],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[cfg(unix)]
#[test]
fn a_decided_import_of_a_dangling_link_is_rejected() {
    // #845's reproduction, imported unconditionally: MSB4019.
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, "  <Import Project=\"alias.targets\" />", &[]);
    std::os::unix::fs::symlink(
        "../Directory.Build.targets",
        tmp.path().join("proj/alias.targets"),
    )
    .unwrap();
    assert_rejected(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_import_with_an_empty_project_is_rejected() {
    // MSB4035 / MSB4020.
    for import in [
        "<Import Project=\"\" />",
        "<Import Project=\"$(Nothing)\" />",
        "<Import />",
    ] {
        let tmp = TempDir::new().unwrap();
        let project_path = project(&tmp, &format!("  {import}"), &[]);
        assert_rejected(&parse_file(&project_path), &["Before", "After"]);
    }
}

#[test]
fn an_sdk_import_of_a_missing_file_is_rejected() {
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) =
        write_synthetic_sdk(tmp.path(), "S", "<Project />", "<Project />");
    let project_path = project(
        &tmp,
        "  <Import Sdk=\"S\" Project=\"missing.props\" />",
        &[],
    );
    let parsed = parse_file_with_sdk(&project_path, |name| {
        if name == "S" {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert_rejected(&parsed, &["Before", "After"]);
}

#[test]
fn an_undecided_directory_build_point_of_a_missing_file_may_be_rejected() {
    // The point's `Exists` is a disjunct: MSBuild imports the path whether
    // or not the file exists, and with no `Directory.Build.props` anywhere
    // it names nothing.
    let tmp = TempDir::new().unwrap();
    let block = COMMON_PROPS_BLOCK.replace(
        "exists('$(DirectoryBuildPropsPath)')\"/>",
        &format!("({UNDECIDED_TRUE} Or exists('$(DirectoryBuildPropsPath)'))\"/>"),
    );
    assert_ne!(block, COMMON_PROPS_BLOCK, "the point's condition moved");
    let (sdk_dir, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "S",
        &format!(
            "<Project>\n{block}  <PropertyGroup><After>1</After></PropertyGroup>\n</Project>\n"
        ),
        "<Project />",
    );
    let project_path = write_at(
        tmp.path(),
        "proj/p.fsproj",
        "<Project Sdk=\"S\">\n  <ItemGroup><Compile Include=\"body.fs\" /></ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk(&project_path, |name| {
        if name == "S" {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert_withdrawn(&parsed, &["After"]);
}

#[test]
fn an_undecided_directory_build_point_of_a_file_that_loads_is_not_rejected() {
    let tmp = TempDir::new().unwrap();
    let block = COMMON_PROPS_BLOCK.replace(
        "exists('$(DirectoryBuildPropsPath)')\"/>",
        &format!("({UNDECIDED_TRUE} Or exists('$(DirectoryBuildPropsPath)'))\"/>"),
    );
    let (sdk_dir, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "S",
        &format!("<Project>\n{block}</Project>\n"),
        "<Project />",
    );
    write_at(tmp.path(), "Directory.Build.props", "<Project />");
    let project_path = write_at(tmp.path(), "proj/p.fsproj", "<Project Sdk=\"S\" />\n");
    let parsed = parse_file_with_sdk(&project_path, |name| {
        if name == "S" {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
}

#[test]
fn an_undecided_import_msbuild_skips_as_a_duplicate_is_not_rejected() {
    // MSBuild compares import paths ignoring case, so it skips the second
    // import without loading it, whether or not `THERE.props` exists.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <Import Project=\"there.props\" />\n  \
             <Import Project=\"THERE.props\" Condition=\"{UNDECIDED_TRUE}\" />"
        ),
        &[("proj/there.props", "<Project />")],
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
}

#[test]
fn an_undecided_sdk_import_of_a_property_made_rooted_path_is_judged_under_the_sdk() {
    // `Path.Combine` runs on the attribute as written, so a path a property
    // makes rooted is appended to the SDK's directory, where `x.props` is.
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) =
        write_synthetic_sdk(tmp.path(), "S", "<Project />", "<Project />");
    write_at(&sdk_dir, "x.props", "<Project />");
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup><P>/x.props</P></PropertyGroup>\n  \
             <Import Sdk=\"S\" Project=\"$(P)\" Condition=\"{UNDECIDED_TRUE}\" />"
        ),
        &[],
    );
    let resolver = |name: &str| {
        if name == "S" {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    let parsed = parse_file_with_sdk(&project_path, resolver);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
    // The same import written rooted names `/x.props` itself, which is
    // missing.
    let project_path = project(
        &tmp,
        &format!("  <Import Sdk=\"S\" Project=\"/x.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[],
    );
    assert_withdrawn(
        &parse_file_with_sdk(&project_path, resolver),
        &["Before", "After"],
    );
}

#[test]
fn an_undecided_sdk_import_under_a_relative_root_is_judged_where_the_walk_follows_it() {
    // A resolver may answer with a relative root; `NormalizePath` makes it
    // absolute against the working directory before collapsing `..`, so a
    // leading `..` still climbs.
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) =
        write_synthetic_sdk(tmp.path(), "S", "<Project />", "<Project />");
    write_at(&sdk_dir, "Extra.props", "<Project />");
    let cwd = std::path::absolute(".").unwrap();
    let mut relative = PathBuf::new();
    for _ in cwd.components().skip(1) {
        relative.push("..");
    }
    let relative_root = relative.join(canon(&sdk_dir).strip_prefix("/").unwrap());
    let project_path = project(
        &tmp,
        &format!("  <Import Sdk=\"S\" Project=\"Extra.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[],
    );
    let parsed = parse_file_with_sdk(&project_path, |name| {
        if name == "S" {
            Ok(SdkPaths {
                root: relative_root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
}

#[test]
fn a_decided_sdk_import_of_a_property_made_rooted_path_is_rejected() {
    // `Path.Combine` runs on the attribute as written, so the rooted value is
    // appended to the SDK's directory, which holds no such file: MSB4019,
    // though the file the value names exists.
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) =
        write_synthetic_sdk(tmp.path(), "S", "<Project />", "<Project />");
    let elsewhere = write_at(tmp.path(), "elsewhere/x.props", "<Project />");
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup><P>{}</P></PropertyGroup>\n  <Import Sdk=\"S\" Project=\"$(P)\" />",
            elsewhere.display()
        ),
        &[],
    );
    let parsed = parse_file_with_sdk(&project_path, |name| {
        if name == "S" {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert_rejected(&parsed, &["Before", "After"]);
}

#[test]
fn a_missing_import_after_content_the_walk_did_not_see_may_be_rejected() {
    // The undecided import before it may have imported `missing.props`
    // already, which would make this import a duplicate MSBuild skips.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <Import Project=\"there.props\" Condition=\"{UNDECIDED_TRUE}\" />\n  \
             <Import Project=\"missing.props\" />"
        ),
        &[("proj/there.props", "<Project />")],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn a_missing_import_inside_an_import_of_an_uncertain_path_may_be_rejected() {
    // `Where` may name another file in the build, which need not import
    // `missing.props`.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup><Where>there.props</Where>\
             <Where Condition=\"{UNDECIDED_TRUE}\">there.props</Where></PropertyGroup>\n  \
             <Import Project=\"$(Where)\" />"
        ),
        &[(
            "proj/there.props",
            "<Project><Import Project=\"missing.props\" /></Project>",
        )],
    );
    let parsed = parse_file(&project_path);
    assert_withdrawn(&parsed, &["Before", "After"]);
}

#[test]
fn a_decided_import_of_a_directory_may_be_rejected() {
    // The walk reads a directory as an I/O failure, which it does not claim.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <Import Project=\"sub\" />",
        &[("proj/sub/x.props", "<Project />")],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

/// [`project`] evaluated by both walkers: with imports, and the pure one.
fn both_walkers(body: &str) -> [ParsedProject; 2] {
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, body, &[]);
    let text = host_fs::read_to_string(&project_path).unwrap();
    let pure = parse_fsproj(
        &crate::ProjectFile::buffer(&project_path, &text)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &HashMap::new(),
    )
    .unwrap();
    [parse_file(&project_path), pure]
}

#[test]
fn an_illegal_condition_msbuild_evaluates_is_rejected() {
    // Each pinned in `tests/condition_diff.rs`'s
    // `where_msbuild_evaluates_a_condition`.
    for body in [
        // A syntax error, however the rest decides.
        "<PropertyGroup><R Condition=\"tr ue\">x</R></PropertyGroup>",
        "<PropertyGroup><R Condition=\"false and (tr ue)\">x</R></PropertyGroup>",
        "<PropertyGroup Condition=\"tr ue\"><R>x</R></PropertyGroup>",
        // MSB4086 on values the walk holds for certain.
        "<PropertyGroup><R Condition=\"1 &lt; abc\">x</R></PropertyGroup>",
        "<PropertyGroup><W>abc</W><R Condition=\"$(W) &gt; 1\">x</R></PropertyGroup>",
        // A scalar outside the boolean vocabulary.
        "<PropertyGroup><R Condition=\"$(Unset)\">x</R></PropertyGroup>",
        // An item's condition, whatever its group's holds.
        "<ItemGroup><I Include=\"x\" Condition=\"tr ue\" /></ItemGroup>",
        "<ItemGroup Condition=\"false\"><I Include=\"x\" Condition=\"1 &lt; abc\" /></ItemGroup>",
        "<ItemGroup Condition=\"false\"><I Remove=\"x\" Condition=\"tr ue\" /></ItemGroup>",
        // An `Include` item's metadata, whatever the item's holds.
        "<ItemGroup><I Include=\"x\" Condition=\"false\"><M Condition=\"tr ue\">m</M></I></ItemGroup>",
        "<ItemGroup Condition=\"false\"><I Include=\"x\"><M Condition=\"1 &lt; abc\">m</M></I></ItemGroup>",
        "<ItemDefinitionGroup Condition=\"tr ue\" />",
        "<ItemDefinitionGroup><I Condition=\"tr ue\" /></ItemDefinitionGroup>",
        "<ItemDefinitionGroup><I><M Condition=\"1 &lt; abc\">m</M></I></ItemDefinitionGroup>",
        "<Choose><When Condition=\"tr ue\"><PropertyGroup><R>x</R></PropertyGroup></When></Choose>",
        "<Choose><When Condition=\"false\" /><When Condition=\"tr ue\" /></Choose>",
        "<Choose><When Condition=\"true\"><ItemGroup><I Include=\"x\" Condition=\"tr ue\" /></ItemGroup></When></Choose>",
        "<Choose><When Condition=\"false\" /><Otherwise><PropertyGroup><R Condition=\"tr ue\">x</R></PropertyGroup></Otherwise></Choose>",
        "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Condition=\"1 &lt; abc\" />",
        "<Import Project=\"nope.props\" Condition=\"tr ue\" />",
        "<ImportGroup Condition=\"tr ue\" />",
        "<ImportGroup><Import Project=\"nope.props\" Condition=\"tr ue\" /></ImportGroup>",
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            let rejection = parsed
                .rejection
                .as_ref()
                .unwrap_or_else(|| panic!("no rejection for {body}: {:#?}", parsed.diagnostics));
            assert!(
                matches!(rejection.cause, RejectionCause::IllegalCondition { .. }),
                "{body}: {rejection:#?}"
            );
            assert_rejected(&parsed, &["Before", "After"]);
        }
    }
}

/// A property function MSBuild throws on (MSB4184) on values the walk is
/// certain of, wherever MSBuild evaluates it: a condition, a property body,
/// an item's `Include` or metadata (#1009). Each pinned in
/// `tests/fsproj_property_table_diff.rs`'s
/// `property_functions_msbuild_throws_on_reject_where_it_evaluates_them` or
/// `tests/condition_diff.rs`'s corners.
#[test]
fn a_property_function_msbuild_throws_on_is_rejected() {
    for body in [
        "<PropertyGroup><P>a;b</P><R Condition=\"'$(P.Split(`;`)[3])' == ''\">x</R></PropertyGroup>",
        "<PropertyGroup><P>abc</P><R Condition=\"'$(P[5])' == '' And false\">x</R></PropertyGroup>",
        "<PropertyGroup><R Condition=\"$([MSBuild]::VersionGreaterThan('abc', '1.0'))\">x</R></PropertyGroup>",
        "<PropertyGroup><P>a;b</P><R>$(P.Split(';')[3])</R></PropertyGroup>",
        "<PropertyGroup><Len>10x</Len><R>$(Len.Split('8')[1])</R></PropertyGroup>",
        "<PropertyGroup><P>a;b</P><R>$([MSBuild]::VersionLessThan('$(P)', '1.0'))</R></PropertyGroup>",
        "<PropertyGroup><P>a;b</P></PropertyGroup><ItemGroup><I Include=\"$(P.Split(';')[3])\" /></ItemGroup>",
        "<PropertyGroup><P>a;b</P></PropertyGroup><ItemGroup><I Include=\"x\"><M>$(P[9])</M></I></ItemGroup>",
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_rejected(&parsed, &["Before", "After"]);
        }
    }
}

/// What the walk reads a property function's inputs as must be MSBuild's
/// before a throw on them is a claim, and the text must be one MSBuild
/// expands: each of these evaluates in MSBuild (`tests/condition_diff.rs`'s
/// `where_msbuild_evaluates_a_text` and corners).
#[test]
fn a_throw_on_text_msbuild_reads_otherwise_is_none() {
    for body in [
        // Version arguments in either other string delimiter.
        "<PropertyGroup><R Condition=\"$([MSBuild]::VersionEquals(&quot;1.2&quot;,&quot;1.2&quot;))\">x</R></PropertyGroup>",
        "<PropertyGroup><R Condition=\"$([MSBuild]::VersionEquals(`1.2`,`1.2`))\">x</R></PropertyGroup>",
        // An item definition's metadata MSBuild substitutes first.
        "<ItemDefinitionGroup><I><V>1.0</V><M>$([MSBuild]::VersionEquals('%(V)','1.0'))</M></I></ItemDefinitionGroup>",
        "<ItemGroup><I Include=\"x\" V=\"1.0\" M=\"$([MSBuild]::VersionEquals('%(V)','1.0'))\" /></ItemGroup>",
        // A label MSBuild does not expand.
        "<PropertyGroup><P>abc</P></PropertyGroup><UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Label=\"$(P[9])\" />",
        "<PropertyGroup><P>abc</P></PropertyGroup><ItemGroup><I Include=\"x\" Label=\"$(P[9])\" /></ItemGroup>",
        // A literal tab in an attribute, which MSBuild reads as itself.
        "<PropertyGroup><P>a&#x9;b</P></PropertyGroup><ItemGroup><I Include=\"$(P.Split('\t')[1])\" /></ItemGroup>",
        // A boolean the walk does not compute coerces without throwing.
        "<PropertyGroup><R Condition=\"$([System.String]::IsNullOrWhiteSpace('\u{a0}'))\">x</R></PropertyGroup>",
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
    // An `Update`'s metadata is expanded only where the update applies.
    let body = "<PropertyGroup><P>abc</P></PropertyGroup><ItemGroup><I Update=\"nothere\" M=\"$(P[9])\" /></ItemGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_ne!(
            parsed.rejection.as_ref().map(|r| r.certainty),
            Some(RejectionCertainty::Certain),
            "{body}"
        );
    }
}

/// A throw on certain values beside an operand the walk cannot judge is
/// still MSBuild's: one on a value the walk holds none of (`A`, refused), or
/// one returning a boolean the walk does not compute, does not hide a later
/// expression that throws whatever it holds.
#[test]
fn a_throw_beside_an_unjudged_expression_is_judged() {
    let refused = "<A>$(P.Substring(0))</A>";
    for body in [
        format!("<PropertyGroup><P>abc</P>{refused}<R>$(A[0])$(P[9])</R></PropertyGroup>"),
        format!(
            "<PropertyGroup><P>abc</P>{refused}<R Condition=\"'$(A)$(P[9])' == ''\">x</R></PropertyGroup>"
        ),
        "<PropertyGroup><P>abc</P><R Condition=\"'$([System.String]::IsNullOrWhiteSpace(&quot;É&quot;))' == '$(P[9])'\">x</R></PropertyGroup>"
            .to_owned(),
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn_as(
                &parsed,
                &["Before", "After"],
                parsed
                    .rejection
                    .as_ref()
                    .map_or(RejectionCertainty::Possible, |r| r.certainty),
            );
        }
    }
}

/// An operand the walk does not model, reached on values it is certain of,
/// may throw (`'abc'.Substring(5)` does, MSB4184): a Possible site, before
/// the operand that decides the condition and not after it. One MSBuild
/// evaluates without throwing, to a boolean the walk cannot compute, is none.
#[test]
fn an_unmodelled_operand_reached_on_certain_values_may_reject() {
    for c in [
        "'$(P.Substring(5))' == '' And false",
        "!('$(P.Substring(5))' == '') Or true",
        "'$(P.Substring(5))' == '' Or true",
    ] {
        let body = format!("<PropertyGroup><P>abc</P><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn(&parsed, &["Before", "After"]);
        }
    }
    for c in [
        "false And '$(P.Substring(5))' == ''",
        "true Or '$(P.Substring(5))' == ''",
        "'É' == 'é'",
        "'É' == 'é' And '$(P)' == 'abc'",
    ] {
        let body = format!("<PropertyGroup><P>abc</P><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
}

/// A property function that fails on a value the walk holds none of, and
/// MSBuild may hold another of (a write the walk refused to compute, a
/// reserved name it does not seed), is no site: the judgement over the values
/// a name may hold (#1009's second stage). The SDK's own
/// `VersionGreaterThanOrEquals($(MSBuildVersion), '17.0')` is of it.
#[test]
fn a_throw_on_a_value_the_walk_holds_none_of_is_not_yet_judged() {
    for body in [
        "<PropertyGroup><R Condition=\"$([MSBuild]::VersionGreaterThanOrEquals($(MSBuildVersion), '17.0'))\">x</R></PropertyGroup>",
        "<PropertyGroup><Q>$(Configuration.Substring(0,1))</Q><R>$([MSBuild]::VersionLessThan('$(Q)', '18.9'))</R></PropertyGroup>",
        "<PropertyGroup><Q>$(Configuration.Substring(0,1))</Q><R Condition=\"'$(Q.Split(`;`)[3])' == ''\">x</R></PropertyGroup>",
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
}

#[test]
fn an_operand_msbuild_never_reaches_is_no_cause_to_withdraw() {
    // MSBuild stops at the operand that decides the condition, so it never
    // reads `X`, which the walk is not certain of, in any of these.
    for position in [
        "<PropertyGroup><R Condition=\"{c}\">x</R></PropertyGroup>",
        "<PropertyGroup Condition=\"{c}\"><R>x</R></PropertyGroup>",
        "<ImportGroup Condition=\"{c}\"><Import Project=\"nope.props\" /></ImportGroup>",
        "<Import Project=\"nope.props\" Condition=\"{c}\" />",
        "<ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup>",
        "<ItemGroup><I Include=\"x\" Condition=\"{c}\" /></ItemGroup>",
        "<Choose><When Condition=\"{c}\" /></Choose>",
    ] {
        for c in ["false And $(X) &gt; 2", "!(true Or $(X) &gt; 2)"] {
            let body = format!(
                "<PropertyGroup><X>1</X><X Condition=\"{UNDECIDED_TRUE}\">abc</X></PropertyGroup>{}",
                position.replace("{c}", c)
            );
            for parsed in both_walkers(&format!("  {body}")) {
                assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
            }
        }
    }
}

#[test]
fn an_illegal_condition_msbuild_never_evaluates_is_not_rejected() {
    for body in [
        "<PropertyGroup><R Condition=\"false and 1 &lt; abc\">x</R></PropertyGroup>",
        "<PropertyGroup Condition=\"false\"><R Condition=\"tr ue\">x</R></PropertyGroup>",
        "<PropertyGroup Condition=\"false\"><R Condition=\"1 &lt; abc\">x</R></PropertyGroup>",
        "<ItemGroup Condition=\"false and 1 &lt; abc\"><I Include=\"x\" /></ItemGroup>",
        "<ItemDefinitionGroup Condition=\"false\"><I><M Condition=\"tr ue\">m</M></I></ItemDefinitionGroup>",
        "<ItemDefinitionGroup><I Condition=\"false\"><M Condition=\"tr ue\">m</M></I></ItemDefinitionGroup>",
        "<ImportGroup Condition=\"false\"><Import Project=\"nope.props\" Condition=\"tr ue\" /></ImportGroup>",
        "<Choose><When Condition=\"true\" /><When Condition=\"tr ue\" /></Choose>",
        "<Choose><When Condition=\"false\"><ItemGroup><I Include=\"x\" Condition=\"tr ue\" /></ItemGroup></When></Choose>",
        "<Choose><When Condition=\"true\" /><Otherwise><ItemGroup><I Include=\"x\" Condition=\"tr ue\" /></ItemGroup></Otherwise></Choose>",
        "<Target Name=\"T\" Condition=\"tr ue\" />",
        "<Target Name=\"T\"><PropertyGroup><R Condition=\"tr ue\">x</R></PropertyGroup></Target>",
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
}

#[test]
fn an_illegal_condition_msbuild_may_not_evaluate_may_be_rejected() {
    for body in [
        // Under a gate the walk cannot decide.
        format!(
            "<PropertyGroup Condition=\"{UNDECIDED_TRUE}\"><R Condition=\"tr ue\">x</R></PropertyGroup>"
        ),
        format!(
            "<PropertyGroup Condition=\"{UNDECIDED_TRUE} Or 'a' == 'a'\"><R Condition=\"tr ue\">x</R></PropertyGroup>"
        ),
        format!(
            "<ImportGroup Condition=\"{UNDECIDED_TRUE}\"><Import Project=\"nope.props\" Condition=\"tr ue\" /></ImportGroup>"
        ),
        format!(
            "<ItemDefinitionGroup Condition=\"{UNDECIDED_TRUE}\"><I Condition=\"tr ue\" /></ItemDefinitionGroup>"
        ),
        // A `<When>` after one the walk cannot decide, and what an unchosen
        // branch after it holds.
        format!(
            "<Choose><When Condition=\"{UNDECIDED_TRUE}\" /><When Condition=\"tr ue\" /></Choose>"
        ),
        format!(
            "<Choose><When Condition=\"{UNDECIDED_TRUE}\"><PropertyGroup><R Condition=\"tr ue\">x</R></PropertyGroup></When></Choose>"
        ),
        format!(
            "<Choose><When Condition=\"{UNDECIDED_TRUE}\" /><Otherwise><ItemGroup><I Include=\"x\" Condition=\"tr ue\" /></ItemGroup></Otherwise></Choose>"
        ),
        // An `Update`'s metadata, evaluated only where the update applies.
        "<ItemGroup><I Update=\"x\"><M Condition=\"tr ue\">m</M></I></ItemGroup>".to_owned(),
        // An ill-typed comparison on a value the walk is not certain of.
        format!(
            "<PropertyGroup><W Condition=\"{UNDECIDED_TRUE}\">5</W><R Condition=\"$(W) &gt; 1\">x</R></PropertyGroup>"
        ),
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn(&parsed, &["Before", "After"]);
        }
    }
}

/// Past an operand the walk cannot evaluate, a literal that throws only once
/// the file system has its say (`/tmp\a;b`: the Unix path adjustment, then
/// two items) is still judged, with the file system: MSBuild may reach it.
#[test]
fn a_literal_needing_the_file_system_past_an_unevaluable_operand_may_reject() {
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <PropertyGroup Condition=\"'É' == 'é' And \
         HasTrailingSlash('/tmp\\a;b')\"><R>x</R></PropertyGroup>",
        &[],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

/// Neither deciding a gate nor judging a rejection probes an operand past one
/// that settles the question: an operand we cannot evaluate ends a decision,
/// and a condition only possibly reached is Possible however its operands
/// stand. So `tail`, which only such an operand reads, is not in the read set,
/// and a change to it does not invalidate the evaluation.
#[test]
fn an_operand_past_the_one_that_settles_the_question_is_not_probed() {
    for body in [
        // The walk's evaluation stops at `U` (`x`, true); deciding the gate
        // without trusting `U` goes on, and stops at the operand it cannot
        // evaluate.
        format!(
            "<PropertyGroup><P>abc</P><U>x</U><U Condition=\"{UNDECIDED_TRUE}\">y</U></PropertyGroup>\
             <PropertyGroup Condition=\"'$(U)' == 'x' Or ('$(P.Substring(5))' == '' And Exists('tail'))\">\
             <R>x</R></PropertyGroup>"
        ),
        format!(
            "<PropertyGroup><U>1</U><U Condition=\"{UNDECIDED_TRUE}\">true</U></PropertyGroup>\
             <PropertyGroup Condition=\"{UNDECIDED_TRUE}\"><R Condition=\"$(U) And Exists('tail')\">x</R></PropertyGroup>"
        ),
        // Evaluation stops at an operand it cannot evaluate; `Exists` cannot
        // throw, nor gates an operand that can.
        "<PropertyGroup Condition=\"'É' == 'é' And Exists('tail')\">\
         <R>x</R></PropertyGroup>"
            .to_owned(),
        // ... nor a boolean literal after it, quoted or not.
        "<PropertyGroup Condition=\"'É' == 'é' And Exists('tail') \
         And true\"><R>x</R></PropertyGroup>"
            .to_owned(),
        "<PropertyGroup Condition=\"'É' == 'é' And Exists('tail') \
         And 'true'\"><R>x</R></PropertyGroup>"
            .to_owned(),
        // Evaluation stops at an operand it cannot evaluate; whether MSBuild
        // may throw is settled in the `Or`, before `Exists`.
        "<PropertyGroup Condition=\"('É' == 'é' Or 1 &lt; abc) \
         And Exists('tail')\"><R>x</R></PropertyGroup>"
            .to_owned(),
        // Reached for certain, throwing on the value the walk holds (unset)
        // but not certainly on MSBuild's: whether it throws for certain is
        // settled at `U`.
        format!(
            "<PropertyGroup><U Condition=\"{UNDECIDED_TRUE}\">true</U></PropertyGroup>\
             <UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Condition=\"$(U) And Exists('tail')\" />"
        ),
    ] {
        let tmp = TempDir::new().unwrap();
        let project_path = project(&tmp, &format!("  {body}"), &[]);
        let parsed = parse_file(&project_path);
        let probed: Vec<_> = parsed
            .read_set
            .reads()
            .iter()
            .filter(|read| read.path.ends_with("tail"))
            .collect();
        assert!(probed.is_empty(), "{body}: {probed:#?}");
    }
}

/// An illegal operand MSBuild reaches through operands of certain value
/// rejects the project for certain, whatever a later operand it never reaches
/// reads; reached only past an operand the walk is not certain of, which may
/// decide the condition first, it may.
#[test]
fn an_illegal_condition_is_certain_as_far_as_its_reach() {
    let prefix =
        format!("<PropertyGroup><X>1</X><X Condition=\"{UNDECIDED_TRUE}\">abc</X></PropertyGroup>");
    for c in [
        "1 &lt; abc Or '$(X)' == 'x'",
        "'a' == 'a' And 1 &lt; abc And $(X) &gt; 2",
    ] {
        let body = format!("{prefix}<PropertyGroup><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_rejected(&parsed, &["Before", "After"]);
        }
    }
    for c in [
        "'$(X)' == 'abc' Or 1 &lt; abc",
        "'$(X)' == '1' And 1 &lt; abc",
    ] {
        let body = format!("{prefix}<PropertyGroup><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn(&parsed, &["Before", "After"]);
        }
    }
}

/// A comparison MSBuild reaches, left to right, before a later operand decides
/// the condition, on a value the walk holds legal but is not certain of
/// (`1`, which MSBuild overwrites with `abc`): MSBuild rejects the project. The
/// walk does not yet judge a condition legal on the values it holds (#1009),
/// so it withdraws nothing. Pinned, in every position a condition takes that
/// raises no other doubt, so that judging them shows here.
#[test]
fn a_condition_legal_on_the_values_the_walk_holds_is_not_yet_judged() {
    for position in [
        "<PropertyGroup><R Condition=\"{c}\">x</R></PropertyGroup>",
        "<PropertyGroup Condition=\"{c}\"><R>x</R></PropertyGroup>",
        "<ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup>",
        "<ItemGroup><I Include=\"x\" Condition=\"{c}\" /></ItemGroup>",
        "<Choose><When Condition=\"{c}\" /></Choose>",
    ] {
        for c in ["$(X) &gt; 2 And false", "$(X) &gt; 2 Or true"] {
            let body = format!(
                "<PropertyGroup><X>1</X><X Condition=\"{UNDECIDED_TRUE}\">abc</X></PropertyGroup>{}",
                position.replace("{c}", c)
            );
            for parsed in both_walkers(&format!("  {body}")) {
                assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
            }
        }
    }
}

#[test]
fn an_illegal_condition_after_content_the_walk_did_not_see_may_be_rejected() {
    // A syntax error rejects whatever the values, but hidden content before
    // it may decide a gate around it otherwise. Here the hidden import is
    // the pure walker's, which follows none.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <Import Project=\"there.props\" />\n  \
         <PropertyGroup><R Condition=\"tr ue\">x</R></PropertyGroup>",
        &[("proj/there.props", "<Project />")],
    );
    let text = host_fs::read_to_string(&project_path).unwrap();
    let pure = parse_fsproj(
        &crate::ProjectFile::buffer(&project_path, &text)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &HashMap::new(),
    )
    .unwrap();
    assert_withdrawn(&pure, &["Before", "After"]);
    assert_rejected(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn a_certain_rejection_outranks_an_earlier_possible_one() {
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup Condition=\"{UNDECIDED_TRUE}\"><R Condition=\"tr ue\">x</R></PropertyGroup>\n  \
             <PropertyGroup><R Condition=\"'a' = 'a'\">x</R></PropertyGroup>"
        ),
        &[],
    );
    let parsed = parse_file(&project_path);
    assert_rejected(&parsed, &["Before", "After"]);
    assert_eq!(
        parsed.rejection.unwrap().cause,
        RejectionCause::IllegalCondition {
            condition: "'a' = 'a'".to_owned()
        }
    );
}

#[test]
fn an_import_through_a_missing_directory_msbuild_collapses_loads() {
    // MSBuild collapses `missing/..` as text and loads `there.props`, through
    // a directory that is not there; so does the walk.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <Import Project=\"missing/../there.props\" />",
        &[("proj/there.props", "<Project />")],
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None);
    assert_eq!(parsed.property("After"), PropertyRead::Value("1".into()));
}

#[test]
fn an_import_msbuild_fails_before_it_collapses_the_path_is_withdrawn() {
    // A trailing separator names a directory (MSB4019), and a NUL fails the
    // path (MSB4102), though collapsing either away would name `E.props`.
    for import in [
        "<Import Project=\"E.props/\" />",
        "<Import Project=\"E.props/./\" />",
        "<Import Project=\"bad%00/../E.props\" />",
    ] {
        let tmp = TempDir::new().unwrap();
        let project_path = project(
            &tmp,
            &format!("  {import}"),
            &[(
                "proj/E.props",
                "<Project><PropertyGroup><Alpha>1</Alpha></PropertyGroup></Project>",
            )],
        );
        assert_withdrawn(&parse_file(&project_path), &["Before", "After", "Alpha"]);
    }
}

#[test]
fn metadata_evaluated_item_by_item_is_not_claimed() {
    // Metadata that reads `%(…)` is evaluated once per item, so not at all
    // for an `Include` that names none (`where_msbuild_evaluates_a_condition`).
    let body = "<ItemGroup><I Include=\"$(Missing)\"><O>%(Filename)</O>\
                <M Condition=\"tr ue\">m</M></I></ItemGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_ne!(
            parsed.rejection.map(|r| r.certainty),
            Some(RejectionCertainty::Certain)
        );
    }
}

#[test]
fn an_import_a_group_may_not_make_does_not_make_a_later_one_a_duplicate() {
    // In a group MSBuild takes, the first import's own condition is false, so
    // MSBuild never imports `cs/a.props`, and the second, `CS/a.props`, is no
    // duplicate: where names are case-sensitive it is another file, which is
    // malformed. The first import's own condition is undecidable, so it
    // cannot make the second one a duplicate. Each import's spelling is tried
    // plain and as a wildcard. A case-insensitive file system cannot hold the
    // two files, and makes no claim.
    for first in ["cs/a.props", "cs/*.props"] {
        let tmp = TempDir::new().unwrap();
        std::fs::create_dir_all(tmp.path().join("proj/cs")).unwrap();
        if crate::observed::host_fs::symlink_metadata(tmp.path().join("proj/CS")).is_ok() {
            return;
        }
        let project_path = project(
            &tmp,
            &format!(
                "  <ImportGroup Condition=\"{UNDECIDED_TRUE}\">\n    <Import Project=\"{first}\" \
                 Condition=\"'É' == 'Ê'\" />\n    \
                 <Import Project=\"CS/a.props\" />\n  </ImportGroup>"
            ),
            &[
                ("proj/cs/a.props", "<Project />"),
                ("proj/CS/a.props", "<Project"),
            ],
        );
        assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
    }
}

#[test]
fn an_undecided_import_with_a_written_backslash_is_judged_as_written_with_a_slash() {
    // MSBuild turns the attribute's own `\` into `/` before expanding it, so
    // `sub\..\there.props` is `there.props` beside the project, which loads.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"sub\\..\\there.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[("proj/there.props", "<Project />")],
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
}

#[test]
fn an_undecided_import_of_a_backslash_the_working_directory_decides_may_be_rejected() {
    // `sub\x/../there.props` from a property opens `sub/there.props`, which is
    // missing, where `sub/` is a directory under MSBuild's working directory,
    // and `there.props` (its `..` popping `sub\x` whole) where it is not.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!(
            "  <PropertyGroup><P>sub\\x/../there.props</P></PropertyGroup>\n  \
             <Import Project=\"$(P)\" Condition=\"{UNDECIDED_TRUE}\" />"
        ),
        &[("proj/there.props", "<Project />")],
    );
    let parsed = parse_file(&project_path);
    assert_withdrawn(&parsed, &["After"]);
}

/// Constructs MSBuild refuses when it loads the file holding them (#888),
/// whatever any condition holds; each probed with `dotnet msbuild` 10.0.
const LOAD_TIME_REJECTED: &[&str] = &[
    // MSB4004, a reserved property name in any case, or a reserved element
    // name, anywhere a property is parsed.
    "<PropertyGroup><MSBuildProjectDirectory>x</MSBuildProjectDirectory></PropertyGroup>",
    "<PropertyGroup Condition=\"false\"><msbuildprojectdirectory>x</msbuildprojectdirectory></PropertyGroup>",
    "<PropertyGroup><MSBuildThisFile Condition=\"false\">x</MSBuildThisFile></PropertyGroup>",
    "<PropertyGroup><MSBuildDisableFeaturesFromVersion>x</MSBuildDisableFeaturesFromVersion></PropertyGroup>",
    "<PropertyGroup><When>x</When></PropertyGroup>",
    "<Choose><When Condition=\"false\"><PropertyGroup><MSBuildProjectName>x</MSBuildProjectName></PropertyGroup></When></Choose>",
    "<Target Name=\"T\"><PropertyGroup><MSBuildProjectName>x</MSBuildProjectName></PropertyGroup></Target>",
    // MSB4035 and MSB4232: an item without a usable specification.
    "<ItemGroup Condition=\"false\"><I Include=\"\" /></ItemGroup>",
    "<ItemGroup><I Include=\"\" Condition=\"false\" /></ItemGroup>",
    "<ItemGroup><I Remove=\"\" /></ItemGroup>",
    "<ItemGroup><I Update=\"\" /></ItemGroup>",
    "<ItemGroup><I /></ItemGroup>",
    "<Target Name=\"T\"><ItemGroup><I Include=\"\" /></ItemGroup></Target>",
    "<Choose><When Condition=\"false\"><ItemGroup><I Include=\"\" /></ItemGroup></When></Choose>",
    // MSB4035: an `<Import>` with no `Project`, wherever it sits.
    "<ImportGroup Condition=\"false\"><Import /></ImportGroup>",
    "<ImportGroup Condition=\"false\"><Import Project=\"\" /></ImportGroup>",
    "<Import Condition=\"false\" />",
    // A malformed `<Choose>`, at any depth.
    "<Choose />",
    "<Choose><When Condition=\"true\" /><Otherwise /><Otherwise /></Choose>",
    "<Choose><When Condition=\"false\"><Choose /></When><Otherwise /></Choose>",
];

/// Shapes beside those that MSBuild loads.
const LOAD_TIME_ACCEPTED: &[&str] = &[
    "<PropertyGroup><MSBuildExtensionsPath>x</MSBuildExtensionsPath></PropertyGroup>",
    "<PropertyGroup><choose>x</choose><Import>x</Import><ItemDefinitionGroup>x</ItemDefinitionGroup></PropertyGroup>",
    "<ItemGroup><I Include=\" \" /><J Include=\"$(Nothing)\" /></ItemGroup>",
    "<Target Name=\"T\"><ItemGroup><I /></ItemGroup></Target>",
    "<ImportGroup Condition=\"false\"><Import Project=\"$(Nothing)\" /><Import Project=\" \" /></ImportGroup>",
    "<Choose><When Condition=\"true\" /><When Condition=\" \" /></Choose>",
    "<ProjectExtensions><PropertyGroup><MSBuildThisFile>x</MSBuildThisFile></PropertyGroup></ProjectExtensions>",
];

#[test]
fn a_construct_msbuild_refuses_at_load_time_is_rejected() {
    for body in LOAD_TIME_REJECTED {
        for parsed in both_walkers(&format!("  {body}")) {
            let rejection = parsed
                .rejection
                .as_ref()
                .unwrap_or_else(|| panic!("no rejection for {body}: {:#?}", parsed.diagnostics));
            assert!(
                matches!(rejection.cause, RejectionCause::LoadTime(_)),
                "{body}: {rejection:#?}"
            );
            assert_rejected(&parsed, &["Before", "After"]);
        }
    }
    for body in LOAD_TIME_ACCEPTED {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}");
        }
    }
}

#[test]
fn a_file_msbuild_refuses_at_load_time_rejects_where_it_is_imported() {
    let refused = "<Project><ItemGroup><I Include=\"\" /></ItemGroup></Project>";
    let import =
        |gate: &str| format!("  <Import Project=\"refused.props\" Condition=\"{gate}\" />");
    // Imported for certain: MSBuild loads the file, and refuses it.
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, &import("true"), &[("proj/refused.props", refused)]);
    assert_rejected(&parse_file(&project_path), &["Before", "After"]);
    // Never imported: MSBuild never loads it.
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, &import("false"), &[("proj/refused.props", refused)]);
    assert_eq!(parse_file(&project_path).rejection, None);
    // Imported through a `\` a property supplies that no spelling of MSBuild's
    // Unix adjustment can move (#903): it opens `sub/refused.props` either way.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <PropertyGroup><P>sub\\refused.props</P></PropertyGroup>\n  <Import Project=\"$(P)\" />",
        &[("proj/sub/refused.props", refused)],
    );
    assert_rejected(&parse_file(&project_path), &["Before", "After"]);
    // Imported through a path the walk does not name for certain: whether the
    // `..` pops `sub\x` whole depends on MSBuild's working directory (#903), so
    // MSBuild may load another file.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <PropertyGroup><P>sub\\x/../refused.props</P></PropertyGroup>\n  <Import Project=\"$(P)\" />",
        &[
            ("proj/refused.props", refused),
            ("proj/sub/refused.props", refused),
        ],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn a_rule_a_parse_configuration_may_relax_is_claimed_only_where_none_can_apply() {
    // MSB4066. A newer MSBuild skips the attribute when a parse configuration
    // lists it (#917): one beside the project, one above it, or one the
    // environment names.
    let relaxable = "  <PropertyGroup X=\"1\"><R>x</R></PropertyGroup>";
    let tmp = TempDir::new().unwrap();
    assert_rejected(
        &parse_file(&project(&tmp, relaxable, &[])),
        &["Before", "After"],
    );
    for config in ["proj/Directory.Parse.config", "Directory.Parse.config"] {
        let tmp = TempDir::new().unwrap();
        let project_path = project(&tmp, relaxable, &[(config, "<ParseConfig />")]);
        assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
    }
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, relaxable, &[]);
    let environment = HashMap::from([(
        "MSBUILD_PARSE_CONFIG".to_owned(),
        "/elsewhere/parse.config".to_owned(),
    )]);
    let parsed = parse_file_with_sdk_env(
        &project_path,
        |_: &str| Err(SdkResolveError::NotFound),
        HashMap::new(),
        environment,
    );
    assert_withdrawn(&parsed, &["Before", "After"]);
    // A rule no configuration relaxes, beside it, is claimed anyway.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <PropertyGroup X=\"1\"><MSBuildProjectName>x</MSBuildProjectName></PropertyGroup>",
        &[("proj/Directory.Parse.config", "<ParseConfig />")],
    );
    assert_rejected(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_include_beside_an_empty_remove_is_rejected() {
    // MSBuild throws a null reference on it (MSB1025 from `dotnet msbuild`),
    // which the loader differential's oracle cannot report as a rejection.
    for parsed in both_walkers("  <ItemGroup><I Include=\"x\" Remove=\"\" /></ItemGroup>") {
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// A leaf over a name the walk holds no value of (`X`, a write it refused to
/// compute) has none of MSBuild's booleans, whatever it computes on the `""`
/// it substitutes: `IsNullOrWhiteSpace('')` is true, but MSBuild's `X` is
/// `Debug`, so its `Or` goes on to an order on a word, which throws. What
/// comes after such a leaf is reached perhaps.
#[test]
fn a_leaf_on_a_value_the_walk_holds_none_of_decides_nothing_after_it() {
    let refused = "<X>$([System.String]::Copy('Debug'))</X>";
    for c in [
        "'$([System.String]::IsNullOrWhiteSpace(`$(X)`))' Or '' &gt; 'x'",
        "'$(X)' == '' Or '' &gt; 'x'",
        "!('$(X)' != '') Or '' &gt; 'x'",
    ] {
        let body = format!("<PropertyGroup>{refused}<R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn(&parsed, &["Before", "After"]);
        }
    }
}

/// MSBuild expands an item's operation by what the operation reads
/// (`LazyItemEvaluator`): an `Include` and its `Exclude`, a `Remove` and its
/// `MatchOnMetadata`, an `Update`. The `MatchOnMetadata` options are parsed
/// as written, and an operation's attribute on another operation's item is
/// not expanded (probed, `msbuild-condition-oracle`, SDK 10.0.401).
#[test]
fn an_item_attribute_is_judged_by_the_operation_that_reads_it() {
    for body in [
        "<ItemGroup><I Include=\"x\" MatchOnMetadata=\"$(P[9])\" /></ItemGroup>",
        "<ItemGroup><I Include=\"x\" MatchOnMetadataOptions=\"$(P[9])\" /></ItemGroup>",
        "<ItemGroup><I Update=\"x\" MatchOnMetadata=\"$(P[9])\" /></ItemGroup>",
        "<ItemGroup><J Include=\"x\" /><I Remove=\"@(J)\" MatchOnMetadata=\"M\" MatchOnMetadataOptions=\"$(P[9])\" /></ItemGroup>",
    ] {
        let body = format!("<PropertyGroup><P>abc</P></PropertyGroup>{body}");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
    let body = "<PropertyGroup><P>abc</P></PropertyGroup><ItemGroup><J Include=\"x\" /><I Remove=\"@(J)\" MatchOnMetadata=\"$(P[9])\" /></ItemGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// A boolean the walk does not compute coerces without throwing only where it
/// is the whole operand: beside text it is a word (`xFalse`), which MSBuild
/// throws on coercing.
#[test]
fn a_boolean_beside_text_is_no_boolean() {
    for c in [
        "'x$([System.String]::IsNullOrWhiteSpace(`é`))'",
        "'$([System.String]::IsNullOrWhiteSpace(`é`))x'",
    ] {
        let body = format!("<PropertyGroup><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            let certainty = parsed
                .rejection
                .as_ref()
                .map_or(RejectionCertainty::Possible, |r| r.certainty);
            assert_withdrawn_as(&parsed, &["Before", "After"], certainty);
        }
    }
    let body = "<PropertyGroup><R Condition=\"'$([System.String]::IsNullOrWhiteSpace(`é`))'\">x</R></PropertyGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
    }
}

/// A throw rests on what its expression read before it threw: a later step,
/// which MSBuild never reaches, reading a name the walk holds no value of
/// does not make the throw one the walk cannot judge.
#[test]
fn a_throw_rests_only_on_what_it_read_before_it() {
    let refused = "<X>$([System.String]::Copy('Debug'))</X>";
    for body in [
        format!(
            "<PropertyGroup><P>abc</P>{refused}<R>$(P.Split(';')[9].Contains('$(X)'))</R></PropertyGroup>"
        ),
        format!(
            "<PropertyGroup><P>abc</P>{refused}<R Condition=\"'$(P.Split(`;`)[9].Contains(`$(X)`))' == ''\">x</R></PropertyGroup>"
        ),
    ] {
        // In a condition the throw's certainty is judged leaf-wise, a
        // doubted name anywhere in the leaf leaving it Possible.
        let certainty = if body.contains("Condition") {
            RejectionCertainty::Possible
        } else {
            RejectionCertainty::Certain
        };
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn_as(&parsed, &["Before", "After"], certainty);
        }
    }
}

/// MSBuild expands an item's text's properties before its item lists, so a
/// function is handed an item list as written, in an operation or a
/// metadatum alike: `VersionEquals('@(J)', '1.0')` throws whatever `J` holds
/// (probed, `msbuild-condition-oracle`, SDK 10.0.401). A metadata reference
/// in an operation is likewise read as written; in a metadatum it is the
/// metadatum's value, which the walk does not judge (#1094).
#[test]
fn an_item_list_in_an_items_function_is_read_as_written() {
    let call = "$([MSBuild]::VersionEquals('@(J)','1.0'))";
    for body in [
        format!("<ItemGroup><J Include=\"1.0\" /><I Include=\"{call}\" /></ItemGroup>"),
        format!("<ItemGroup><J Include=\"1.0\" /><I Include=\"x\" M=\"{call}\" /></ItemGroup>"),
        format!("<ItemGroup><J Include=\"1.0\" /><I Include=\"x\"><M>{call}</M></I></ItemGroup>"),
        "<ItemGroup><I Include=\"$([MSBuild]::VersionEquals('%(M)','1.0'))\" /></ItemGroup>"
            .to_owned(),
    ] {
        // Metadata reading an item list is evaluated item by item, which the
        // walk does not count here: reached perhaps.
        let certainty = if body.contains("<I Include=\"x\"") {
            RejectionCertainty::Possible
        } else {
            RejectionCertainty::Certain
        };
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn_as(&parsed, &["Before", "After"], certainty);
        }
    }
}

/// In an item's condition MSBuild expands an item expression its properties
/// form after it expands them, so one formed beside a boolean the walk does
/// not compute is still formed: `@(Foo->NoSuchFunction())` throws.
#[test]
fn an_item_expression_beside_an_unknown_boolean_may_reject() {
    let body = "<PropertyGroup><A>@</A><B>(Foo-&gt;NoSuchFunction())</B></PropertyGroup><ItemGroup><Foo Include=\"f\" /><I Include=\"x\" Condition=\"'$([System.String]::IsNullOrWhiteSpace(`é`))$(A)$(B)' == 'z'\" /></ItemGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// `Version.Parse` throws on what it cannot read, a boolean among them.
#[test]
fn a_version_parse_of_an_unknown_boolean_may_reject() {
    let body = "<PropertyGroup><R Condition=\"$([System.Version]::Parse($([System.String]::IsNullOrWhiteSpace('é'))).Build) == 1\">x</R></PropertyGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// An unquoted version argument holding an expansion is read as MSBuild
/// reads it: `VersionLessThan($(Major).0, 4.0)` is true for `Major=3`.
#[test]
fn an_unquoted_version_argument_around_an_expansion_is_read() {
    let body = "<PropertyGroup><Major>3</Major><R Condition=\"$([MSBuild]::VersionLessThan($(Major).0,4.0))\">x</R></PropertyGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        assert_eq!(parsed.property("R").value(), Some("x"), "{body}");
    }
}

/// A file-system function MSBuild throws on, in text the walk does not
/// expand itself (an item's `Include`), is judged on what the file system
/// holds, as the walk's own expansions are: `GetDirectoryNameOfFileAbove`
/// finds no file and returns `''`, which has no first character.
#[test]
fn a_file_system_function_in_an_items_text_is_judged_on_the_file_system() {
    let body = "<ItemGroup><I Include=\"$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildProjectDirectory), 'surely-not-here-1009.props')[0])\" /></ItemGroup>";
    let [with_imports, _] = both_walkers(&format!("  {body}"));
    assert_rejected(&with_imports, &["Before", "After"]);
}

/// A throw that read a name the walk holds no value of is judged where it
/// throws whatever that name's expressions return, on the rest: `true` is no
/// version, whatever `X` is (MSBuild's `X` is `Debug`; it throws). In a text
/// and in a condition's `Exists` alike.
#[test]
fn a_throw_whatever_an_unheld_name_returns_may_reject() {
    let refused = "<X>$([System.String]::Copy('Debug'))</X>";
    for body in [
        format!(
            "<PropertyGroup><A>true</A>{refused}<R>$([MSBuild]::VersionLessThan($(A),$(X)))</R></PropertyGroup>"
        ),
        format!(
            "<PropertyGroup><A>true</A>{refused}</PropertyGroup><ItemGroup><I Include=\"x\" Condition=\"Exists('$([MSBuild]::VersionLessThan($(X),$(A)))')\" /></ItemGroup>"
        ),
    ] {
        for parsed in both_walkers(&format!("  {body}")) {
            assert_withdrawn(&parsed, &["Before", "After"]);
        }
    }
}

/// A body under a gate the walk decides true whatever it could not evaluate
/// (`'$(U[0])' == 'z' Or true` is true wherever it returns) is one MSBuild
/// evaluates, and a throw in it is judged.
#[test]
fn a_throw_under_a_gate_decided_true_past_an_unknown_operand_is_judged() {
    let refused = "<U>$([System.String]::Copy('abc'))</U>";
    for gate in ["'$(U[0])' == 'z' Or true", "'$(U)' == 'z' Or true"] {
        let body = format!(
            "<PropertyGroup><P>a</P>{refused}<R Condition=\"{gate}\">$(P[9])</R></PropertyGroup>"
        );
        for parsed in both_walkers(&format!("  {body}")) {
            let certainty = parsed
                .rejection
                .as_ref()
                .map_or(RejectionCertainty::Possible, |r| r.certainty);
            assert_withdrawn_as(&parsed, &["Before", "After"], certainty);
        }
    }
}

/// Design-time evaluation of a property's condition expands both sides of an
/// equality, for its table of conditioned properties, even where one side
/// is empty and decides it: `'' != 'a$(P[9])'` throws there, though a build
/// never expands `'a$(P[9])'`. An item's condition does not: there the empty
/// side decides it, and the item is excluded.
#[test]
fn an_empty_side_does_not_spare_the_other_from_design_time_expansion() {
    for c in ["'' != 'a$(P[9])'", "'a$(P[9])' == ''"] {
        let body = format!("<PropertyGroup><P>a</P><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_rejected(&parsed, &["Before", "After"]);
        }
        let body = format!(
            "<PropertyGroup><P>a</P></PropertyGroup><ItemGroup><I Include=\"x\" Condition=\"{c}\" /></ItemGroup>"
        );
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
}

/// A leaf on a name the walk is not sure of, though it holds a value MSBuild
/// may hold, has none of MSBuild's booleans: `U` is `''` as the walk holds it,
/// but MSBuild takes the write the walk could not decide, so its `Or` goes on
/// to an order on a word, which throws.
#[test]
fn a_leaf_on_a_value_the_walk_is_not_sure_of_decides_nothing_after_it() {
    let body = format!(
        "<PropertyGroup><U></U><U Condition=\"{UNDECIDED_TRUE}\">yes</U>\
         <R Condition=\"$([System.String]::IsNullOrWhiteSpace('$(U)')) Or 1 &lt; abc\">x</R></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// An `Update` under a gate certainly false applies nowhere, so MSBuild
/// expands none of its metadata.
#[test]
fn an_update_under_a_false_gate_expands_no_metadata() {
    for body in [
        "<ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"false\" M=\"$(P[9])\" /></ItemGroup>",
        "<ItemGroup><I Include=\"x\" /></ItemGroup><ItemGroup Condition=\"false\"><I Update=\"x\" M=\"$(P[9])\" /></ItemGroup>",
        "<ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"false\"><M>$(P[9])</M></I></ItemGroup>",
    ] {
        let body = format!("<PropertyGroup><P>a</P></PropertyGroup>{body}");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        }
    }
}

/// A typed result spliced among other text in a version argument is the
/// text it renders as: `VersionGreaterThan($(P.Length).0, 0)` is true for
/// `P=1`, quoted or not.
#[test]
fn a_typed_result_among_text_in_a_version_argument_is_its_text() {
    for c in [
        "$([MSBuild]::VersionGreaterThan($(P.Length).0, 0))",
        "$([MSBuild]::VersionGreaterThan('$(P.Length).0', 0))",
    ] {
        let body = format!("<PropertyGroup><P>1</P><R Condition=\"{c}\">x</R></PropertyGroup>");
        for parsed in both_walkers(&format!("  {body}")) {
            assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
            assert_eq!(parsed.property("R").value(), Some("x"), "{body}");
        }
    }
}

/// MSBuild expands an item's text after every property write, so an item in
/// a `<Choose>` branch the walk does not take is judged against the final
/// table: `P` is `a` there, which has no index 1, though it is `abc` where
/// the branch stands.
#[test]
fn an_untaken_branchs_items_are_judged_against_the_final_table() {
    let branch = format!(
        "<Choose><When Condition=\"{UNDECIDED_TRUE}\"><ItemGroup><I Include=\"$(P[1])\" /></ItemGroup></When></Choose>"
    );
    let rejected = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup>{branch}<PropertyGroup><P>a</P></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {rejected}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
    let evaluated = format!(
        "<PropertyGroup><P>a</P></PropertyGroup>{branch}<PropertyGroup><P>abc</P></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {evaluated}")) {
        assert_eq!(
            parsed.rejection, None,
            "{evaluated}: {:#?}",
            parsed.diagnostics
        );
    }
}

/// A write in content the walk does not take leaves its name's value there
/// unknown to what follows on that path, so nothing reading it there is
/// certain; but a throw on the value the walk holds from before the content,
/// `a`, which MSBuild holds where it skips the group, is a Possible site,
/// though on the path through the group MSBuild reads `abc`, which has an
/// index 1, and evaluates the project. A decline: judging the content's own
/// value is the judgement over the values a name may hold (#1051, #1200),
/// and trying values for the name instead was not monotone (#1164).
#[test]
fn a_write_in_untaken_content_is_judged_on_the_value_before_it() {
    let body = format!(
        "<PropertyGroup><P>a</P></PropertyGroup><PropertyGroup Condition=\"{UNDECIDED_TRUE}\"><P>abc</P><Q>$(P[1])</Q></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// Each branch of a `<Choose>` in content the walk does not take starts from
/// what the path held before it: a write in one `<When>` is no write in the
/// `<Otherwise>`, where `P` is `abc`, which has no index 9.
#[test]
fn a_branch_does_not_see_its_siblings_writes() {
    let body = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\"><Choose>\
         <When Condition=\"'É' == 'x'\"><PropertyGroup><P>abcdefghijkl</P></PropertyGroup></When>\
         <Otherwise><PropertyGroup><R>$(P[9])</R></PropertyGroup></Otherwise>\
         </Choose></When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// MSBuild turns a `UsingTask`'s `AssemblyFile`'s own `\` into `/` before it
/// expands it where `\` is no separator: `$(P.Split('\')[1])` splits `a/b`
/// on `/`.
#[cfg(not(windows))]
#[test]
fn a_using_task_assembly_file_is_read_with_its_slashes_turned() {
    let body = "<PropertyGroup><P>a/b</P></PropertyGroup><UsingTask TaskName=\"X\" AssemblyFile=\"$(P.Split('\\')[1])\" />";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
    }
}

/// Whether an item's metadata is evaluated item by item is read from the
/// metadata as MSBuild reads it: `&lt;![CDATA[%]]&gt;(Identity)` in an
/// attribute is `%(Identity)`, so with no item MSBuild evaluates no metadata,
/// and a throw in it is no certain rejection.
#[test]
fn per_item_metadata_is_read_from_its_decoded_value() {
    let body = "<PropertyGroup><Z>abc</Z></PropertyGroup><ItemGroup><I Include=\"$(Empty)\" V=\"&lt;![CDATA[%]]&gt;(Identity)\"><M>$(Z[9])</M></I></ItemGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_ne!(
            parsed.rejection.as_ref().map(|r| r.certainty),
            Some(RejectionCertainty::Certain),
            "{body}: {:#?}",
            parsed.rejection
        );
    }
}

/// An item group in a `<Choose>` branch the walk does not take, judged in the
/// item pass, knows the names written before it on that path: `P` is long
/// enough to index there, though the final table holds `abc`, so nothing
/// reading `P` there is certain. A throw on the `abc` the walk holds is a
/// Possible site all the same, a decline (#1164, #1200).
#[test]
fn an_untaken_branchs_items_know_the_writes_before_them() {
    let body = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
         <ItemGroup><I Include=\"$(P[9])\" /></ItemGroup></When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// A certain write after the path settles what the item pass reads: `P` is
/// `z` there, which has no index 9, whatever the branch wrote.
#[test]
fn a_certain_write_after_the_path_settles_an_items_value() {
    let body = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
         <ItemGroup><I Include=\"$(P[9])\" /></ItemGroup></When></Choose>\
         <PropertyGroup><P>z</P></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// So does one after a write the walk refused (an item list, a function it
/// does not model): the walk holds `z` as MSBuild does, whether the refusal
/// came first or just before, and the mark it keeps of it is history the item
/// pass does not read (#1153). A text and a condition alike.
#[test]
fn a_certain_write_after_a_refused_one_settles_an_items_value() {
    for refused in ["@(J)", "$([System.String]::Copy('d'))"] {
        for (first, last) in [
            (format!("<P>{refused}</P>"), "<P>z</P>".to_owned()),
            ("<P>abc</P>".to_owned(), format!("<P>{refused}</P><P>z</P>")),
        ] {
            for group in [
                "<ItemGroup><I Include=\"$(P[9])\" /></ItemGroup>",
                "<ItemGroup Condition=\"'$(P[9])' != ''\"><I Include=\"x\" /></ItemGroup>",
            ] {
                let body = format!(
                    "<PropertyGroup>{first}</PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
                     <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>{group}</When></Choose>\
                     <PropertyGroup>{last}</PropertyGroup>"
                );
                for parsed in both_walkers(&format!("  {body}")) {
                    assert_withdrawn(&parsed, &["Before", "After"]);
                }
            }
        }
    }
}

/// A name the second walk holds settled does not decide a condition's
/// course: `'$(P)' == 'abcdefghijkl'` is false on `P`'s final `z`, so MSBuild
/// never reaches `$(P[9])` and evaluates the project, but which operands
/// MSBuild reaches is main's to decide in either walk, and main doubts the
/// refused `P` there, so each walk judges `$(P[9])` on the `z` it holds. The
/// site stands, Possible: a decline, never a claim (#1153, #1164, #1183).
#[test]
fn a_condition_the_walk_doubts_keeps_a_second_walks_site() {
    let body = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
         <ItemGroup Condition=\"'$(P)' == 'abcdefghijkl' And '$(P[9])' != ''\"><I Include=\"x\" /></ItemGroup>\
         </When></Choose>\
         <PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        let rejection = parsed.rejection.as_ref().expect("the second walk's site");
        assert_eq!(rejection.certainty, RejectionCertainty::Possible, "{body}");
    }
}

/// But not the gates around a site: under `'$(P)' == 'abcdefghijkl'`, false
/// on `P`'s final `z`, MSBuild expands no metadatum, update or definition, so
/// it rejects none of these rows. Either walk, deciding a gate it judges as
/// main does, takes it as undecided, and finds the throw on the `z` it holds
/// in a gated metadatum or update (#1164). What MSBuild reaches is main's to
/// decide in both walks, so that site stands, Possible: a decline MSBuild does
/// not need, never a claim (#1153, #1183). Neither walk judges a definition
/// from an untaken arm, so the definition rows note nothing; that is #1172's
/// gap, which misses a throw MSBuild does reach, and fixing it may move these
/// rows to the item rows' Possible. A `<When>` holds no `<UsingTask>`, so no
/// task is judged from an untaken path.
#[test]
fn a_gate_the_walk_doubts_keeps_a_second_walks_site() {
    let gate = "'$(P)' == 'abcdefghijkl'";
    let possible = Some(RejectionCertainty::Possible);
    let rows = [
        (
            format!(
                "<ItemGroup><I Include=\"x\"><M Condition=\"{gate}\">$(P[9])</M></I></ItemGroup>"
            ),
            possible,
        ),
        (
            format!(
                "<ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"{gate}\"><M>$(P[9])</M></I></ItemGroup>"
            ),
            possible,
        ),
        (
            format!(
                "<ItemDefinitionGroup><I><M Condition=\"{gate}\">$(P[9])</M></I></ItemDefinitionGroup>"
            ),
            None,
        ),
        (
            format!(
                "<ItemDefinitionGroup Condition=\"{gate}\"><I><M>$(P[9])</M></I></ItemDefinitionGroup>"
            ),
            None,
        ),
        (
            format!(
                "<ItemDefinitionGroup><I Condition=\"{gate}\"><M>$(P[9])</M></I></ItemDefinitionGroup>"
            ),
            None,
        ),
    ];
    let throw = RejectionCause::ThrowingExpression {
        expression: "$(P[9])".to_string(),
    };
    for (group, expected) in rows {
        let body = format!(
            "<PropertyGroup><P>abc</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
             <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>{group}</When></Choose>\
             <PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup>"
        );
        for parsed in both_walkers(&format!("  {body}")) {
            let rejection = parsed.rejection.as_ref();
            assert_eq!(
                rejection.map(|r| r.certainty),
                expected,
                "{group}: {:#?}",
                parsed.diagnostics
            );
            if let Some(rejection) = rejection {
                assert_eq!(rejection.cause, throw, "{group}");
            }
        }
    }
}

/// The second walk holds a refused-then-rebound name certain only where
/// nothing else leaves its value unknown: the arm the walk does not take
/// writes `P` again, so in the arm `P` is uncertain to either walk, and
/// `$(P[9])`, which throws on the `abc` before the arm but not on the arm's
/// `abcdefghijkl`, MSBuild's value there, is a Possible site in either, a
/// decline (#1153, #1164, #1200), never a certain one.
#[test]
fn a_second_walk_holds_no_name_a_speculation_leaves_unknown() {
    let body = format!(
        "<PropertyGroup><P>@(J)</P><P>abc</P></PropertyGroup>\
         <Choose><When Condition=\"{UNDECIDED_TRUE}\"><PropertyGroup><P>abcdefghijkl</P>\
         <Q Condition=\"'$(P[9])' != ''\">q</Q></PropertyGroup></When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// But not the `<Choose>` the site's group stands in: `'$(P)' == 'off'` is
/// false on `P`'s `z`, so MSBuild takes no arm and evaluates the project, but
/// the walk's own course doubts the refused name, so it judges the arm in
/// either walk, and each, holding `P` at its final `z`, finds `$(P[9])`
/// throwing there (#1164). What each walk judges is main's to decide, so the
/// site stands, Possible: a decline MSBuild does not need, never a claim
/// (#1153).
#[test]
fn an_arm_the_walk_doubts_keeps_a_second_walks_site() {
    let body = "<PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup>\
                <Choose><When Condition=\"'$(P)' == 'off'\">\
                <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
                <ItemGroup><I Include=\"$(P[9])\" /></ItemGroup></When></Choose>";
    for parsed in both_walkers(&format!("  {body}")) {
        let rejection = parsed.rejection.as_ref().expect("the second walk's site");
        assert_eq!(rejection.certainty, RejectionCertainty::Possible);
        assert!(!parsed.property("After").is_exact());
    }
}

/// The record of sites adopted from a second walk is kept only while a
/// caller collects it: a walk that adopts one, uncollected, keeps nothing,
/// and a collection a panic leaves is closed (#1153). The site is the second
/// walk's name for a text reached for certain whose throws each walk picks
/// apart (`$(P[9])`, on the refused `P`'s `z`, where the first walk names the
/// certain `$(S[9])`). This pins the test collector, not an outcome the
/// oracle grades.
#[test]
fn an_uncollected_walk_keeps_no_second_walk_site() {
    let body = "<PropertyGroup><P>@(J)</P><P>z</P><S>a</S></PropertyGroup>\
                <ItemGroup><I Include=\"$(P[9])$(S[9])\" /></ItemGroup>";
    let (_, collected) =
        crate::test_support::second_walk_sites(|| both_walkers(&format!("  {body}")));
    assert!(
        !collected.is_empty(),
        "the walk adopts a second walk's site"
    );
    assert!(crate::test_support::second_walk_collector_idle());
    for parsed in both_walkers(&format!("  {body}")) {
        assert!(parsed.rejection.is_some());
    }
    assert!(crate::test_support::second_walk_collector_idle());
    let unwound = std::panic::catch_unwind(|| {
        crate::test_support::second_walk_sites(|| {
            both_walkers(&format!("  {body}"));
            panic!("out of the collected walk");
        })
    });
    assert!(unwound.is_err());
    assert!(crate::test_support::second_walk_collector_idle());
    let (_, collected) =
        crate::test_support::second_walk_sites(|| both_walkers(&format!("  {body}")));
    let index = crate::RejectionCause::ThrowingExpression {
        expression: "$(P[9])".to_string(),
    };
    assert!(
        !collected.is_empty() && collected.iter().all(|site| site.cause == index),
        "{collected:?}"
    );
}

/// A refusal a later write overwrote settles its name only to add sites, not
/// to lose one: `VersionLessThan('$(P)v1.0', '$(Q)')` throws on the values
/// the walk holds of `P` and `Q` (`""` and `bad`), whatever the arm leaves
/// unknown, and MSBuild throws on `Q`'s `nope` (MSB4184), so the walk
/// withdraws, in either walk (#1153, #1164).
#[test]
fn settling_a_refused_name_keeps_a_site_its_unknown_value_shows() {
    let body = format!(
        "<PropertyGroup><Q>bad</Q></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <PropertyGroup><P>abc</P><Q>nope</Q></PropertyGroup>\
         <ItemGroup><I Include=\"$([MSBuild]::VersionLessThan('$(P)v1.0','$(Q)'))\" /></ItemGroup>\
         </When></Choose>\
         <PropertyGroup><P>@(J)</P><P></P></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// Every site a group's judgement notes, from either walk, in place, each
/// cause in the rejection judgement's order: the first walk's in document
/// order, then the second walk's own. `$(P[9])$(Short[9])` is one text each
/// walk names a throw of (`$(Short[9])`, certain, in the first; `$(P[9])`,
/// holding the refused `P` at `z`, in the second); two items or one item's
/// `Include` and `Exclude`; two attributes throwing alike are two sites. The
/// evaluation's rejection is the first walk's first, certain (#1153).
#[test]
fn a_second_walks_sites_follow_the_first_walks() {
    let throw = |expression: &str| RejectionCause::ThrowingExpression {
        expression: expression.to_owned(),
    };
    for (items, sites) in [
        (
            "<I Include=\"$(P[9])$(Short[9])\" /><I Include=\"$(Short[9])\" />",
            vec!["$(Short[9])", "$(Short[9])", "$(P[9])"],
        ),
        (
            "<I Include=\"$(P[9])$(Short[9])\" Exclude=\"$(Short[9])\" />",
            vec!["$(Short[9])", "$(Short[9])", "$(P[9])"],
        ),
        (
            "<I Include=\"$(Short[9])\" Exclude=\"$(Short[9])\" />",
            vec!["$(Short[9])", "$(Short[9])"],
        ),
    ] {
        let body = format!(
            "<PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>\
             <ItemGroup>{items}</ItemGroup>"
        );
        for parsed in both_walkers(&format!("  {body}")) {
            assert_rejected(&parsed, &["Before", "After"]);
            let rejection = parsed.rejection.as_ref().expect("withdrawn");
            assert_eq!(rejection.cause, throw(sites[0]), "{items}: {rejection:#?}");
            assert_eq!(
                site_causes(&parsed),
                sites.iter().map(|site| throw(site)).collect::<Vec<_>>(),
                "{items}: {:#?}",
                parsed.diagnostics
            );
        }
    }
}

/// The causes of every site `parsed` notes, certain and possible, in order.
fn site_causes(parsed: &ParsedProject) -> Vec<RejectionCause> {
    parsed
        .diagnostics
        .iter()
        .filter_map(|d| match &d.kind {
            DiagnosticKind::Rejected { cause } | DiagnosticKind::MayBeRejected { cause } => {
                Some(cause.clone())
            }
            _ => None,
        })
        .collect()
}

/// Each site of one group is noted once, whichever walk finds it: the first
/// walk's in its order, then the second walk's own in theirs, and the first of
/// them is the evaluation's rejection (#1153). Every sequence of two or three
/// items, and every item with an `Include` and an `Exclude`, drawn from a text
/// both walks name alike (`$(Short[9])`) and one each walk names a throw of
/// apart (`$(P[9])$(Short[9])`: `$(Short[9])` in the first, `$(P[9])`, on the
/// refused `P`'s final `z`, in the second), in the entry project and in an
/// imported file, whose sites share one published span.
#[test]
fn sites_from_either_walk_are_each_noted_once() {
    #[derive(Clone, Copy, Debug)]
    enum Text {
        Alike,
        Apart,
    }
    let expression = |text: Text| match text {
        Text::Alike => "$(Short[9])",
        Text::Apart => "$(P[9])$(Short[9])",
    };
    let all = [Text::Alike, Text::Apart];
    let mut cases: Vec<(String, Vec<Text>)> = Vec::new();
    for a in all {
        for b in all {
            let include = |t: Text| format!("<I Include=\"{}\" />", expression(t));
            cases.push((format!("{}{}", include(a), include(b)), vec![a, b]));
            cases.push((
                format!(
                    "<I Include=\"{}\" Exclude=\"{}\" />",
                    expression(a),
                    expression(b)
                ),
                vec![a, b],
            ));
            for c in all {
                cases.push((
                    format!("{}{}{}", include(a), include(b), include(c)),
                    vec![a, b, c],
                ));
            }
        }
    }
    let throw = |expression: &str| RejectionCause::ThrowingExpression {
        expression: expression.to_owned(),
    };
    let mut adopted = 0;
    for (items, texts) in cases {
        let group = format!(
            "<PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>\
             <ItemGroup>{items}</ItemGroup>"
        );
        // The first walk names `$(Short[9])` in every text, the second walk
        // `$(P[9])` too in each text apart.
        let expected: Vec<RejectionCause> = texts
            .iter()
            .map(|_| throw("$(Short[9])"))
            .chain(
                texts
                    .iter()
                    .filter(|t| matches!(t, Text::Apart))
                    .map(|_| throw("$(P[9])")),
            )
            .collect();
        let tmp = TempDir::new().unwrap();
        let imported = project(
            &tmp,
            "  <Import Project=\"inner.props\" />",
            &[("proj/inner.props", &format!("<Project>{group}</Project>"))],
        );
        let ((entry, imported), collected) = crate::test_support::second_walk_sites(|| {
            (both_walkers(&format!("  {group}")), parse_file(&imported))
        });
        adopted += collected.len();
        for (place, parsed) in [
            ("entry", &entry[0]),
            ("pure", &entry[1]),
            ("imported", &imported),
        ] {
            assert_eq!(
                site_causes(parsed),
                expected,
                "{place} {items}: {:#?}",
                parsed.diagnostics
            );
            assert_eq!(
                parsed.rejection.as_ref().map(|r| &r.cause),
                expected.first(),
                "{place} {items}"
            );
        }
    }
    assert!(adopted > 0, "no case adopts a second walk's site");
}

/// In an arm the walk does not take, each walk names the first throw of a
/// text on values MSBuild may hold: `$(P[9])`, on the `z` the walk holds of
/// `P`, which the arm writes and a refused write precedes, though MSBuild's
/// value there may be the arm's. The two walks name it alike, so it is noted
/// once, and `$(Short[9])` after it in the same text is not (#1153, #1164).
#[test]
fn in_an_untaken_arm_each_walk_names_the_first_throw_on_values_held() {
    let body = format!(
        "<PropertyGroup><P>abc</P><Short>a</Short></PropertyGroup>\
         <Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
         <ItemGroup><I Include=\"$(P[9])$(Short[9])\" /></ItemGroup>\
         </When></Choose>\
         <PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup>"
    );
    let throw = |expression: &str| RejectionCause::ThrowingExpression {
        expression: expression.to_owned(),
    };
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(
            site_causes(&parsed),
            [throw("$(P[9])")],
            "{:#?}",
            parsed.diagnostics
        );
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// No second walk where its reading cannot differ: the refused `P` is
/// rewritten, but the judgement reads it only in a gate, which both walks
/// decide as main does, so the first walk never reads `P` where the second
/// would hold it certain, and the evaluation is walked once; its certain throw
/// is one site (#1153).
#[test]
fn no_second_walk_where_its_reading_cannot_differ() {
    let body = format!(
        "<PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>\
         <Choose><When Condition=\"{UNDECIDED_TRUE}\"><Choose>\
         <When Condition=\"'$(P)' == 'off'\"><ItemGroup><I Include=\"x\" /></ItemGroup></When>\
         </Choose></When></Choose>\
         <ItemGroup><K Include=\"$(Short[9])\" /></ItemGroup>"
    );
    let (parsed, costs) =
        crate::test_support::count_walk_costs(|| both_walkers(&format!("  {body}")));
    assert_eq!(costs.second_walks, 0, "{costs:?}");
    for parsed in parsed {
        let sites = parsed
            .diagnostics
            .iter()
            .filter(|d| {
                matches!(
                    d.kind,
                    DiagnosticKind::Rejected { .. } | DiagnosticKind::MayBeRejected { .. }
                )
            })
            .count();
        assert_eq!(sites, 1, "{:#?}", parsed.diagnostics);
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// A site only the second walk finds in an SDK's `Sdk.props` or
/// `Sdk.targets` is noted, after every site the first walk notes, in the
/// SDK's file and in the project's body: the first walk names `$(Short[9])`
/// of the SDK's text, the second `$(P[9])`, holding the refused `P` at `z`.
/// The evaluation's rejection is the first walk's certain site (#1153).
#[test]
fn a_second_walks_site_in_an_sdks_file_is_noted() {
    let site = "<Project><ItemGroup><I Include=\"$(P[9])$(Short[9])\" /></ItemGroup></Project>";
    let throw = |expression: &str| RejectionCause::ThrowingExpression {
        expression: expression.to_owned(),
    };
    // The project body's own site, `$(Short[9])` in an arm the walk does not
    // take, comes after `Sdk.props` and before `Sdk.targets`.
    for (props, targets, expected) in [
        (
            "<Project></Project>",
            site,
            [throw("$(Short[9])"), throw("$(Short[9])"), throw("$(P[9])")],
        ),
        (
            site,
            "<Project></Project>",
            [throw("$(Short[9])"), throw("$(Short[9])"), throw("$(P[9])")],
        ),
    ] {
        let tmp = TempDir::new().unwrap();
        let (sdk_dir, props_path, targets_path) =
            write_synthetic_sdk(tmp.path(), "Order.Sdk", props, targets);
        let project_path = write_at(
            tmp.path(),
            "Demo.fsproj",
            &format!(
                "<Project Sdk=\"Order.Sdk\"><PropertyGroup><Short>a</Short></PropertyGroup>\
                 <ItemGroup><J Include=\"1.0\" /></ItemGroup>\
                 <Choose><When Condition=\"{UNDECIDED_TRUE}\">\
                 <ItemGroup><K Include=\"$(Short[9])\" /></ItemGroup></When></Choose>\
                 <PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup></Project>"
            ),
        );
        let parsed = parse_file_with_sdk(&project_path, |_| {
            Ok(SdkPaths {
                root: sdk_dir.clone(),
                props: props_path.clone(),
                targets: targets_path.clone(),
            })
        });
        assert_eq!(site_causes(&parsed), expected, "{:#?}", parsed.diagnostics);
        let rejection = parsed.rejection.as_ref().expect("withdrawn");
        assert_eq!(rejection.certainty, RejectionCertainty::Certain);
        assert_eq!(rejection.cause, throw("$(Short[9])"));
    }
}

/// Two files' constructs at one span are two sites: `x.props` and
/// `y.props` lay out one text alike, `$(P[9])$(Short[9])`, which only the
/// second walk names by `$(P[9])` (the first names the certain
/// `$(Short[9])`). Each is noted, at its own import (#1153).
#[test]
fn constructs_of_two_files_at_one_span_are_two_sites() {
    let file = "<Project><ItemGroup><I Include=\"$(P[9])$(Short[9])\" /></ItemGroup></Project>";
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <Import Project=\"x.props\" /><Import Project=\"y.props\" />\
         <PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>",
        &[("proj/x.props", file), ("proj/y.props", file)],
    );
    let parsed = parse_file(&project_path);
    let item = RejectionCause::ThrowingExpression {
        expression: "$(P[9])".to_owned(),
    };
    let spans: BTreeSet<_> = parsed
        .diagnostics
        .iter()
        .filter(|d| matches!(&d.kind, DiagnosticKind::MayBeRejected { cause } if *cause == item))
        .map(|d| (d.span.start, d.span.end))
        .collect();
    assert_eq!(spans.len(), 2, "{:#?}", parsed.diagnostics);
}

/// One cause in two texts of an element is two sites: the first walk notes
/// `$(P[9])` in the `Exclude` alone (in the `Include` it names the certain
/// `$(Short[9])`), the second in both, and both are noted (#1153).
#[test]
fn one_cause_in_two_texts_of_an_element_is_two_sites() {
    let body = "<PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>\
                <ItemGroup><I Include=\"$(P[9])$(Short[9])\" Exclude=\"$(P[9])\" /></ItemGroup>";
    let cause = RejectionCause::ThrowingExpression {
        expression: "$(P[9])".to_owned(),
    };
    for parsed in both_walkers(&format!("  {body}")) {
        let noted = site_causes(&parsed).iter().filter(|c| **c == cause).count();
        assert_eq!(noted, 2, "{:#?}", parsed.diagnostics);
    }
}

/// The entry project's buffer and a document opened from its file are two
/// files to a site: `link.props`, a link to the project's own file, holds the
/// project's text, and its item's `$(P[9])$(Short[9])`, which only the second
/// walk names by `$(P[9])`, is noted in each (#1153).
#[cfg(unix)]
#[test]
fn the_entry_buffer_and_its_file_opened_again_are_two_files() {
    let tmp = TempDir::new().unwrap();
    let body = "  <ItemGroup><I Include=\"$(P[9])$(Short[9])\" /></ItemGroup>\
                <Import Project=\"link.props\" />\
                <PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>";
    let project_path = project(&tmp, body, &[]);
    std::os::unix::fs::symlink(&project_path, tmp.path().join("proj/link.props")).unwrap();
    let parsed = parse_file(&project_path);
    let item = RejectionCause::ThrowingExpression {
        expression: "$(P[9])".to_owned(),
    };
    let noted = parsed
        .diagnostics
        .iter()
        .filter(|d| matches!(&d.kind, DiagnosticKind::MayBeRejected { cause } if *cause == item))
        .count();
    assert_eq!(noted, 2, "{:#?}", parsed.diagnostics);
}

/// What MSBuild reaches is main's to decide in either walk: the walk doubts
/// the refused `P` in the group's gate, so either walk judges the group, and
/// in it the write to `R` under the same gate, which neither decides, leaves
/// `R` uncertain, and `$(R[9])` throws on the `a` the walk holds from before
/// the group: a Possible site in either walk, though MSBuild skips the group
/// and evaluates the project. A decline (#1153, #1164, #1200), never a claim.
#[test]
fn a_skipped_group_the_walk_doubts_is_judged_on_the_value_before_it() {
    let body = "<PropertyGroup><P>@(J)</P><P>z</P><R>a</R></PropertyGroup>\
                <PropertyGroup Condition=\"'$(P)' == 'off'\">\
                <R Condition=\"'$(P)' == 'off'\">abcdefghijkl</R><T>$(R[9])</T></PropertyGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// Which of a text's throws a walk names is the judgement's to decide: the
/// first walk names `$(S[9])`, certain, and the second `$(P[9])`, the one
/// MSBuild reports, holding the refused `P` at `z`; both are noted (#1153).
#[test]
fn the_second_walk_names_the_throw_its_reading_reaches_first() {
    let body = "<PropertyGroup><P>@(J)</P><P>z</P><S>a</S><T>$(P[9])$(S[9])</T></PropertyGroup>";
    let throw = |expression: &str| RejectionCause::ThrowingExpression {
        expression: expression.to_owned(),
    };
    for parsed in both_walkers(&format!("  {body}")) {
        assert_rejected(&parsed, &["Before", "After"]);
        assert_eq!(
            parsed.rejection.as_ref().map(|r| &r.cause),
            Some(&throw("$(S[9])"))
        );
        assert!(
            parsed.diagnostics.iter().any(|d| matches!(
                &d.kind,
                DiagnosticKind::MayBeRejected { cause } if *cause == throw("$(P[9])")
            )),
            "{:#?}",
            parsed.diagnostics
        );
    }
}

/// Nor where the throw that reads the rewritten name is reached only
/// perhaps: then either walk names the first throw it holds, whatever its
/// reading, so the evaluation is walked once (#1153).
#[test]
fn no_second_walk_for_a_throw_reached_perhaps() {
    let body = format!(
        "<PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup>\
         <PropertyGroup Condition=\"{UNDECIDED_TRUE}\"><T>$(P[9])</T></PropertyGroup>"
    );
    let (parsed, costs) =
        crate::test_support::count_walk_costs(|| both_walkers(&format!("  {body}")));
    assert_eq!(costs.second_walks, 0, "{costs:?}");
    for parsed in parsed {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// Nor where the second walk would name the throw the first does: one held
/// throw on the rewritten name, reached for certain, is the pick of either
/// walk, and only its certainty, which adoption discards, could differ
/// (#1153).
#[test]
fn no_second_walk_where_it_names_the_same_throw() {
    let body = "<PropertyGroup><P>@(J)</P><P>z</P><T>$(P[9])</T></PropertyGroup>";
    let (parsed, costs) =
        crate::test_support::count_walk_costs(|| both_walkers(&format!("  {body}")));
    assert_eq!(costs.second_walks, 0, "{costs:?}");
    for parsed in parsed {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// Adopting the second walk's sites is linear in the sites: one count for
/// each of the first walk's, one lookup for each of the second's (#1153).
/// Each of 600 items' text is named apart by the two walks
/// ([`a_second_walks_sites_follow_the_first_walks`]), so each walk notes 600.
#[test]
fn adopting_a_second_walks_sites_is_linear_in_them() {
    let items: String = (0..600)
        .map(|_| "<I Include=\"$(P[9])$(Short[9])\" />")
        .collect();
    let body = format!(
        "<PropertyGroup><P>@(J)</P><P>z</P><Short>a</Short></PropertyGroup>\
         <ItemGroup>{items}</ItemGroup>"
    );
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, &format!("  {body}"), &[]);
    let text = host_fs::read_to_string(&project_path).unwrap();
    let (parsed, costs) = crate::test_support::count_walk_costs(|| {
        parse_fsproj(
            &crate::ProjectFile::buffer(&project_path, &text)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &HashMap::new(),
        )
        .unwrap()
    });
    assert_eq!(site_causes(&parsed).len(), 1200, "{:#?}", parsed.rejection);
    assert_eq!(costs.second_walks, 1);
    // Each of the first walk's 600 sites counted, each of the second's 600
    // looked up.
    let bound = 600 + 600;
    assert!(
        costs.site_merge_probes <= bound,
        "{} probes, over {bound}",
        costs.site_merge_probes
    );
}

/// A write whose gate is certainly false on the path writes nothing there:
/// `P` is still `a`, which has no index 9.
#[test]
fn a_write_under_a_false_gate_leaves_its_name_as_it_was() {
    let body = format!(
        "<PropertyGroup><P>a</P></PropertyGroup><PropertyGroup Condition=\"{UNDECIDED_TRUE}\">\
         <P Condition=\"false\">abcdefghijkl</P><Q>$(P[9])</Q></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// An inline task's `Evaluate` holding an item list is one the walk does not
/// expand: `@(Flag)` is `false` to MSBuild, which then skips the body, so a
/// throw in the body is no certain rejection.
#[test]
fn an_evaluate_flag_holding_an_item_list_reaches_the_body_perhaps() {
    let body = "<PropertyGroup><P>a</P></PropertyGroup><ItemGroup><Flag Include=\"false\" /></ItemGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task Evaluate=\"@(Flag)\">$(P[9])</Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_ne!(
            parsed.rejection.as_ref().map(|r| r.certainty),
            Some(RejectionCertainty::Certain),
            "{body}: {:#?}",
            parsed.rejection
        );
    }
}

/// A condition of the property pass reads an item list its properties'
/// values form as text: `'$(A)$(B)' != ''` is true, `@(I)` being no empty
/// text (probed, `msbuild-condition-oracle`, SDK 10.0.401).
#[test]
fn an_item_list_formed_in_a_property_condition_is_text() {
    let body = "<PropertyGroup><A>@</A><B>(I)</B><R Condition=\"'$(A)$(B)' != ''\">yes</R></PropertyGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
        assert_eq!(parsed.property("R").value(), Some("yes"), "{body}");
    }
}

/// An inline task's body holding an element is its inner XML as serialized:
/// a plain reference in an attribute (`<Reference Include="$(Lib)" />`) is
/// no throw, as in any declaration that names a library by a property.
#[test]
fn a_plain_reference_in_an_inline_task_attribute_is_no_throw() {
    let body = "<PropertyGroup><Lib>abc.dll</Lib></PropertyGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task><Reference Include=\"$(Lib)\" /><Code Type=\"Fragment\" Language=\"cs\">x</Code></Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
    }
}

/// An inline task's `Evaluate` flag is read as `Boolean.TryParse` reads it,
/// which takes `false` padded with NULs as with whitespace: the body is then
/// not expanded, and its throw is none.
#[test]
fn an_evaluate_flag_padded_with_a_nul_is_false() {
    let task = |flag: &str| {
        format!(
            "<PropertyGroup><P>x</P><N>%00</N></PropertyGroup>\
             <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
             <Task Evaluate=\"{flag}\">$(P[9])</Task></UsingTask>"
        )
    };
    let padded = task("false$(N[0])");
    for parsed in both_walkers(&format!("  {padded}")) {
        assert_eq!(
            parsed.rejection, None,
            "{padded}: {:#?}",
            parsed.diagnostics
        );
    }
    let evaluated = task("true$(N[0])");
    for parsed in both_walkers(&format!("  {evaluated}")) {
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// A property's or metadatum's body holding an element is its inner XML,
/// which MSBuild expands like any other body: a throw in it rejects the
/// project, and the same body with an index in range does not.
#[test]
fn an_element_valued_body_is_judged_as_its_inner_xml() {
    let sites = [
        "<PropertyGroup><Q><Data>$(P[INDEX])</Data></Q></PropertyGroup>",
        "<ItemGroup><I Include=\"a\"><M><Data>$(P[INDEX])</Data></M></I></ItemGroup>",
        "<ItemDefinitionGroup><I><M><Data>$(P[INDEX])</Data></M></I></ItemDefinitionGroup>",
    ];
    for site in sites {
        let throwing = format!(
            "<PropertyGroup><P>x</P></PropertyGroup>{}",
            site.replace("INDEX", "9")
        );
        for parsed in both_walkers(&format!("  {throwing}")) {
            assert_rejected(&parsed, &["Before", "After"]);
        }
        let in_range = format!(
            "<PropertyGroup><P>x</P></PropertyGroup>{}",
            site.replace("INDEX", "0")
        );
        for parsed in both_walkers(&format!("  {in_range}")) {
            assert_eq!(
                parsed.rejection, None,
                "{in_range}: {:#?}",
                parsed.diagnostics
            );
        }
    }
}

/// An inline task written with Windows line ends is read as MSBuild reads it:
/// its whitespace nodes, carriage returns and all, are dropped, and a plain
/// reference in an attribute is no throw.
#[test]
fn an_inline_task_with_windows_line_ends_is_serialized() {
    let body = "<PropertyGroup><Lib>abc.dll</Lib></PropertyGroup>\r\n\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\r\n\
                <Task>\r\n  <Reference Include=\"$(Lib)\" />\r\n  \
                <Code Type=\"Fragment\" Language=\"cs\"><![CDATA[x]]></Code>\r\n</Task>\r\n</UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
    }
}

/// Code written as an element's text over several lines is serialized as
/// read, its line ends included: an expression in it is judged, a throw for
/// certain and a plain reference as none.
#[test]
fn an_inline_tasks_code_over_several_lines_is_judged() {
    let task = |code: &str| {
        format!(
            "<PropertyGroup><P>abc</P></PropertyGroup>\
             <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
             <Task>\n  <Code Type=\"Fragment\" Language=\"cs\">\n    {code}\n  </Code>\n</Task></UsingTask>"
        )
    };
    let throwing = task("Log.LogMessage(\"$(P[9])\");");
    for parsed in both_walkers(&format!("  {throwing}")) {
        assert_rejected(&parsed, &["Before", "After"]);
    }
    let plain = task("Log.LogMessage(\"$(P)\");");
    for parsed in both_walkers(&format!("  {plain}")) {
        assert_eq!(parsed.rejection, None, "{plain}: {:#?}", parsed.diagnostics);
    }
}

/// An item group from content the walk does not take is judged knowing the
/// writes of its whole path, those after it included: MSBuild evaluates it
/// after every property write there, when `P` is long enough to index, so
/// nothing reading `P` there is certain. A throw on the `x` the walk holds is
/// a Possible site all the same, a decline (#1164, #1200).
#[test]
fn an_untaken_branchs_items_know_the_writes_after_them() {
    let body = format!(
        "<PropertyGroup><P>x</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <ItemGroup><I Include=\"$(P[4])\" /></ItemGroup>\
         <PropertyGroup><P>long enough</P></PropertyGroup></When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// An item group from content the walk does not take knows only the writes
/// that can reach it: one in another arm of a `<Choose>` that holds it is
/// none. MSBuild takes the `<Otherwise>` here, where `P` is short, and
/// rejects; the long `P` of the `<When>` beside it never reaches the item.
#[test]
fn an_untaken_branchs_items_know_no_write_of_a_sibling_arm() {
    let body = format!(
        "<PropertyGroup><P>x</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <Choose><When Condition=\"'É' == 'Ê'\"><PropertyGroup><P>long enough</P></PropertyGroup></When>\
         <Otherwise><ItemGroup><I Include=\"$(P[9])\" /></ItemGroup></Otherwise></Choose>\
         </When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// The values an expression on an unheld name is tried as returning include
/// the hyphen a prerelease version joins with: `1$(X)preview` is `1-preview`
/// for MSBuild's `X`, a version, so the walk claims no throw on it.
#[test]
fn a_prerelease_spelling_is_among_the_values_tried() {
    let body = "<PropertyGroup><X>$([System.String]::Copy('-'))</X>\
                <R>$([MSBuild]::VersionLessThan('1$(X)preview', '2.0'))</R></PropertyGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
    }
}

/// An inline task's body that starts with a CDATA section is its inner text,
/// an element's included: `$(P[9])` here, which MSBuild throws on, for
/// certain.
#[test]
fn a_task_body_leading_with_cdata_is_its_inner_text() {
    let body = "<PropertyGroup><P>x</P></PropertyGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task><![CDATA[$]]><Code>(P[9])</Code></Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// An inline task's body nested past the bound the serialization descends
/// to (so that a deep body cannot take the stack) declines: a throw in it is
/// a possible rejection, not a certain one.
#[test]
fn a_task_body_nested_past_the_bound_declines() {
    let body = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup>\
         <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
         <Task>{}$(P[9]){}</Task></UsingTask>",
        "<a>".repeat(100),
        "</a>".repeat(100)
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// A CDATA section in an element of an inline task's body is serialized as
/// one, so an expression in it is judged, for certain where it is reached
/// for certain.
#[test]
fn an_expression_in_a_task_bodys_cdata_section_is_judged() {
    let body = "<PropertyGroup><P>abc</P></PropertyGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task><Code><![CDATA[$(P[9])]]></Code></Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// The inner text of a body that starts with a CDATA section drops a
/// whitespace node between its sections, as MSBuild's reader does: the
/// separator set here is `;` alone, and `a b` has no second element.
#[test]
fn a_task_bodys_inner_text_drops_whitespace_nodes() {
    let body = "<PropertyGroup><S>a b</S></PropertyGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task><![CDATA[$(S.Split(']]><Code> </Code><![CDATA[;')[1])]]></Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_rejected(&parsed, &["Before", "After"]);
    }
}

/// An inline task's body in the project's own namespace, as most `.targets`
/// declare it, is serialized with the declaration, which holds no
/// expression: a plain reference in an attribute is no throw.
#[test]
fn an_inline_task_in_the_msbuild_namespace_is_serialized() {
    let tmp = TempDir::new().unwrap();
    let project_path = write_at(
        tmp.path(),
        "proj/p.fsproj",
        "<Project xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">\
         <PropertyGroup><Lib>a.dll</Lib></PropertyGroup>\
         <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
         <Task><Reference Include=\"$(Lib)\" /><Code Type=\"Fragment\" Language=\"cs\">x</Code></Task></UsingTask>\
         <PropertyGroup><After>1</After></PropertyGroup></Project>",
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
}

/// A metadatum's value substituted into another's text may move where an
/// expression starts (`%(M)` holding `$(`), so a throw in such text is no
/// certain rejection.
#[test]
fn a_throw_beside_a_metadata_reference_is_no_certain_rejection() {
    let body = "<PropertyGroup><P>abc</P></PropertyGroup>\
                <ItemDefinitionGroup><I><M>$(</M><N>%(M)abc$(P[9])</N></I></ItemDefinitionGroup>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_ne!(
            parsed.rejection.as_ref().map(|r| r.certainty),
            Some(RejectionCertainty::Certain),
            "{body}: {:#?}",
            parsed.rejection
        );
    }
}

/// An inline task's body the walk cannot read as MSBuild does (a carriage
/// return in a text, whose line end `roxmltree` folds and MSBuild's reader
/// keeps) is checked for an expression across its markup, as its inner text
/// joins it: `$` and `(P[9])` in separate pieces still form one.
#[test]
fn a_task_body_read_apart_is_checked_across_its_markup() {
    let body = "<PropertyGroup><P>abc</P></PropertyGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task><![CDATA[$]]><Code>(P[9])\r</Code></Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_withdrawn(&parsed, &["Before", "After"]);
    }
}

/// Under `xml:space="preserve"` MSBuild keeps the whitespace the walk would
/// drop from an inline task's inner text, so the walk declines that reading
/// rather than claim a throw it would form without the space.
#[test]
fn a_task_body_under_xml_space_is_no_certain_rejection() {
    let body = "<PropertyGroup><P>abc</P></PropertyGroup>\
                <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                <Task><![CDATA[$]]><Code xml:space=\"preserve\"> </Code><![CDATA[(P[9])]]></Task></UsingTask>";
    for parsed in both_walkers(&format!("  {body}")) {
        assert_ne!(
            parsed.rejection.as_ref().map(|r| r.certainty),
            Some(RejectionCertainty::Certain),
            "{body}: {:#?}",
            parsed.rejection
        );
    }
}
