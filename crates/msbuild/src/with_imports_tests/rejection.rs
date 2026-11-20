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
/// unknown to what follows on that path: `P` is `abc` by the time `Q` reads
/// it there, which has an index 1, though the walk holds `a`. That MSBuild
/// throws on such a value is the judgement over the values a name may hold
/// (#1097), not a judgement on the value the walk holds.
#[test]
fn a_write_in_untaken_content_leaves_its_name_unknown_there() {
    let body = format!(
        "<PropertyGroup><P>a</P></PropertyGroup><PropertyGroup Condition=\"{UNDECIDED_TRUE}\"><P>abc</P><Q>$(P[1])</Q></PropertyGroup>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
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
/// enough to index there, though the final table holds `abc`. A throw on the
/// value the walk holds is no site.
#[test]
fn an_untaken_branchs_items_know_the_writes_before_them() {
    let body = format!(
        "<PropertyGroup><P>abc</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
         <ItemGroup><I Include=\"$(P[9])\" /></ItemGroup></When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
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

/// An item group from content the walk does not take is judged knowing the
/// writes of its whole path, those after it included: MSBuild evaluates it
/// after every property write there, when `P` is long enough to index.
#[test]
fn an_untaken_branchs_items_know_the_writes_after_them() {
    let body = format!(
        "<PropertyGroup><P>x</P></PropertyGroup><Choose><When Condition=\"{UNDECIDED_TRUE}\">\
         <ItemGroup><I Include=\"$(P[4])\" /></ItemGroup>\
         <PropertyGroup><P>long enough</P></PropertyGroup></When></Choose>"
    );
    for parsed in both_walkers(&format!("  {body}")) {
        assert_eq!(parsed.rejection, None, "{body}: {:#?}", parsed.diagnostics);
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
