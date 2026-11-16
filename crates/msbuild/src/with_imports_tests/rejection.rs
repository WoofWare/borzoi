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
const UNDECIDED_TRUE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";

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
fn an_undecided_import_of_a_wildcard_is_not_rejected() {
    // A wildcard that matches nothing imports nothing, silently.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        &format!("  <Import Project=\"none/*.props\" Condition=\"{UNDECIDED_TRUE}\" />"),
        &[],
    );
    let parsed = parse_file(&project_path);
    assert_eq!(parsed.rejection, None, "{:#?}", parsed.diagnostics);
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
    let pure = parse_fsproj(&text, &project_path, &HashMap::new(), &HashMap::new()).unwrap();
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
    let pure = parse_fsproj(&text, &project_path, &HashMap::new(), &HashMap::new()).unwrap();
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
    // Imported through a path the walk does not name for certain (a `\` a
    // property supplies, #903): MSBuild may load another file.
    let tmp = TempDir::new().unwrap();
    let project_path = project(
        &tmp,
        "  <PropertyGroup><P>sub\\refused.props</P></PropertyGroup>\n  <Import Project=\"$(P)\" />",
        &[("proj/sub/refused.props", refused)],
    );
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}
