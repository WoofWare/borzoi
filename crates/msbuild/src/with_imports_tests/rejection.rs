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

/// Whether the walk published nothing as the build's: the facets and reads a
/// rejected evaluation withdraws.
fn assert_withdrawn(parsed: &ParsedProject, names: &[&str]) {
    let rejection = parsed
        .rejection
        .as_ref()
        .unwrap_or_else(|| panic!("no rejection: {:#?}", parsed.diagnostics));
    assert_eq!(rejection.certainty, RejectionCertainty::Possible);
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
    let may_be_rejected =
        |kind: &DiagnosticKind| matches!(kind, DiagnosticKind::MayBeRejected { .. });
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
fn a_decided_import_of_a_missing_file_may_be_rejected() {
    // #845: MSB4019. What the walk bound before the import is no more the
    // build's than what it bound after.
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, "  <Import Project=\"missing.props\" />", &[]);
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
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
fn a_decided_import_of_a_dangling_link_may_be_rejected() {
    // #845's reproduction, imported unconditionally: MSB4019.
    let tmp = TempDir::new().unwrap();
    let project_path = project(&tmp, "  <Import Project=\"alias.targets\" />", &[]);
    std::os::unix::fs::symlink(
        "../Directory.Build.targets",
        tmp.path().join("proj/alias.targets"),
    )
    .unwrap();
    assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
}

#[test]
fn an_import_with_an_empty_project_may_be_rejected() {
    // MSB4035 / MSB4020.
    for import in [
        "<Import Project=\"\" />",
        "<Import Project=\"$(Nothing)\" />",
        "<Import />",
    ] {
        let tmp = TempDir::new().unwrap();
        let project_path = project(&tmp, &format!("  {import}"), &[]);
        assert_withdrawn(&parse_file(&project_path), &["Before", "After"]);
    }
}

#[test]
fn an_sdk_import_of_a_missing_file_may_be_rejected() {
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
    assert_withdrawn(&parsed, &["Before", "After"]);
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
