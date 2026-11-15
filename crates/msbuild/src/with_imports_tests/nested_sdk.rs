//! Nested SDK roots declared by imported files, and the `Directory.Build.props`
//! import point their `Sdk.props` holds.

use super::*;
use tempfile::TempDir;

// -------------------------------------------------------------------------
// Nested SDK roots inside imported files
// -------------------------------------------------------------------------

#[test]
fn nested_sdk_props_runs_before_imported_file_body() {
    // An imported file that declares `<Project Sdk="X">` should get
    // the same splice as a root-Sdk entry project: `Sdk.props` runs
    // before the imported file's body, so a property the SDK sets is
    // visible to a `$(...)` reference inside the imported body.
    // Without nested-SDK splicing the body's `$(SdkSeed)` would be
    // undefined and we'd produce a garbage item path.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        r#"<Project>
  <PropertyGroup>
    <SdkSeed>fromprops</SdkSeed>
  </PropertyGroup>
</Project>"#,
        "<Project/>",
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="$(SdkSeed).fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    assert_eq!(paths_of(&result.items), vec![dir.join("fromprops.fs")]);
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| matches!(d.kind, DiagnosticKind::UndefinedProperty { .. })),
        "$(SdkSeed) should resolve from nested Sdk.props, no UndefinedProperty expected: {:?}",
        result.diagnostics,
    );
}

#[test]
fn nested_sdk_targets_runs_after_imported_file_body() {
    // The other half of the splice: `Sdk.targets` of a nested SDK
    // root runs *after* the imported file's body. Items it
    // contributes therefore appear later in document order than
    // items the imported body itself declares. Pins the
    // [body, targets] ordering — without targets-splicing we'd lose
    // `last.fs` entirely; with mis-ordered splicing we'd see it
    // before the body's items.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        "<Project/>",
        r#"<Project>
  <ItemGroup>
    <Compile Include="last.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    assert_eq!(
        paths_of(&result.items),
        vec![dir.join("nested-body.fs"), dir.join("last.fs")],
    );
}

#[test]
fn nested_sdk_items_carry_entry_import_site_span() {
    // Items contributed by a nested SDK's `Sdk.props` must collapse
    // to the *entry* project's `<Import>` element span — that's the
    // standing import-site span contract for any item coming from an
    // imported file or any file transitively reached from it. Without
    // it, the LSP would point users at a phantom span in a file they
    // can't edit.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-sdk-props.fs" />
  </ItemGroup>
</Project>"#,
        "<Project/>",
    );
    write_at(tmp.path(), "nested.targets", r#"<Project Sdk="MySdk" />"#);
    let project_source = r#"<Project>
  <Import Project="nested.targets" />
</Project>"#;
    let project_path = write_at(tmp.path(), "Demo.fsproj", project_source);
    let result = parse_with_sdk(&project_path, project_source, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let import_start = project_source.find("<Import").unwrap();
    let import_end = project_source[import_start..].find("/>").unwrap() + import_start + 2;
    let item = result
        .items
        .iter()
        .find(|i| {
            i.include
                .file_name()
                .is_some_and(|n| n == "from-sdk-props.fs")
        })
        .expect("from-sdk-props.fs should appear in items");
    assert_eq!(
        item.span,
        import_start..import_end,
        "nested SDK items must collapse to the entry project's <Import> site",
    );
}

#[test]
fn nested_sdk_resolver_error_surfaces_as_sdk_not_found() {
    // The new path routes nested SDK resolution through the same
    // `resolve_project_sdk` the entry project uses, so resolver-side
    // errors map to the same diagnostic kinds. Previously we just
    // diagnosed *any* SDK attribute on an imported root as
    // `UnsupportedConstruct`, losing the distinction between "we
    // don't know how to resolve SDKs" and "the resolver looked and
    // it isn't there". Witness that an `Err(NotFound)` from the
    // resolver now reaches the caller as `SdkNotFound` with origin
    // `Imported` (so LSP consumers can suppress it if they choose).
    let tmp = TempDir::new().unwrap();
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="DoesNotExist" />"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |_name| Err(SdkResolveError::NotFound));
    let sdk_not_found: Vec<_> = result
        .diagnostics
        .iter()
        .filter(
            |d| matches!(&d.kind, DiagnosticKind::SdkNotFound { name } if name == "DoesNotExist"),
        )
        .collect();
    assert_eq!(
        sdk_not_found.len(),
        1,
        "expected exactly one SdkNotFound for the nested SDK, got: {:?}",
        result.diagnostics,
    );
    assert_eq!(
        sdk_not_found[0].origin,
        DiagnosticOrigin::Imported,
        "diagnostic from a nested file must carry Imported origin",
    );
    assert!(result.is_partial);
}

#[test]
fn a_nested_sdk_imports_directory_build_props_once() {
    // The nested SDK's `Sdk.props` holds the import point, so
    // `Directory.Build.props` is imported there, once: a second import of
    // the file would double-count any items it contributes.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(tmp.path(), "nested.targets", r#"<Project Sdk="MySdk" />"#);
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dirbuild_count = result
        .items
        .iter()
        .filter(|i| {
            i.include
                .file_name()
                .is_some_and(|n| n == "from-dirbuild.fs")
        })
        .count();
    assert_eq!(
        dirbuild_count,
        1,
        "Directory.Build.props should walk exactly once, got: {:?}",
        paths_of(&result.items),
    );
}

#[test]
fn entry_no_sdk_nested_sdk_props_visible_to_directory_build_props() {
    // MSBuild imports `Directory.Build.props` exactly once, at the import
    // point of the *first* `Sdk.props` to run. When the entry project has
    // no resolvable SDK but a nested imported file does, that first
    // `Sdk.props` is the nested one (mid-body), so `Directory.Build.props`
    // runs inside it, after the property the nested SDK sets: a
    // `Directory.Build.props` that conditions on (or substitutes) that
    // property sees it.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        &format!(
            "<Project>\n  <PropertyGroup>\n    <NestedFlag>yes</NestedFlag>\n  </PropertyGroup>\n{COMMON_PROPS_BLOCK}</Project>"
        ),
        "<Project/>",
    );
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <PropertyGroup>
    <Saw>$(NestedFlag)</Saw>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="$(Saw).fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    let paths = paths_of(&result.items);
    assert!(
        paths.contains(&dir.join("yes.fs")),
        "Directory.Build.props must run after the nested Sdk.props so $(NestedFlag) is visible; got: {paths:?}",
    );
    assert!(
        !paths.contains(&dir.join(".fs")),
        "an empty $(Saw) (`.fs`) means Directory.Build.props ran before the nested Sdk.props; got: {paths:?}",
    );
}

#[test]
fn a_project_with_no_sdk_anywhere_imports_no_directory_build_props() {
    // Only an SDK's `Microsoft.Common.props` imports `Directory.Build.props`,
    // so with no SDK anywhere MSBuild never reads it (#676).
    let tmp = TempDir::new().unwrap();
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <ItemGroup>
    <Compile Include="body.fs" />
  </ItemGroup>
</Project>"#,
    );
    // Resolver present but irrelevant: there is no SDK anywhere.
    let result = parse_file_with_sdk(&project_path, |_name| Err(SdkResolveError::NotFound));
    let dir = canon(tmp.path());
    assert_eq!(
        paths_of(&result.items),
        vec![dir.join("body.fs")],
        "no SDK imports Directory.Build.props, so only the body's item is there",
    );
}

#[test]
fn directory_build_props_at_a_nested_sdk_is_imported_once() {
    // The nested `Sdk.props` imports `Directory.Build.props` at its import
    // point, once: the sentinel item from `Directory.Build.props` must appear
    // exactly once.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        &format!(
            "<Project>\n  <PropertyGroup>\n    <NestedFlag>yes</NestedFlag>\n  </PropertyGroup>\n{COMMON_PROPS_BLOCK}</Project>"
        ),
        "<Project/>",
    );
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dirbuild_count = result
        .items
        .iter()
        .filter(|i| {
            i.include
                .file_name()
                .is_some_and(|n| n == "from-dirbuild.fs")
        })
        .count();
    assert_eq!(
        dirbuild_count,
        1,
        "Directory.Build.props must import exactly once, got: {:?}",
        paths_of(&result.items),
    );
}

#[test]
fn an_import_gated_on_what_only_directory_build_props_writes_never_fires() {
    // The body's import of the nested-SDK file is gated on a property that
    // *only* `Directory.Build.props` sets, and only the nested SDK would
    // import `Directory.Build.props`. MSBuild decides the gate first, finds
    // it false, and so imports neither file.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <PropertyGroup>
    <FromDbp>1</FromDbp>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" Condition="'$(FromDbp)' == '1'" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert!(
        result.items.is_empty() && !result.items_uncertain,
        "neither file is imported, and that is certain; got: {:?}",
        paths_of(&result.items)
    );
}

#[test]
fn entry_and_nested_sdk_import_directory_build_props_once_after_the_entry_sdk() {
    // When the entry project *has* an SDK, its `Sdk.props` is the first to
    // run, so its import point imports `Directory.Build.props` (after the
    // entry Sdk.props, before the body). The nested SDK's point deeper in the
    // body is then a duplicate MSBuild skips: the file is imported once.
    let tmp = TempDir::new().unwrap();
    let (entry_root, entry_props, entry_targets) = write_synthetic_sdk(
        tmp.path(),
        "EntrySdk",
        &format!(
            "<Project>\n  <ItemGroup>\n    <Compile Include=\"entry-props.fs\" />\n  </ItemGroup>\n{COMMON_PROPS_BLOCK}</Project>"
        ),
        "<Project/>",
    );
    let (nested_root, nested_props, nested_targets) =
        write_synthetic_sdk(tmp.path(), "NestedSdk", &common_props_sdk(), "<Project/>");
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="NestedSdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project Sdk="EntrySdk">
  <ItemGroup>
    <Compile Include="body.fs" />
  </ItemGroup>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, move |name| match name {
        "EntrySdk" => Ok(SdkPaths {
            root: entry_root.clone(),
            props: entry_props.clone(),
            targets: entry_targets.clone(),
        }),
        "NestedSdk" => Ok(SdkPaths {
            root: nested_root.clone(),
            props: nested_props.clone(),
            targets: nested_targets.clone(),
        }),
        _ => Err(SdkResolveError::NotFound),
    });
    let dir = canon(tmp.path());
    let paths = paths_of(&result.items);
    let idx = |name: &str| {
        paths
            .iter()
            .position(|p| p == &dir.join(name))
            .unwrap_or_else(|| panic!("{name} missing from {paths:?}"))
    };
    assert_eq!(
        paths
            .iter()
            .filter(|p| *p == &dir.join("from-dirbuild.fs"))
            .count(),
        1,
        "Directory.Build.props must import exactly once; got: {paths:?}",
    );
    assert!(
        idx("entry-props.fs") < idx("from-dirbuild.fs"),
        "entry Sdk.props must precede Directory.Build.props; got: {paths:?}",
    );
    assert!(
        idx("from-dirbuild.fs") < idx("body.fs"),
        "Directory.Build.props must precede the entry body; got: {paths:?}",
    );
}

#[test]
fn the_nested_point_reads_a_gate_the_body_wrote() {
    // MSBuild evaluates the `ImportDirectoryBuildProps` gate at the point
    // it imports `Directory.Build.props` — for the entry-no-SDK shape that
    // is the first nested `Sdk.props`, *after* the entry body has run. A
    // body `<PropertyGroup>` that sets `ImportDirectoryBuildProps=false`
    // before the nested SDK import therefore closes the point.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <PropertyGroup>
    <ImportDirectoryBuildProps>false</ImportDirectoryBuildProps>
  </PropertyGroup>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    let paths = paths_of(&result.items);
    assert!(
        paths.contains(&dir.join("nested-body.fs")),
        "the nested SDK import still fires; got: {paths:?}",
    );
    assert!(
        !paths.contains(&dir.join("from-dirbuild.fs")),
        "ImportDirectoryBuildProps=false set before the nested SDK must \
         close its import point; got: {paths:?}",
    );
}

#[test]
fn the_nested_point_reads_a_path_the_body_redirected() {
    // The `DirectoryBuildPropsPath` redirect is likewise read at the nested
    // import point. A body `<PropertyGroup>` that redirects it before the
    // nested SDK import makes the point import the redirect target, not the
    // nearest-ancestor file.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    // Nearest-ancestor fallback (would be imported if we used the
    // stale before-body resolution).
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-fallback.fs" />
  </ItemGroup>
</Project>"#,
    );
    // The redirect target the body points at.
    let alt = tmp.path().join("alt");
    std::fs::create_dir_all(&alt).unwrap();
    write_at(
        &alt,
        "Custom.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-custom.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <PropertyGroup>
    <DirectoryBuildPropsPath>$(MSBuildThisFileDirectory)alt/Custom.props</DirectoryBuildPropsPath>
  </PropertyGroup>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    let paths = paths_of(&result.items);
    assert!(
        paths.contains(&dir.join("from-custom.fs")),
        "the body's DirectoryBuildPropsPath redirect must be honoured at the deferred fire point; got: {paths:?}",
    );
    assert!(
        !paths.contains(&dir.join("from-fallback.fs")),
        "the stale before-body fallback must not be imported once the body redirects the path; got: {paths:?}",
    );
}

#[test]
fn entry_no_sdk_body_directory_build_props_path_override_imported_at_nested_sdk() {
    // The entry has no SDK and there is *no* on-disk
    // `Directory.Build.props`: only the body's `DirectoryBuildPropsPath`
    // override names a file, and the nested `Sdk.props` point imports it,
    // exactly where MSBuild performs the import.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    // The redirect target the body points at. Note: there is deliberately
    // *no* `Directory.Build.props` on disk, so only the redirect names a file.
    let alt = tmp.path().join("alt");
    std::fs::create_dir_all(&alt).unwrap();
    write_at(
        &alt,
        "Custom.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-custom.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <PropertyGroup>
    <DirectoryBuildPropsPath>$(MSBuildThisFileDirectory)alt/Custom.props</DirectoryBuildPropsPath>
  </PropertyGroup>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    let paths = paths_of(&result.items);
    assert!(
        paths.contains(&dir.join("from-custom.fs")),
        "the body's DirectoryBuildPropsPath override must be imported at the nested Sdk.props point even with no on-disk Directory.Build.props; got: {paths:?}",
    );
    assert!(
        paths.contains(&dir.join("nested-body.fs")),
        "the nested SDK body items must still be present; got: {paths:?}",
    );
}

#[test]
fn directory_build_props_runs_after_the_import_that_reaches_it() {
    // `Directory.Build.props` sets `SkipNested=true` and the body's only
    // nested-SDK import is gated on `'$(SkipNested)' != 'true'`. MSBuild
    // evaluates that condition *before* `Directory.Build.props` runs (it
    // runs at the nested `Sdk.props`, which the import reaches), so
    // `SkipNested` is unset, the import fires, and the nested `Sdk.props`
    // runs.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <PropertyGroup>
    <SkipNested>true</SkipNested>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <Import Project="nested.targets" Condition="'$(SkipNested)' != 'true'" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    let dir = canon(tmp.path());
    let paths = paths_of(&result.items);
    assert!(
        paths.contains(&dir.join("nested-body.fs")),
        "the nested import must fire under the faithful order: its condition is evaluated before Directory.Build.props sets SkipNested; got: {paths:?}",
    );
    assert!(
        paths.contains(&dir.join("from-dirbuild.fs")),
        "Directory.Build.props must still contribute, fired at the nested Sdk.props; got: {paths:?}",
    );
}

#[test]
fn the_nested_point_declines_on_an_undecidable_body_gate() {
    // The nested SDK's `Microsoft.Common.props` import of
    // `Directory.Build.props` is an import point like the entry SDK's, so it
    // has the same trust check: otherwise an undecidable body write of the
    // gate leaves the import (and its Compile items) published as exact.
    //
    // `'$(X.Substring(0,1))' == 'a'` is ordinary MSBuild we do not model, and
    // the oracle says it is **true** (dotnet 10.0.301, 2026-08-01) — so the
    // real build writes `false` and skips the file, while we take the default
    // and import it.
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk(tmp.path(), "MySdk", &common_props_sdk(), "<Project/>");
    write_at(
        tmp.path(),
        "Directory.Build.props",
        r#"<Project>
  <ItemGroup>
    <Compile Include="from-dirbuild.fs" />
  </ItemGroup>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "nested.targets",
        r#"<Project Sdk="MySdk">
  <ItemGroup>
    <Compile Include="nested-body.fs" />
  </ItemGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <PropertyGroup>
    <X>abc</X>
    <ImportDirectoryBuildProps Condition="'$(X.Substring(0,1))' == 'a'">false</ImportDirectoryBuildProps>
  </PropertyGroup>
  <Import Project="nested.targets" />
</Project>"#,
    );
    let result = parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    });
    assert!(
        result.items_uncertain,
        "the nested import point's gate could not be decided, so the item set must \
         not be published as exact; items: {:?}",
        paths_of(&result.items),
    );
}
