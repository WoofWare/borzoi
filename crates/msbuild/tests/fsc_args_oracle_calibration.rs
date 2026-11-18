//! Calibration of [`borzoi_oracle_harness::msbuild_oracle::fsc_args`], and of
//! the reading of fsc's arguments ([`borzoi_oracle_harness::fsc_args`]),
//! against what real compiling builds do.
//!
//! `fsc_args` runs a real `dotnet msbuild -restore -t:Build` and reads each
//! `Fsc` invocation's response file off the command line the task logs. Two
//! things in that are claims rather than facts, and this test checks both:
//!
//! - that the logged command line is the response file: its lines, but for
//!   `--refout:`/`--refonly` (which the task writes to the file and not to
//!   its reported arguments), equal the `FscCommandLineArgs` a second real
//!   build reports through `-getItem` (with `ProvideCommandLineArgs`; the
//!   items decode `%XX` and turn `\` into `/`, so the file's lines are
//!   compared that way), in order;
//! - that the reading names the file fsc wrote: the output it parses exists
//!   after the build, and its name is the one pinned per fixture.
//!
//! The fixtures span the routes by which fsc's output moves (the name
//! properties and a global, an output switch in `OtherFlags` after a line
//! break inside quotes, padded inside quotes, behind a leading `/`,
//! commented out, an escaped `%`, a `\` in the name, a Compile item spelled
//! as a switch, a line break in an argument the task passes verbatim, a
//! target that acts only when the compiler really runs), and project
//! references, built as a real build builds them: one a hook needs built
//! first, and a C# one that fails to compile, after which nothing is built.
//! A `global.json` no installed SDK satisfies builds nothing either, and
//! compiler arguments set ahead of the response file (in
//! `DotnetFscCompilerPath`) leave the driver unable to answer.

mod common;

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::unescape;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::fsc_args::assembly_name_of;
use borzoi_oracle_harness::msbuild_oracle::{
    FscArgsDecline, FscBuild, build_environment, fsc_args,
};

/// What `fsc_args` must report for a fixture.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Expect {
    /// One invocation, compiling to [`Fixture::compiles_to`].
    Compiles,
    /// Nothing built: the `dotnet` host refuses the build.
    NoBuild,
    /// No answer: no fsc run of the project's left evidence (the build
    /// failed first), or one ran on arguments the response file does not
    /// hold.
    Unanswered,
}

struct Fixture {
    name: &'static str,
    /// Project elements inside `<Project>`, after the target framework.
    body: &'static str,
    /// Further Compile includes, before `A.fs`.
    compile: &'static [&'static str],
    /// Further files beside the project, as `(relative path, contents)`.
    files: &'static [(&'static str, &'static str)],
    /// Global properties for the build.
    globals: &'static [(&'static str, &'static str)],
    /// The assembly name the build compiles to.
    compiles_to: &'static str,
    expect: Expect,
}

/// A second project, for the fixtures that reference one.
const LIB: &[(&str, &str)] = &[
    (
        "Lib/Lib.fsproj",
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
         <TargetFramework>net10.0</TargetFramework></PropertyGroup>\
         <ItemGroup><Compile Include=\"L.fs\" /></ItemGroup></Project>",
    ),
    ("Lib/L.fs", "module L\nlet y = 2\n"),
];

/// A C# project that does not compile.
const BROKEN_LIB: &[(&str, &str)] = &[
    (
        "Broken/Broken.csproj",
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
         <TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>",
    ),
    ("Broken/B.cs", "class B { int x = ; }\n"),
];

fn fixtures() -> Vec<Fixture> {
    use Expect::{Compiles, NoBuild, Unanswered};
    let props = |name, body, compiles_to| Fixture {
        name,
        body,
        compile: &[],
        files: &[],
        globals: &[],
        compiles_to,
        expect: Compiles,
    };
    vec![
        props("plain", "", "Demo"),
        props(
            "OtherFlags gated on what a logging switch would set",
            "<PropertyGroup Condition=\"'$(MSBuildBinaryLoggerEnabled)$(MSBuildLogImports)\
             $(MSBUILDLOGTASKINPUTS)' != ''\"><OtherFlags>--out:obj/Instrumented.dll</OtherFlags>\
             </PropertyGroup>",
            "Demo",
        ),
        props(
            "AssemblyName",
            "<PropertyGroup><AssemblyName>Friend</AssemblyName></PropertyGroup>",
            "Friend",
        ),
        Fixture {
            globals: &[("AssemblyName", "GlobalName")],
            ..props("a global AssemblyName", "", "GlobalName")
        },
        props(
            "an output switch in OtherFlags",
            "<PropertyGroup><OtherFlags>--out:obj/Other.dll</OtherFlags></PropertyGroup>",
            "Other",
        ),
        props(
            "an output switch after a line break inside quotes",
            "<PropertyGroup><OtherFlags>\"--warnon:1182&#10;--out:obj/Nl.dll\"</OtherFlags></PropertyGroup>",
            "Nl",
        ),
        props(
            "an output switch padded inside quotes",
            "<PropertyGroup><OtherFlags>\" --out:obj/Pad.dll\"</OtherFlags></PropertyGroup>",
            "Pad",
        ),
        props(
            "a slash output switch",
            "<PropertyGroup><OtherFlags>/o:obj/Slash.dll</OtherFlags></PropertyGroup>",
            "Slash",
        ),
        props(
            "a commented-out output switch",
            "<PropertyGroup><OtherFlags>#--out:obj/Hash.dll</OtherFlags></PropertyGroup>",
            "Demo",
        ),
        props(
            "an escaped percent in the name",
            "<PropertyGroup><AssemblyName>%2541</AssemblyName></PropertyGroup>",
            "%41",
        ),
        props(
            "a doubly escaped percent in the name",
            "<PropertyGroup><AssemblyName>%252541</AssemblyName></PropertyGroup>",
            "%2541",
        ),
        props(
            "a backslash in the name",
            "<PropertyGroup><TargetName>back\\slash</TargetName></PropertyGroup>",
            "slash",
        ),
        Fixture {
            compile: &["--out:obj/Src.dll"],
            ..props("a Compile item spelled as a switch", "", "Src")
        },
        props(
            "a line break in a verbatim argument",
            "<PropertyGroup><DocumentationFile>doc.xml&#10;--out:obj/Doc.dll</DocumentationFile></PropertyGroup>",
            "Doc",
        ),
        props(
            "a target that acts only when the compiler runs",
            "<Target Name=\"OnlyWhenCompiling\" BeforeTargets=\"CoreCompile\" \
             Condition=\"'$(SkipCompilerExecution)' != 'true'\"><PropertyGroup>\
             <OtherFlags>$(OtherFlags) --out:obj/Real.dll</OtherFlags></PropertyGroup></Target>",
            "Real",
        ),
        Fixture {
            files: LIB,
            ..props(
                "a project reference",
                "<ItemGroup><ProjectReference Include=\"Lib/Lib.fsproj\" /></ItemGroup>",
                "Demo",
            )
        },
        Fixture {
            files: LIB,
            ..props(
                "a hook that needs the referenced project built",
                "<ItemGroup><ProjectReference Include=\"Lib/Lib.fsproj\" /></ItemGroup>\
                 <Target Name=\"NeedsLib\" BeforeTargets=\"CoreCompile\"><Error \
                 Condition=\"!Exists('Lib/bin/Debug/net10.0/Lib.dll')\" Text=\"Lib is not built\" />\
                 </Target>",
                "Demo",
            )
        },
        Fixture {
            expect: Unanswered,
            ..props(
                "a target that fails every build",
                "<Target Name=\"Fail\" BeforeTargets=\"CoreCompile\"><Error Text=\"no\" /></Target>",
                "",
            )
        },
        Fixture {
            files: BROKEN_LIB,
            expect: Unanswered,
            ..props(
                "a C# project reference that does not compile",
                "<ItemGroup><ProjectReference Include=\"Broken/Broken.csproj\" /></ItemGroup>",
                "",
            )
        },
        Fixture {
            files: &[(
                "global.json",
                "{\"sdk\":{\"version\":\"9.9.999\",\"rollForward\":\"disable\"}}",
            )],
            expect: NoBuild,
            ..props("a global.json no installed SDK satisfies", "", "")
        },
        Fixture {
            expect: Unanswered,
            ..props(
                "compiler arguments ahead of the response file",
                "<PropertyGroup><DotnetFscCompilerPath>\"$(MSBuildBinPath)/FSharp/fsc.dll\" \
                 --define:EXTRACLI</DotnetFscCompilerPath></PropertyGroup>",
                "",
            )
        },
    ]
}

/// The `FscCommandLineArgs` a real build of `project` reports through
/// `-getItem` (unescaped), in the environment `fsc_args` builds in. Run on a
/// second copy of the fixture, so it builds from scratch and leaves the
/// graded build's tree alone.
fn reported_arguments(project: &Path, globals: &[(&str, &str)]) -> Vec<String> {
    let dir = project.parent().unwrap();
    let out_file = dir.join("fsc-args-items.json");
    let mut cmd = Command::new("dotnet");
    cmd.current_dir(dir).args([
        "msbuild",
        "-nologo",
        "-nodeReuse:false",
        "-restore",
        "-t:Build",
        "-p:ProvideCommandLineArgs=true",
        "-getItem:FscCommandLineArgs",
    ]);
    for (name, value) in globals {
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(format!("-getResultOutputFile:{}", out_file.display()));
    cmd.arg(project).env_clear().envs(build_environment());
    let out = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(900))
        .run()
        .unwrap_or_else(|e| panic!("real build of {}: {e}", project.display()));
    let json = host_fs::read_to_string(&out_file).unwrap_or_else(|e| {
        panic!(
            "real build of {} wrote no items ({e}):\n{}",
            project.display(),
            String::from_utf8_lossy(&out.stdout)
        )
    });
    let value: serde_json::Value = serde_json::from_str(&json).expect("getItem output is JSON");
    value["Items"]["FscCommandLineArgs"]
        .as_array()
        .expect("FscCommandLineArgs items present")
        .iter()
        .map(|item| {
            item["Identity"]
                .as_str()
                .expect("item identity is a string")
                .to_string()
        })
        .collect()
}

/// `argument` with the path of a reference (`-r:`) canonicalised: two builds
/// may reach one installation through different links (the devshell's
/// combined `dotnet` is a tree of links into each SDK's own).
fn canonical_reference(argument: &str) -> String {
    match argument.strip_prefix("-r:") {
        Some(path) => match host_fs::canonicalize(Path::new(path)) {
            Ok(canonical) => format!("-r:{}", canonical.display()),
            Err(_) => argument.to_string(),
        },
        None => argument.to_string(),
    }
}

/// Arguments as the comparison reads them: split at line breaks (as fsc
/// reads them), without the `--refout:`/`--refonly` the task does not
/// report, the reference paths canonical.
fn comparable(lines: impl Iterator<Item = String>) -> Vec<String> {
    lines
        .filter(|line| !line.starts_with("--refout:") && line != "--refonly")
        .map(|line| canonical_reference(&line))
        .collect()
}

/// The response file's lines as the reported items spell them: decoded once,
/// and each `\` a `/`.
fn spelled_as_items(line: &str) -> String {
    unescape(&line.replace('\\', "/"))
}

/// Check one fixture's [`FscBuild`]; the failures it shows.
///
/// The file the reading names is checked first, before the control build
/// (in `control`, a second copy of the fixture) could write anything.
fn check_build(fixture: &Fixture, dir: &Path, control: &Path, build: &FscBuild) -> Vec<String> {
    let mut failures = Vec::new();
    let [invocation] = build.invocations.as_slice() else {
        return vec![format!(
            "`{}`: {} Fsc invocations",
            fixture.name,
            build.invocations.len()
        )];
    };
    match invocation.arguments().map(|args| args.output) {
        Ok(Some(path)) => {
            if !dir.join(&path).host_is_file() {
                failures.push(format!("`{}`: fsc wrote no {path:?}", fixture.name));
            }
            if assembly_name_of(&path) != fixture.compiles_to {
                failures.push(format!(
                    "`{}`: fsc compiles to {path:?}, not a {:?}",
                    fixture.name, fixture.compiles_to
                ));
            }
        }
        other => failures.push(format!("`{}`: no output read: {other:?}", fixture.name)),
    }
    // The reference assembly, which only the response file carries: every
    // fixture targets a framework that produces one, and fsc writes it.
    let refout: Vec<String> = invocation
        .arguments()
        .map(|args| {
            args.options
                .into_iter()
                .filter(|option| option.name == "refout")
                .map(|option| option.argument)
                .collect()
        })
        .unwrap_or_default();
    match refout.as_slice() {
        [path] if dir.join(path).host_is_file() => {}
        other => failures.push(format!(
            "`{}`: the reference assembly fsc wrote is not the one --refout names: {other:?}",
            fixture.name
        )),
    }
    let (graded_dir, control_dir) = (dir.display().to_string(), control.display().to_string());
    let reported = comparable(
        reported_arguments(&control.join("Demo.fsproj"), fixture.globals)
            .join("\n")
            .split('\n')
            .map(|line| line.replace(&control_dir, &graded_dir)),
    );
    let read = comparable(invocation.response_file.split('\n').map(spelled_as_items));
    if read != reported {
        let only_read: Vec<&String> = read.iter().filter(|a| !reported.contains(a)).collect();
        let only_reported: Vec<&String> = reported.iter().filter(|a| !read.contains(a)).collect();
        failures.push(format!(
            "`{}`: the logged response file is not the reported arguments\n  only the file's: \
             {only_read:?}\n  only the reported: {only_reported:?}",
            fixture.name
        ));
    }
    failures
}

/// Write `fixture`'s files under `dir`; the project file's path.
fn lay_out(fixture: &Fixture, dir: &Path) -> std::path::PathBuf {
    let project = dir.join("Demo.fsproj");
    let compile: String = fixture
        .compile
        .iter()
        .chain(&["A.fs"])
        .map(|c| format!("<Compile Include=\"{c}\" />"))
        .collect();
    std::fs::write(
        &project,
        format!(
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
             <TargetFramework>net10.0</TargetFramework></PropertyGroup>{}\
             <ItemGroup>{compile}</ItemGroup></Project>",
            fixture.body
        ),
    )
    .unwrap();
    std::fs::write(dir.join("A.fs"), "module A\nlet x = 1\n").unwrap();
    for (name, contents) in fixture.files {
        let file = dir.join(name);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, contents).unwrap();
    }
    project
}

#[test]
fn fsc_args_reads_what_real_builds_hand_fsc() {
    let mut failures = Vec::new();
    let all = fixtures();
    for fixture in &all {
        let tmp = tempfile::TempDir::new().expect("tempdir for fixture");
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        let (dir, control) = (root.join("graded"), root.join("control"));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::create_dir_all(&control).unwrap();
        let project = lay_out(fixture, &dir);
        lay_out(fixture, &control);
        let globals: Vec<(String, String)> = fixture
            .globals
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
        match (fixture.expect, fsc_args(&project, &globals, &[])) {
            (Expect::Compiles, Ok(build)) => {
                failures.extend(check_build(fixture, &dir, &control, &build))
            }
            (Expect::NoBuild, Err(FscArgsDecline::NoBuild(_))) => {}
            (Expect::Unanswered, Err(FscArgsDecline::Unanswered(_))) => {}
            (expect, answer) => failures.push(format!(
                "`{}`: expected {expect:?}, got {answer:?}",
                fixture.name
            )),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} calibration fixtures failed:\n{}",
        failures.len(),
        all.len(),
        failures.join("\n")
    );
}
