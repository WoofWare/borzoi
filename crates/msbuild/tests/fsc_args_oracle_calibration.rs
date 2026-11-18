//! Calibration of the oracle's `fscArgs` op, and of the reading of fsc's
//! arguments ([`borzoi_oracle_harness::fsc_args`]), against **real compiling
//! builds**.
//!
//! ## Why the oracle needs an oracle
//!
//! The evaluation ops of `msbuild-condition-oracle` are exactly as
//! trustworthy as MSBuild's evaluator. `fscArgs` answers a question about the
//! *build*: it restores, runs a real `Build`'s targets through `Compile`
//! in-process with the compiler's run skipped and project references
//! resolved without being built, and reports the arguments the real `Fsc`
//! task computed. That such a build passes fsc what a real one does is a
//! claim, not a fact; so is the reading of those arguments as fsc reads them,
//! and so is the op's saying MSBuild built nothing. This test checks all
//! three:
//!
//! - the op's arguments, unescaped, equal the `FscCommandLineArgs` of a real
//!   `dotnet msbuild -restore -t:Build` of the same project (a whole `Build`,
//!   compiling: `ProvideCommandLineArgs` alone, so fsc runs), in order;
//! - the file the reading takes fsc's output to be is the one that build
//!   wrote, and its name is the one pinned per fixture;
//! - where the op says MSBuild built nothing, the real build fails without
//!   running fsc, and where the op's own settings fail a build that runs
//!   fsc without them, the op refuses rather than saying so.
//!
//! The op reports each argument as the task wrote it (`%41` stays `%41`); the
//! real build's `-getItem` reports items unescaped, so the comparison
//! unescapes the op's side, and the file check, which only the op's spelling
//! can pass, is what holds the escaped spelling to the truth.
//!
//! The fixtures span the routes by which fsc's output moves: the name
//! properties, an output switch in `OtherFlags` after a line break inside
//! quotes, padded inside quotes, behind a leading `/`, commented out, an
//! escaped `%`, a `\` in the name (which MSBuild turns into a separator on
//! Unix), a Compile item spelled as a switch, a line break in an argument the
//! task passes verbatim; and a project reference, which the op resolves
//! without building it.
//!
//! One fixture must make the op **disagree**: a target that changes the
//! arguments only when fsc really runs. That is the op's genuine boundary, and
//! the fixture proves the comparison can see it.
//!
//! Every restore here is pinned to the devshell's offline feed
//! ([`msbuild_oracle::restore_sources`]).

mod common;

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::unescape;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::fsc_args::{FscArguments, assembly_name_of};
use borzoi_oracle_harness::msbuild_oracle::{self, FscArgsDecline, Oracle};
use common::scrub_oracle_env;

/// What the op must do on a fixture, relative to the real build.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Expect {
    /// The real build's arguments, exactly, and the name it compiled to.
    Agree,
    /// Other arguments than the real build's: the fixture exercises build
    /// logic outside the op's scope.
    Diverge,
    /// Say MSBuild built nothing: the real build fails before fsc runs.
    NoBuild,
    /// Refuse: the op's own settings fail a build the real one compiles.
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
    /// The assembly name the real build compiles to.
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

fn fixtures() -> Vec<Fixture> {
    use Expect::{Agree, Diverge, NoBuild, Unanswered};
    let props = |name, body| Fixture {
        name,
        body,
        compile: &[],
        files: &[],
        compiles_to: "",
        expect: Agree,
    };
    vec![
        Fixture {
            compiles_to: "Demo",
            ..props("plain", "")
        },
        Fixture {
            compiles_to: "Friend",
            ..props(
                "AssemblyName",
                "<PropertyGroup><AssemblyName>Friend</AssemblyName></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "Other",
            ..props(
                "an output switch in OtherFlags",
                "<PropertyGroup><OtherFlags>--out:obj/Other.dll</OtherFlags></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "Nl",
            ..props(
                "an output switch after a line break inside quotes",
                "<PropertyGroup><OtherFlags>\"--warnon:1182&#10;--out:obj/Nl.dll\"</OtherFlags></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "Pad",
            ..props(
                "an output switch padded inside quotes",
                "<PropertyGroup><OtherFlags>\" --out:obj/Pad.dll\"</OtherFlags></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "Slash",
            ..props(
                "a slash output switch",
                "<PropertyGroup><OtherFlags>/o:obj/Slash.dll</OtherFlags></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "Demo",
            ..props(
                "a commented-out output switch",
                "<PropertyGroup><OtherFlags>#--out:obj/Hash.dll</OtherFlags></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "%41",
            ..props(
                "an escaped percent in the name",
                "<PropertyGroup><AssemblyName>%2541</AssemblyName></PropertyGroup>",
            )
        },
        Fixture {
            compiles_to: "slash",
            ..props(
                "a backslash in the name",
                "<PropertyGroup><TargetName>back\\slash</TargetName></PropertyGroup>",
            )
        },
        Fixture {
            compile: &["--out:obj/Src.dll"],
            compiles_to: "Src",
            ..props("a Compile item spelled as a switch", "")
        },
        Fixture {
            compiles_to: "Doc",
            ..props(
                "a line break in a verbatim argument",
                "<PropertyGroup><DocumentationFile>doc.xml&#10;--out:obj/Doc.dll</DocumentationFile></PropertyGroup>",
            )
        },
        Fixture {
            files: LIB,
            compiles_to: "Demo",
            ..props(
                "a project reference",
                "<ItemGroup><ProjectReference Include=\"Lib/Lib.fsproj\" /></ItemGroup>",
            )
        },
        Fixture {
            compiles_to: "Real",
            expect: Diverge,
            ..props(
                "a target that only acts when fsc runs",
                "<Target Name=\"OnlyWhenCompiling\" BeforeTargets=\"CoreCompile\" \
                 Condition=\"'$(SkipCompilerExecution)' != 'true'\"><PropertyGroup>\
                 <OtherFlags>$(OtherFlags) --out:obj/Real.dll</OtherFlags></PropertyGroup></Target>",
            )
        },
        Fixture {
            expect: NoBuild,
            ..props(
                "a target that fails every build",
                "<Target Name=\"Fail\" BeforeTargets=\"CoreCompile\"><Error Text=\"no\" /></Target>",
            )
        },
        Fixture {
            files: LIB,
            expect: Unanswered,
            ..props(
                "a hook that needs the referenced project built",
                "<ItemGroup><ProjectReference Include=\"Lib/Lib.fsproj\" /></ItemGroup>\
                 <Target Name=\"NeedsLib\" BeforeTargets=\"CoreCompile\"><Error \
                 Condition=\"!Exists('Lib/bin/Debug/net10.0/Lib.dll')\" Text=\"Lib is not built\" />\
                 </Target>",
            )
        },
    ]
}

/// A real, compiling `Build` of `project`, its restore pinned as the op's
/// is: whether it succeeded, the `FscCommandLineArgs` `-getItem` reports
/// (unescaped; empty when none were written), and its output.
///
/// A build whose compiler wrote its output somewhere other than
/// `@(IntermediateAssembly)` fails afterwards, copying the file that is not
/// there (MSB3030, or MSB3883 for the reference assembly), as such a real
/// build does; [`compiled`] accepts that failure alone.
fn real_build(project: &Path) -> (bool, Vec<String>, String) {
    let out_file = project.with_file_name("fsc-args.json");
    let mut cmd = Command::new("dotnet");
    cmd.args([
        "msbuild",
        "-nologo",
        "-nodeReuse:false",
        "-restore",
        "-t:Build",
        "-p:ProvideCommandLineArgs=true",
        "-getItem:FscCommandLineArgs",
    ]);
    if let Some(sources) = msbuild_oracle::restore_sources() {
        cmd.arg(format!("-restoreProperty:RestoreSources={sources}"));
    }
    cmd.arg(format!("-getResultOutputFile:{}", out_file.display()));
    cmd.arg(project);
    scrub_oracle_env(&mut cmd);
    let out = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(600))
        .run()
        .unwrap_or_else(|e| panic!("real build of {}: {e}", project.display()));
    let output = format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let args = host_fs::read_to_string(&out_file)
        .ok()
        .and_then(|json| serde_json::from_str::<serde_json::Value>(&json).ok())
        .and_then(|value| {
            value["Items"]["FscCommandLineArgs"]
                .as_array()
                .map(|items| {
                    items
                        .iter()
                        .map(|item| {
                            item["Identity"]
                                .as_str()
                                .expect("item identity is a string")
                                .to_string()
                        })
                        .collect()
                })
        })
        .unwrap_or_default();
    (out.status.success(), args, output)
}

/// Whether a real build compiled: it succeeded, or failed only copying an
/// output fsc wrote elsewhere (MSB3883 reports its exception on further
/// `error :` lines of its own).
fn compiled(succeeded: bool, output: &str) -> bool {
    let errors: Vec<&str> = output.lines().filter(|l| l.contains(" error ")).collect();
    succeeded
        || (errors
            .iter()
            .any(|l| l.contains("error MSB3030") || l.contains("error MSB3883"))
            && errors.iter().all(|l| {
                l.contains("error MSB3030")
                    || l.contains("error MSB3883")
                    || l.contains(": error : ")
            }))
}

/// `argument` with the path of a reference (`-r:`) canonicalised: the oracle
/// and `dotnet` may reach one installation through different links (the
/// devshell's combined `dotnet` is a tree of links into each SDK's own), and
/// name the same reference assemblies by different paths.
fn canonical_reference(argument: &str) -> String {
    match argument.strip_prefix("-r:") {
        Some(path) => match host_fs::canonicalize(Path::new(path)) {
            Ok(canonical) => format!("-r:{}", canonical.display()),
            Err(_) => argument.to_string(),
        },
        None => argument.to_string(),
    }
}

#[test]
fn fsc_args_op_matches_real_builds() {
    let mut failures = Vec::new();
    let all = fixtures();
    for fixture in &all {
        let tmp = tempfile::TempDir::new().expect("tempdir for fixture");
        let dir = host_fs::canonicalize(tmp.path()).unwrap();
        let mut oracle = Oracle::spawn_in_dir_with_env(&dir, &[]);
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

        // The op goes first, on the project as written and unrestored, since
        // restoring is part of what it claims to do.
        let op = oracle.fsc_args(&project, &[]);
        let (succeeded, real, output) = real_build(&project);
        let real: Vec<String> = real.iter().map(|a| canonical_reference(a)).collect();
        let op = match (fixture.expect, op) {
            (Expect::NoBuild, Err(FscArgsDecline::NoBuild(_))) => {
                if compiled(succeeded, &output) || !real.is_empty() {
                    failures.push(format!(
                        "`{}`: the op says MSBuild built nothing, but the real build ran fsc",
                        fixture.name
                    ));
                }
                continue;
            }
            (Expect::Unanswered, Err(FscArgsDecline::Unanswered(_))) => {
                if !compiled(succeeded, &output) {
                    failures.push(format!(
                        "`{}`: the real build did not compile:\n{output}",
                        fixture.name
                    ));
                }
                continue;
            }
            (Expect::Agree | Expect::Diverge, Ok(op)) => op,
            (expect, op) => {
                failures.push(format!(
                    "`{}`: expected {expect:?}, the op answered {op:?}",
                    fixture.name
                ));
                continue;
            }
        };
        if !compiled(succeeded, &output) {
            failures.push(format!(
                "`{}`: the real build did not compile:\n{output}",
                fixture.name
            ));
            continue;
        }
        let unescaped: Vec<String> = op
            .args
            .iter()
            .map(|a| canonical_reference(&unescape(a)))
            .collect();
        match fixture.expect {
            Expect::Agree => {
                if unescaped != real {
                    let only_op: Vec<&String> =
                        unescaped.iter().filter(|a| !real.contains(a)).collect();
                    let only_real: Vec<&String> =
                        real.iter().filter(|a| !unescaped.contains(a)).collect();
                    failures.push(format!(
                        "`{}`: the op's arguments are not the real build's\n  only the op's: \
                         {only_op:?}\n  only the real build's: {only_real:?}",
                        fixture.name
                    ));
                    continue;
                }
                let Some(path) = op.arguments().ok().and_then(|args| args.output) else {
                    failures.push(format!(
                        "`{}`: no output in {:?}",
                        fixture.name, op.response_file
                    ));
                    continue;
                };
                if !dir.join(&path).host_is_file() {
                    failures.push(format!(
                        "`{}`: the real build wrote no {path:?}",
                        fixture.name
                    ));
                }
                if assembly_name_of(&path) != fixture.compiles_to {
                    failures.push(format!(
                        "`{}`: fsc compiles to {path:?}, not a {:?}",
                        fixture.name, fixture.compiles_to
                    ));
                }
            }
            Expect::Diverge => {
                let real_name = FscArguments::parse_arguments(&real)
                    .ok()
                    .and_then(|args| args.assembly_name());
                if unescaped == real || real_name.as_deref() != Some(fixture.compiles_to) {
                    failures.push(format!(
                        "`{}`: expected the op to miss the real build's {:?}\n  op:   \
                         {unescaped:?}\n  real: {real:?}",
                        fixture.name, fixture.compiles_to
                    ));
                }
            }
            Expect::NoBuild | Expect::Unanswered => unreachable!("handled above"),
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
