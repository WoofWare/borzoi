//! Calibration of the oracle's `fscArgs` op, and of the test-side reading of
//! fsc's arguments ([`common::fsc_reading`]), against **real compiling
//! builds**.
//!
//! ## Why the oracle needs an oracle
//!
//! Every other op of `msbuild-condition-oracle` but `defines`-style ones stops
//! at evaluation, and so is exactly as trustworthy as MSBuild's evaluator.
//! `fscArgs` answers a question about the *build*: it restores, runs a real
//! `Build`'s targets through `Compile` in-process with the compiler's run
//! skipped, and reports the arguments the real `Fsc` task computed. That such
//! a build passes fsc what a real one does is a claim, not a fact; so is the
//! reading of those arguments as fsc reads them. This test checks both:
//!
//! - the op's arguments, unescaped, equal the `FscCommandLineArgs` of a real
//!   `dotnet msbuild -restore -t:Build` of the same project (a whole `Build`,
//!   compiling: `ProvideCommandLineArgs` alone, so fsc runs), in order;
//! - the file the reading takes fsc's output to be is the one that build
//!   wrote, and its name is the one pinned per fixture.
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
//! Unix), a Compile item spelled as a switch, and a line break in an argument
//! the task passes verbatim.
//!
//! One fixture must make the op **disagree**: a target that changes the
//! arguments only when fsc really runs. That is the op's genuine boundary, and
//! the fixture proves the comparison can see it.

mod common;

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::unescape;
use borzoi_oracle_harness::BoundedCommand;
use common::fsc_reading::{assembly_name_of, fsc_output_path, fsc_output_path_in};
use common::{Oracle, scrub_oracle_env};

/// What the op must do on a fixture, relative to the real build.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Expect {
    /// The real build's arguments, exactly, and the name it compiled to.
    Agree,
    /// Other arguments than the real build's: the fixture exercises build
    /// logic outside the op's scope.
    Diverge,
}

struct Fixture {
    name: &'static str,
    /// Project elements inside `<Project>`, after the target framework.
    body: &'static str,
    /// Further Compile includes, before `A.fs`.
    compile: &'static [&'static str],
    /// The assembly name the real build compiles to.
    compiles_to: &'static str,
    expect: Expect,
}

fn fixtures() -> Vec<Fixture> {
    use Expect::{Agree, Diverge};
    let props = |name, body| Fixture {
        name,
        body,
        compile: &[],
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
            compiles_to: "Real",
            expect: Diverge,
            ..props(
                "a target that only acts when fsc runs",
                "<Target Name=\"OnlyWhenCompiling\" BeforeTargets=\"CoreCompile\" \
                 Condition=\"'$(SkipCompilerExecution)' != 'true'\"><PropertyGroup>\
                 <OtherFlags>$(OtherFlags) --out:obj/Real.dll</OtherFlags></PropertyGroup></Target>",
            )
        },
    ]
}

/// The `FscCommandLineArgs` of a real, compiling `Build` of `project`, as
/// `-getItem` reports them (unescaped).
///
/// A build whose compiler wrote its output somewhere other than
/// `@(IntermediateAssembly)` fails afterwards, copying the file that is not
/// there (MSB3030, or MSB3883 for the reference assembly), as such a real
/// build does; that failure, alone, is accepted, since fsc has run by then.
fn real_fsc_arguments(project: &Path) -> Vec<String> {
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
    cmd.arg(format!("-getResultOutputFile:{}", out_file.display()));
    cmd.arg(project);
    scrub_oracle_env(&mut cmd);
    let out = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(600))
        .run()
        .unwrap_or_else(|e| panic!("real build of {}: {e}", project.display()));
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    // MSB3883 reports its exception on further `error :` lines of its own.
    let copy_failure = |l: &&str| {
        l.contains("error MSB3030") || l.contains("error MSB3883") || l.contains(": error : ")
    };
    let errors: Vec<&str> = stdout.lines().filter(|l| l.contains(" error ")).collect();
    assert!(
        out.status.success()
            || (errors
                .iter()
                .any(|l| l.contains("error MSB3030") || l.contains("error MSB3883"))
                && errors.iter().all(copy_failure)
                && !stderr.contains("error")),
        "real build of {} failed:\n{stdout}\n{stderr}",
        project.display()
    );
    let json = host_fs::read_to_string(&out_file).unwrap_or_else(|e| {
        panic!(
            "real build of {} wrote no items ({e}):\n{stdout}",
            project.display()
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
        let mut oracle = Oracle::spawn_in_dir(&dir);
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

        // The op goes first, on the project as written and unrestored, since
        // restoring is part of what it claims to do.
        let op = match oracle.fsc_args(&project, &[]) {
            Ok(op) => op,
            Err(errors) => {
                failures.push(format!("`{}`: the op declined: {errors:?}", fixture.name));
                continue;
            }
        };
        let real = real_fsc_arguments(&project);
        let unescaped: Vec<String> = op
            .args
            .iter()
            .map(|a| canonical_reference(&unescape(a)))
            .collect();
        let real: Vec<String> = real.iter().map(|a| canonical_reference(a)).collect();
        let read = |args: &[String]| fsc_output_path(args).ok().flatten();
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
                let Some(path) = fsc_output_path_in(&op.response_file).ok().flatten() else {
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
                let real_name = read(&real).map(|p| assembly_name_of(&p));
                if unescaped == real || real_name.as_deref() != Some(fixture.compiles_to) {
                    failures.push(format!(
                        "`{}`: expected the op to miss the real build's {:?}\n  op:   {unescaped:?}\n  real: {real:?}",
                        fixture.name, fixture.compiles_to
                    ));
                }
            }
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
