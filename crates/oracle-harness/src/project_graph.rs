//! Project graphs for `fcs-dump uses-project-graph-batch`, and the
//! multi-project fixture layout the graph differentials share.
//!
//! FCS references an F# project the way an IDE does when it is handed the
//! project as an `FSharpReferencedProject.FSharpReference`: it type-checks the
//! referenced project's sources and reads its signature from memory. That is
//! the semantics borzoi resolves `<ProjectReference>`s against, so it is the
//! oracle. A [`GraphRequest`] describes one such check: a set of projects, the
//! references between them, and the one whose files to report.
//!
//! A [`ProjectGraphFixture`] is a set of F# projects written to a fresh
//! directory, one subdirectory per project with its sources and a buildable
//! `.fsproj`. It answers both questions a graph differential asks: what FCS
//! says with each reference passed from source ([`ProjectGraphFixture::source_request`]),
//! and what it says with each reference built and passed as a DLL
//! ([`build_fixtures`], [`ProjectGraphFixture::dll_request`]).
//!
//! This module knows the protocol and the layout. Spawning `fcs-dump` is the
//! caller's: each crate already locates and builds it its own way.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use serde_json::Value;

use crate::BoundedCommand;

/// The target framework every fixture project builds for: the runtime
/// `fcs-dump` itself runs on, so the SDK references its script resolution
/// picks are the ones a fixture build compiles against.
pub const FIXTURE_TFM: &str = "net10.0";

/// A name `fcs-dump` accepts as a project id or an assembly name: a non-empty
/// run of ASCII letters, digits, `.`, `_` and `-`, so it can name a file
/// without escaping, and an assembly name is a simple name rather than a path
/// or a display name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PlainName(String);

impl PlainName {
    /// `name`, if it is plain.
    pub fn new(name: &str) -> Result<Self, GraphError> {
        let plain = !name.is_empty()
            && name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'));
        if plain {
            Ok(PlainName(name.to_owned()))
        } else {
            Err(GraphError::NotPlain(name.to_owned()))
        }
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for PlainName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// One project of a [`GraphRequest`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphProject {
    /// What other projects' [`project_refs`](Self::project_refs) name it by.
    pub id: PlainName,
    /// The assembly FCS checks it as, through `-o:`. Never derived: without
    /// it FCS names the assembly after the project's last source file, and no
    /// `InternalsVisibleTo` naming the real assembly would match.
    pub assembly_name: PlainName,
    /// Its source files, absolute, in Compile order.
    pub paths: Vec<PathBuf>,
    /// The assemblies it references, absolute.
    pub refs: Vec<PathBuf>,
    /// Its `#if` symbols.
    pub defines: Vec<String>,
    /// Its pinned `<LangVersion>`, if any.
    pub lang_version: Option<String>,
    /// Whether [`refs`](Self::refs) are the whole reference set, so the
    /// running SDK's framework is not added (`uses-project-batch`'s
    /// `exclusiveRefs`).
    pub exclusive_refs: bool,
    /// The projects of the same request it references from source.
    pub project_refs: Vec<PlainName>,
}

/// Why a [`GraphRequest`] or a [`ProjectGraphFixture`] is not a graph
/// `fcs-dump` checks as described.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GraphError {
    /// A project id or assembly name that is not a [`PlainName`].
    NotPlain(String),
    /// FCS's background compiler drops a project reference whose output is
    /// named like FSharp.Core and needs the DLL on disk instead.
    FSharpCoreName(PlainName),
    DuplicateId(PlainName),
    /// Two projects with one assembly name (compared ignoring case, as the
    /// runtime compares simple names).
    DuplicateAssemblyName(PlainName),
    UnknownReference {
        from: PlainName,
        to: PlainName,
    },
    /// A reference cycle through this project.
    Cycle(PlainName),
    /// The project to check is not one of the request's.
    UnknownCheck(PlainName),
    NoPaths(PlainName),
    /// A source or reference path that is not absolute.
    RelativePath(PathBuf),
}

impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GraphError::NotPlain(s) => write!(f, "{s:?} is not a plain name"),
            GraphError::FSharpCoreName(id) => {
                write!(
                    f,
                    "project {id} is named FSharp.Core, which FCS reads only from disk"
                )
            }
            GraphError::DuplicateId(id) => write!(f, "two projects have the id {id}"),
            GraphError::DuplicateAssemblyName(n) => write!(f, "two projects are named {n}"),
            GraphError::UnknownReference { from, to } => {
                write!(f, "project {from} references unknown project {to}")
            }
            GraphError::Cycle(id) => write!(f, "project reference cycle through {id}"),
            GraphError::UnknownCheck(id) => write!(f, "no project {id} to check"),
            GraphError::NoPaths(id) => write!(f, "project {id} has no source files"),
            GraphError::RelativePath(p) => write!(f, "{} is not absolute", p.display()),
        }
    }
}

impl std::error::Error for GraphError {}

/// A request for `fcs-dump uses-project-graph-batch`: check
/// [`check`](Self::check)'s files, with every project it reaches through
/// `project_refs` passed from source. Built only through [`GraphRequest::new`],
/// which refuses every graph the oracle would refuse, so a request that
/// reaches the oracle is one it checks as described.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphRequest {
    projects: Vec<GraphProject>,
    check: PlainName,
}

impl GraphRequest {
    pub fn new(projects: Vec<GraphProject>, check: PlainName) -> Result<Self, GraphError> {
        let mut by_id = BTreeMap::new();
        let mut names = BTreeSet::new();
        for p in &projects {
            if p.assembly_name.as_str().eq_ignore_ascii_case("FSharp.Core") {
                return Err(GraphError::FSharpCoreName(p.id.clone()));
            }
            if p.paths.is_empty() {
                return Err(GraphError::NoPaths(p.id.clone()));
            }
            if let Some(relative) = p.paths.iter().chain(&p.refs).find(|q| !q.is_absolute()) {
                return Err(GraphError::RelativePath(relative.clone()));
            }
            if by_id.insert(p.id.clone(), p).is_some() {
                return Err(GraphError::DuplicateId(p.id.clone()));
            }
            if !names.insert(p.assembly_name.as_str().to_ascii_lowercase()) {
                return Err(GraphError::DuplicateAssemblyName(p.assembly_name.clone()));
            }
        }
        for p in &projects {
            if let Some(to) = p.project_refs.iter().find(|r| !by_id.contains_key(*r)) {
                return Err(GraphError::UnknownReference {
                    from: p.id.clone(),
                    to: to.clone(),
                });
            }
        }
        if let Some(id) = first_cycle(&projects) {
            return Err(GraphError::Cycle(id));
        }
        if !by_id.contains_key(&check) {
            return Err(GraphError::UnknownCheck(check));
        }
        Ok(GraphRequest { projects, check })
    }

    pub fn projects(&self) -> &[GraphProject] {
        &self.projects
    }

    pub fn check(&self) -> &PlainName {
        &self.check
    }

    /// The request as the one JSON line the oracle reads.
    pub fn to_json_line(&self) -> String {
        let path_strings = |paths: &[PathBuf]| -> Vec<String> {
            paths.iter().map(|p| p.display().to_string()).collect()
        };
        let projects: Vec<Value> = self
            .projects
            .iter()
            .map(|p| {
                serde_json::json!({
                    "id": p.id.as_str(),
                    "assemblyName": p.assembly_name.as_str(),
                    "paths": path_strings(&p.paths),
                    "refs": path_strings(&p.refs),
                    // `--define:` with nothing after it is not a symbol.
                    "defines": p.defines.iter().filter(|d| !d.trim().is_empty()).collect::<Vec<_>>(),
                    "langversion": p.lang_version,
                    "exclusiveRefs": p.exclusive_refs,
                    "projectRefs": p.project_refs.iter().map(PlainName::as_str).collect::<Vec<_>>(),
                })
            })
            .collect();
        serde_json::json!({ "projects": projects, "check": self.check.as_str() }).to_string()
    }
}

/// Some project on a reference cycle, if the graph has one. Every reference
/// must already name a project of `projects`.
fn first_cycle(projects: &[GraphProject]) -> Option<PlainName> {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        Open,
        Done,
    }
    fn visit<'a>(
        id: &'a PlainName,
        by_id: &BTreeMap<&'a PlainName, &'a GraphProject>,
        marks: &mut BTreeMap<&'a PlainName, Mark>,
    ) -> Option<PlainName> {
        match marks.get(id) {
            Some(Mark::Done) => return None,
            Some(Mark::Open) => return Some(id.clone()),
            None => {}
        }
        marks.insert(id, Mark::Open);
        for r in &by_id[id].project_refs {
            if let Some(cycle) = visit(r, by_id, marks) {
                return Some(cycle);
            }
        }
        marks.insert(id, Mark::Done);
        None
    }
    let by_id: BTreeMap<&PlainName, &GraphProject> = projects.iter().map(|p| (&p.id, p)).collect();
    let mut marks = BTreeMap::new();
    projects
        .iter()
        .find_map(|p| visit(&p.id, &by_id, &mut marks))
}

/// A referenced project's entry in a [`GraphResponse`].
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct ReferencedProject {
    #[serde(rename = "Id")]
    pub id: String,
    #[serde(rename = "AssemblyName")]
    pub assembly_name: String,
    /// The `-o:` the oracle named it by. Never written: a test may hold that it
    /// does not exist.
    #[serde(rename = "OutputPath")]
    pub output_path: PathBuf,
    /// Its whole-project diagnostics, as `uses-project` renders a file's.
    #[serde(rename = "Diagnostics")]
    pub diagnostics: Vec<Value>,
}

impl ReferencedProject {
    /// Its error-severity diagnostics.
    pub fn errors(&self) -> impl Iterator<Item = &Value> {
        self.diagnostics.iter().filter(|d| {
            d.get("Severity")
                .and_then(Value::as_str)
                .is_some_and(|s| s.eq_ignore_ascii_case("Error"))
        })
    }
}

/// What `uses-project-graph-batch` answers: the `uses-project` records of the
/// checked project's files, kept as JSON so that two answers can be compared
/// whole, and the projects it referenced.
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct GraphResponse {
    #[serde(rename = "Files")]
    pub files: Vec<Value>,
    #[serde(rename = "Referenced")]
    pub referenced: Vec<ReferencedProject>,
}

/// Parse one response line; a `BatchError` (the oracle refused the request)
/// is the `Err`.
pub fn parse_graph_response(line: &str) -> Result<GraphResponse, String> {
    let value: Value =
        serde_json::from_str(line).map_err(|e| format!("unreadable response ({e}): {line}"))?;
    if let Some(message) = value.get("BatchError") {
        return Err(message
            .as_str()
            .unwrap_or("<non-string BatchError>")
            .to_owned());
    }
    serde_json::from_value(value).map_err(|e| format!("unexpected response shape ({e}): {line}"))
}

/// One source file of a [`FixtureProject`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureFile {
    /// Its file name, relative to the project directory (`Lib.fsi`, `Lib.fs`).
    pub name: String,
    pub text: String,
}

/// One project of a [`ProjectGraphFixture`]. Its name is its directory, its
/// `.fsproj`'s stem, its project id and its assembly name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureProject {
    pub name: PlainName,
    /// Compile order.
    pub files: Vec<FixtureFile>,
    pub project_refs: Vec<PlainName>,
    /// `#if` symbols, beyond what the SDK defines for a build. A source
    /// that tests an SDK symbol (`NET`, `RELEASE`) reads differently built
    /// and checked from source, since only the build defines it.
    pub defines: Vec<String>,
}

/// A set of F# projects in a fresh directory: `<root>/<name>/<name>.fsproj`
/// beside the project's sources. Removed when dropped.
///
/// Each `.fsproj` builds the project exactly as the oracle checks it from
/// source: its Compile items and nothing else. The SDK's generated
/// `AssemblyInfo.fs` (which declares namespace `FSharp` and the
/// `InternalsVisibleTo` items) and its `AssemblyAttributes.fs` (the
/// `TargetFrameworkAttribute`) are turned off, so a built DLL and a source
/// reference declare the same entities and the same assembly attributes.
#[derive(Debug)]
pub struct ProjectGraphFixture {
    /// Owns the directory.
    _dir: tempfile::TempDir,
    /// The directory's canonical path: what both the build and the oracle are
    /// given, so the ranges a built DLL's signature carries name the same
    /// files the oracle's source reference does.
    root: PathBuf,
    projects: Vec<FixtureProject>,
}

impl ProjectGraphFixture {
    /// Write `projects` to a fresh directory.
    pub fn materialise(projects: Vec<FixtureProject>) -> Result<Self, GraphError> {
        // The graph rules are the request's: check them on a stand-in request
        // before writing anything.
        let stand_in: Vec<GraphProject> = projects
            .iter()
            .map(|p| GraphProject {
                id: p.name.clone(),
                assembly_name: p.name.clone(),
                paths: vec![PathBuf::from("/").join(p.name.as_str())],
                refs: Vec::new(),
                defines: Vec::new(),
                lang_version: None,
                exclusive_refs: false,
                project_refs: p.project_refs.clone(),
            })
            .collect();
        for p in &projects {
            if p.files.is_empty() {
                return Err(GraphError::NoPaths(p.name.clone()));
            }
            GraphRequest::new(stand_in.clone(), p.name.clone())?;
        }

        let dir = tempfile::Builder::new()
            .prefix("borzoi-project-graph-")
            .tempdir()
            .expect("create a project-graph fixture directory");
        let root = dir
            .path()
            .canonicalize()
            .expect("canonicalise the fixture directory");
        let fixture = ProjectGraphFixture {
            _dir: dir,
            root,
            projects,
        };
        for p in &fixture.projects {
            let project_dir = fixture.dir(&p.name);
            std::fs::create_dir_all(&project_dir).expect("create a fixture project directory");
            for f in &p.files {
                std::fs::write(project_dir.join(&f.name), &f.text).expect("write a fixture source");
            }
            std::fs::write(fixture.fsproj(&p.name), fsproj_text(p))
                .expect("write a fixture .fsproj");
        }
        Ok(fixture)
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn projects(&self) -> &[FixtureProject] {
        &self.projects
    }

    /// The project named `name`. Panics if there is none: every name a test
    /// holds came from the fixture it is asking.
    pub fn project(&self, name: &PlainName) -> &FixtureProject {
        self.projects
            .iter()
            .find(|p| &p.name == name)
            .unwrap_or_else(|| panic!("the fixture has no project {name}"))
    }

    pub fn dir(&self, name: &PlainName) -> PathBuf {
        self.root.join(name.as_str())
    }

    pub fn fsproj(&self, name: &PlainName) -> PathBuf {
        self.dir(name).join(format!("{name}.fsproj"))
    }

    /// `name`'s sources, absolute, in Compile order.
    pub fn paths(&self, name: &PlainName) -> Vec<PathBuf> {
        let dir = self.dir(name);
        self.project(name)
            .files
            .iter()
            .map(|f| dir.join(&f.name))
            .collect()
    }

    /// Where [`build_fixtures`] puts `name`'s assembly.
    pub fn output_dll(&self, name: &PlainName) -> PathBuf {
        self.dir(name)
            .join("bin")
            .join("Release")
            .join(FIXTURE_TFM)
            .join(format!("{name}.dll"))
    }

    /// Every project `name` reaches through its references, in dependency
    /// order (a project after everything it references), `name` excluded.
    pub fn closure(&self, name: &PlainName) -> Vec<&FixtureProject> {
        fn visit<'a>(
            fixture: &'a ProjectGraphFixture,
            name: &PlainName,
            seen: &mut BTreeSet<PlainName>,
            out: &mut Vec<&'a FixtureProject>,
        ) {
            if !seen.insert(name.clone()) {
                return;
            }
            let p = fixture.project(name);
            for r in &p.project_refs {
                visit(fixture, r, seen, out);
            }
            out.push(p);
        }
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        visit(self, name, &mut seen, &mut out);
        out.pop();
        out
    }

    fn graph_project(
        &self,
        p: &FixtureProject,
        refs: Vec<PathBuf>,
        project_refs: Vec<PlainName>,
    ) -> GraphProject {
        GraphProject {
            id: p.name.clone(),
            assembly_name: p.name.clone(),
            paths: self.paths(&p.name),
            refs,
            defines: p.defines.clone(),
            lang_version: None,
            exclusive_refs: false,
            project_refs,
        }
    }

    /// Check `check` with every project it reaches passed from source, each
    /// checked with its own defines and its own references.
    pub fn source_request(&self, check: &PlainName) -> GraphRequest {
        let projects = self
            .closure(check)
            .into_iter()
            .chain(std::iter::once(self.project(check)))
            .map(|p| self.graph_project(p, Vec::new(), p.project_refs.clone()))
            .collect();
        GraphRequest::new(projects, check.clone()).expect("a materialised fixture is a graph")
    }

    /// Check `check` alone, with every project it reaches passed as the DLL
    /// [`build_fixtures`] built for it. Panics if one is missing.
    pub fn dll_request(&self, check: &PlainName) -> GraphRequest {
        let refs = self
            .closure(check)
            .into_iter()
            .map(|p| {
                let dll = self.output_dll(&p.name);
                assert!(dll.is_file(), "{} was not built", dll.display());
                dll
            })
            .collect();
        let project = self.graph_project(self.project(check), refs, Vec::new());
        GraphRequest::new(vec![project], check.clone()).expect("one project is a graph")
    }
}

/// The `.fsproj` for `p`. See [`ProjectGraphFixture`] for what it turns off.
fn fsproj_text(p: &FixtureProject) -> String {
    let compile: String = p
        .files
        .iter()
        .map(|f| format!("    <Compile Include=\"{}\" />\n", xml_escape(&f.name)))
        .collect();
    let refs: String = p
        .project_refs
        .iter()
        .map(|r| format!("    <ProjectReference Include=\"../{r}/{r}.fsproj\" />\n"))
        .collect();
    let defines: String = p
        .defines
        .iter()
        .map(|d| format!(";{}", xml_escape(d)))
        .collect();
    format!(
        r#"<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>{FIXTURE_TFM}</TargetFramework>
    <AssemblyName>{name}</AssemblyName>
    <GenerateAssemblyInfo>false</GenerateAssemblyInfo>
    <GenerateTargetFrameworkAttribute>false</GenerateTargetFrameworkAttribute>
    <GenerateDocumentationFile>false</GenerateDocumentationFile>
    <DefineConstants>$(DefineConstants){defines}</DefineConstants>
    <Deterministic>true</Deterministic>
    <DeterministicSourcePaths>false</DeterministicSourcePaths>
    <ContinuousIntegrationBuild>false</ContinuousIntegrationBuild>
    <PathMap></PathMap>
    <DebugType>none</DebugType>
    <DebugSymbols>false</DebugSymbols>
    <TreatWarningsAsErrors>false</TreatWarningsAsErrors>
  </PropertyGroup>
  <ItemGroup>
{compile}  </ItemGroup>
  <ItemGroup>
{refs}  </ItemGroup>
</Project>
"#,
        name = p.name,
    )
}

fn xml_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Budget for one [`build_fixtures`] build: a cold one restores packages for
/// every project it builds. It is there to stop a build stalled on a NuGet
/// lock a sibling worktree holds, not to police a slow one.
const BUILD_TIMEOUT: Duration = Duration::from_secs(1800);

/// Build `fsprojs` (each a fixture project's [`ProjectGraphFixture::fsproj`])
/// with one `dotnet build` of a solution listing them all, so MSBuild builds
/// them in one process and in parallel. Panics, with the build's output, if
/// it fails.
pub fn build_fixtures(fsprojs: &[PathBuf]) {
    let dir = tempfile::Builder::new()
        .prefix("borzoi-project-graph-build-")
        .tempdir()
        .expect("create a solution directory");
    let solution = dir.path().join("fixtures.slnx");
    let entries: String = fsprojs
        .iter()
        .map(|p| {
            format!(
                "  <Project Path=\"{}\" />\n",
                xml_escape(&p.display().to_string())
            )
        })
        .collect();
    std::fs::write(&solution, format!("<Solution>\n{entries}</Solution>\n"))
        .expect("write the fixture solution");
    let mut cmd = Command::new("dotnet");
    cmd.args(["build", "-c", "Release", "--nologo", "-v:q"])
        .arg(&solution);
    BoundedCommand::new(cmd)
        .timeout(BUILD_TIMEOUT)
        .run_ok("dotnet build the project-graph fixtures");
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn name(s: &str) -> PlainName {
        PlainName::new(s).expect("plain")
    }

    fn project(id: &str, refs: &[&str]) -> GraphProject {
        GraphProject {
            id: name(id),
            assembly_name: name(&format!("Asm{id}")),
            paths: vec![PathBuf::from(format!("/src/{id}.fs"))],
            refs: Vec::new(),
            defines: Vec::new(),
            lang_version: None,
            exclusive_refs: false,
            project_refs: refs.iter().map(|r| name(r)).collect(),
        }
    }

    #[test]
    fn plain_names_are_what_fcs_dump_accepts() {
        for ok in ["A", "WoofWare.Expect", "a-b_c.1"] {
            assert!(PlainName::new(ok).is_ok(), "{ok}");
        }
        for bad in ["", "a b", "a/b", "a,Version=1.0", "é"] {
            assert_eq!(
                PlainName::new(bad),
                Err(GraphError::NotPlain(bad.to_owned()))
            );
        }
    }

    #[test]
    fn a_request_names_its_checked_project_and_every_reference() {
        let r = GraphRequest::new(vec![project("a", &[]), project("b", &["a"])], name("b"))
            .expect("a graph");
        let json: Value = serde_json::from_str(&r.to_json_line()).expect("json");
        assert_eq!(json["check"], "b");
        assert_eq!(json["projects"][1]["projectRefs"], serde_json::json!(["a"]));
        assert_eq!(json["projects"][1]["assemblyName"], "Asmb");
    }

    #[test]
    fn a_request_refuses_what_the_oracle_would() {
        let fsharp_core = GraphProject {
            assembly_name: name("FSharp.Core"),
            ..project("a", &[])
        };
        assert_eq!(
            GraphRequest::new(vec![fsharp_core], name("a")),
            Err(GraphError::FSharpCoreName(name("a")))
        );
        assert_eq!(
            GraphRequest::new(vec![project("a", &["z"])], name("a")),
            Err(GraphError::UnknownReference {
                from: name("a"),
                to: name("z")
            })
        );
        assert_eq!(
            GraphRequest::new(vec![project("a", &[])], name("z")),
            Err(GraphError::UnknownCheck(name("z")))
        );
        let twin = GraphProject {
            id: name("b"),
            ..project("a", &[])
        };
        assert_eq!(
            GraphRequest::new(vec![project("a", &[]), twin], name("a")),
            Err(GraphError::DuplicateAssemblyName(name("Asma")))
        );
        let relative = GraphProject {
            paths: vec![PathBuf::from("a.fs")],
            ..project("a", &[])
        };
        assert_eq!(
            GraphRequest::new(vec![relative], name("a")),
            Err(GraphError::RelativePath(PathBuf::from("a.fs")))
        );
    }

    /// Whether the reference relation over `n` nodes has a cycle, by repeatedly
    /// removing nodes nothing references (Kahn): an implementation independent
    /// of [`first_cycle`]'s depth-first walk.
    fn has_cycle_by_kahn(n: usize, edges: &[(usize, usize)]) -> bool {
        let mut alive: BTreeSet<usize> = (0..n).collect();
        loop {
            let leaf = alive.iter().copied().find(|&v| {
                !edges
                    .iter()
                    .any(|&(from, to)| from == v && alive.contains(&to))
            });
            match leaf {
                Some(v) => {
                    alive.remove(&v);
                }
                None => return !alive.is_empty(),
            }
        }
    }

    proptest! {
        /// A request is refused for a cycle exactly when the graph has one.
        #[test]
        fn a_cycle_is_refused_exactly_when_there_is_one(
            n in 1usize..6,
            raw in proptest::collection::vec((0usize..6, 0usize..6), 0..10),
        ) {
            let edges: Vec<(usize, usize)> =
                raw.into_iter().map(|(a, b)| (a % n, b % n)).collect();
            let projects: Vec<GraphProject> = (0..n)
                .map(|i| {
                    let refs: Vec<String> = edges
                        .iter()
                        .filter(|&&(from, _)| from == i)
                        .map(|&(_, to)| format!("p{to}"))
                        .collect();
                    let refs: Vec<&str> = refs.iter().map(String::as_str).collect();
                    project(&format!("p{i}"), &refs)
                })
                .collect();
            let refused = matches!(
                GraphRequest::new(projects, name("p0")),
                Err(GraphError::Cycle(_))
            );
            prop_assert_eq!(refused, has_cycle_by_kahn(n, &edges));
        }
    }

    #[test]
    fn a_fixture_lays_out_buildable_projects_and_both_requests() {
        let fixture = ProjectGraphFixture::materialise(vec![
            FixtureProject {
                name: name("Lib"),
                files: vec![FixtureFile {
                    name: "Lib.fs".into(),
                    text: "module Lib\nlet x = 1\n".into(),
                }],
                project_refs: Vec::new(),
                defines: vec!["LIB_ONLY".into()],
            },
            FixtureProject {
                name: name("App"),
                files: vec![FixtureFile {
                    name: "Program.fs".into(),
                    text: "module Program\nlet y = Lib.x\n".into(),
                }],
                project_refs: vec![name("Lib")],
                defines: Vec::new(),
            },
        ])
        .expect("a graph");
        let app = fixture.fsproj(&name("App"));
        let text = std::fs::read_to_string(&app).expect("read the .fsproj");
        assert!(text.contains(r#"<ProjectReference Include="../Lib/Lib.fsproj" />"#));
        assert!(text.contains("<GenerateAssemblyInfo>false</GenerateAssemblyInfo>"));
        let lib = std::fs::read_to_string(fixture.fsproj(&name("Lib"))).expect("read");
        assert!(lib.contains("<DefineConstants>$(DefineConstants);LIB_ONLY</DefineConstants>"));

        let source = fixture.source_request(&name("App"));
        let ids: Vec<&str> = source.projects().iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, ["Lib", "App"]);
        assert_eq!(source.projects()[0].defines, ["LIB_ONLY"]);
        assert_eq!(source.projects()[1].project_refs, [name("Lib")]);
        assert!(source.projects()[1].paths[0].starts_with(fixture.root()));
    }

    #[test]
    fn a_fixture_refuses_a_cycle_before_writing() {
        let p = |n: &str, r: &str| FixtureProject {
            name: name(n),
            files: vec![FixtureFile {
                name: "A.fs".into(),
                text: String::new(),
            }],
            project_refs: vec![name(r)],
            defines: Vec::new(),
        };
        assert!(matches!(
            ProjectGraphFixture::materialise(vec![p("A", "B"), p("B", "A")]),
            Err(GraphError::Cycle(_))
        ));
    }
}
