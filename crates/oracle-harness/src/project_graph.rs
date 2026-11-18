//! Project graphs for `fcs-dump uses-project-graph-batch`, and the
//! multi-project fixture layout the graph differentials share.
//!
//! FCS references an F# project the way an IDE does when it is handed the
//! project as an `FSharpReferencedProject.FSharpReference`: it type-checks the
//! referenced project's sources and reads its signature from memory. That is
//! the semantics borzoi resolves `<ProjectReference>`s against, so it is the
//! oracle. A [`GraphRequest`] describes one such check: each project's own fsc
//! arguments (what its build hands fsc, read off a design-time build by
//! [`msbuild_oracle`](crate::msbuild_oracle)), which of their `-r:` arguments
//! are projects of the request, and the project whose files to report.
//! `fcs-dump` parses the request, once and strictly, into the only value its
//! checking code reads, and re-derives none of the compiler's inputs.
//!
//! A [`ProjectGraphFixture`] is a set of F# projects written to a fresh
//! directory, one subdirectory per project with its sources and a buildable
//! `.fsproj`. It answers both questions a graph differential asks: what FCS
//! says with each reference passed from source
//! ([`ProjectGraphFixture::source_request`]), and what it says with each
//! reference built and passed as the DLL its build compiles against
//! ([`build_fixtures`], [`ProjectGraphFixture::dll_request`]). The two
//! requests hand FCS one argument list and differ only in whether a project
//! reference's `-r:` is registered as a project.
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
use crate::msbuild_oracle::Oracle;

/// The target framework every fixture project builds for.
pub const FIXTURE_TFM: &str = "net10.0";

/// The language version every fixture project builds at. A project's own
/// arguments must name one: left unnamed, the build checks at its compiler's
/// default and FCS at its own, newer one's, so the oracle refuses the
/// request.
pub const FIXTURE_LANG_VERSION: &str = "10.0";

/// The configuration fixtures are built and read under.
pub const FIXTURE_CONFIGURATION: &str = "Release";

/// A name `fcs-dump` accepts as a project id: a non-empty run of ASCII
/// letters, digits, `.`, `_` and `-`, other than `.` and `..`, so it names
/// one ordinary file or directory without escaping.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PlainName(String);

impl PlainName {
    /// `name`, if it is plain.
    pub fn new(name: &str) -> Result<Self, GraphError> {
        let plain = !name.is_empty()
            && name != "."
            && name != ".."
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
    /// What other projects' [`ProjectRef`]s name it by.
    pub id: PlainName,
    /// Its project file, absolute: FCS's `ProjectFileName`, whose directory
    /// relative arguments and project-relative inputs (a type provider's
    /// sample file) resolve from, as in the build.
    pub project_file: PathBuf,
    /// Its fsc arguments, one response-file line each, as its build hands
    /// them to fsc (`FscInvocation::response_file`). `fcs-dump` passes them
    /// to FCS as they stand, but for the mappings it states, and refuses a
    /// list outside the domain it reads as fsc does.
    pub args: Vec<String>,
    /// The `-r:` arguments of [`args`](Self::args) that are projects of the
    /// same request, passed from source.
    pub project_refs: Vec<ProjectRef>,
}

/// One `-r:` argument of a [`GraphProject`] registered as another project of
/// the request: FCS is handed that project as an `FSharpReference` whose
/// output file is exactly the argument, in the argument's place.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectRef {
    pub project: PlainName,
    /// The `-r:` argument, exactly as in the project's arguments.
    pub reference: String,
}

/// Why a [`GraphRequest`] or a [`ProjectGraphFixture`] is not a graph
/// `fcs-dump` checks as described. The shape of the graph only: `fcs-dump`
/// is the one judge of the arguments themselves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GraphError {
    /// A project id that is not a [`PlainName`].
    NotPlain(String),
    DuplicateId(PlainName),
    /// Two projects with one project file.
    DuplicateProjectFile(PathBuf),
    UnknownReference {
        from: PlainName,
        to: PlainName,
    },
    /// A [`ProjectRef`] whose reference is not one `-r:` argument of its
    /// project.
    ReferenceNotInArgs {
        from: PlainName,
        reference: String,
    },
    /// A reference cycle through this project.
    Cycle(PlainName),
    /// The project to check is not one of the request's.
    UnknownCheck(PlainName),
    /// A project file that is not absolute.
    RelativePath(PathBuf),
    /// A path that is not UTF-8, which the JSON wire cannot carry unchanged.
    NotUtf8(PathBuf),
    /// A fixture project with no source.
    NoSources(PlainName),
    /// A fixture source name that is not a `/`-separated path of plain names.
    UncontainedFile(String),
}

impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GraphError::NotPlain(s) => write!(f, "{s:?} is not a plain name"),
            GraphError::DuplicateId(id) => write!(f, "two projects have the id {id}"),
            GraphError::DuplicateProjectFile(p) => {
                write!(f, "two projects have the project file {}", p.display())
            }
            GraphError::UnknownReference { from, to } => {
                write!(f, "project {from} references unknown project {to}")
            }
            GraphError::ReferenceNotInArgs { from, reference } => {
                write!(f, "project {from} has no single -r:{reference} argument")
            }
            GraphError::Cycle(id) => write!(f, "project reference cycle through {id}"),
            GraphError::UnknownCheck(id) => write!(f, "no project {id} to check"),
            GraphError::RelativePath(p) => write!(f, "{} is not absolute", p.display()),
            GraphError::NotUtf8(p) => write!(f, "{} is not UTF-8", p.display()),
            GraphError::NoSources(id) => write!(f, "project {id} has no source files"),
            GraphError::UncontainedFile(n) => {
                write!(f, "{n:?} is not a relative path of plain names")
            }
        }
    }
}

impl std::error::Error for GraphError {}

/// A request for `fcs-dump uses-project-graph-batch`: check
/// [`check`](Self::check)'s files, with every project it reaches through its
/// [`ProjectRef`]s passed from source. Built only through
/// [`GraphRequest::new`], which refuses a graph that is not one; `fcs-dump`
/// then refuses arguments outside its domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphRequest {
    projects: Vec<GraphProject>,
    check: PlainName,
}

/// The `-r:` arguments of `args`, in order.
fn references_in(args: &[String]) -> impl Iterator<Item = &str> {
    args.iter().filter_map(|line| {
        line.strip_prefix("-r:")
            .or_else(|| line.strip_prefix("--reference:"))
    })
}

impl GraphRequest {
    pub fn new(projects: Vec<GraphProject>, check: PlainName) -> Result<Self, GraphError> {
        let mut by_id = BTreeMap::new();
        let mut project_files = BTreeSet::new();
        for p in &projects {
            if !p.project_file.is_absolute() {
                return Err(GraphError::RelativePath(p.project_file.clone()));
            }
            if p.project_file.to_str().is_none() {
                return Err(GraphError::NotUtf8(p.project_file.clone()));
            }
            if by_id.insert(p.id.clone(), p).is_some() {
                return Err(GraphError::DuplicateId(p.id.clone()));
            }
            if !project_files.insert(&p.project_file) {
                return Err(GraphError::DuplicateProjectFile(p.project_file.clone()));
            }
        }
        for p in &projects {
            for r in &p.project_refs {
                if !by_id.contains_key(&r.project) {
                    return Err(GraphError::UnknownReference {
                        from: p.id.clone(),
                        to: r.project.clone(),
                    });
                }
                if references_in(&p.args).filter(|a| *a == r.reference).count() != 1 {
                    return Err(GraphError::ReferenceNotInArgs {
                        from: p.id.clone(),
                        reference: r.reference.clone(),
                    });
                }
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
        let projects: Vec<Value> = self
            .projects
            .iter()
            .map(|p| {
                serde_json::json!({
                    "id": p.id.as_str(),
                    "projectFile": p.project_file.to_str().expect("checked UTF-8"),
                    "args": p.args,
                    "projectRefs": p.project_refs.iter().map(|r| serde_json::json!({
                        "project": r.project.as_str(),
                        "reference": r.reference,
                    })).collect::<Vec<_>>(),
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
            if let Some(cycle) = visit(&r.project, by_id, marks) {
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
    /// The file stem of its `-o:` argument: the assembly name fsc gives it.
    #[serde(rename = "AssemblyName")]
    pub assembly_name: String,
    /// Its `-o:` argument, made absolute.
    #[serde(rename = "OutputPath")]
    pub output_path: PathBuf,
    /// Its whole-project diagnostics, as `uses-project` renders a file's.
    #[serde(rename = "Diagnostics")]
    pub diagnostics: Vec<Value>,
}

impl ReferencedProject {
    /// Its error-severity diagnostics.
    pub fn errors(&self) -> impl Iterator<Item = &Value> {
        errors_of(&self.diagnostics)
    }
}

impl GraphResponse {
    /// The checked project's error-severity whole-project diagnostics.
    pub fn errors(&self) -> impl Iterator<Item = &Value> {
        errors_of(&self.diagnostics)
    }
}

fn errors_of(diagnostics: &[Value]) -> impl Iterator<Item = &Value> {
    diagnostics.iter().filter(|d| {
        d.get("Severity")
            .and_then(Value::as_str)
            .is_some_and(|s| s.eq_ignore_ascii_case("Error"))
    })
}

/// What `uses-project-graph-batch` answers: the `uses-project` records of the
/// checked project's files, kept as JSON so that two answers can be compared
/// whole, its whole-project diagnostics, and the projects it referenced.
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct GraphResponse {
    #[serde(rename = "Files")]
    pub files: Vec<Value>,
    /// The checked project's whole-project diagnostics: what its files'
    /// checks report and what only a project check finds (FS0240, a
    /// signature with no implementation).
    #[serde(rename = "Diagnostics")]
    pub diagnostics: Vec<Value>,
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
    /// `#if` symbols beyond the SDK's.
    pub defines: Vec<String>,
    /// Assemblies on disk it references (`<Reference>` with a `HintPath`),
    /// absolute.
    pub assembly_refs: Vec<PathBuf>,
}

impl FixtureProject {
    /// A project with these sources, and no references or defines.
    pub fn new(name: PlainName, files: Vec<FixtureFile>) -> Self {
        FixtureProject {
            name,
            files,
            project_refs: Vec::new(),
            defines: Vec::new(),
            assembly_refs: Vec::new(),
        }
    }
}

/// A set of F# projects in a fresh directory: `<root>/<name>/<name>.fsproj`
/// beside the project's sources. Removed when dropped.
///
/// The SDK's generated `AssemblyInfo.fs` (which declares namespace `FSharp`
/// and the `InternalsVisibleTo` items) and `AssemblyAttributes.fs` (the
/// `TargetFrameworkAttribute`) are turned off, so a fixture declares only
/// what its sources do.
#[derive(Debug)]
pub struct ProjectGraphFixture {
    /// Owns the directory.
    _dir: tempfile::TempDir,
    /// The directory's canonical path, which the build and the oracle are
    /// both given.
    root: PathBuf,
    projects: Vec<FixtureProject>,
}

/// Each fixture project's fsc arguments, as its build hands them to fsc:
/// one response-file line each.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureArgs(BTreeMap<PlainName, Vec<String>>);

impl FixtureArgs {
    /// The arguments of the project named `name`.
    pub fn of(&self, name: &PlainName) -> &[String] {
        self.0
            .get(name)
            .unwrap_or_else(|| panic!("no fsc arguments for {name}"))
    }
}

/// The `msbuild-condition-oracle` child fixtures read their fsc arguments
/// through, in the oracle's scrubbed environment. Its requests pin each
/// design-time build's restore to the feed this process restores from
/// ([`crate::msbuild_oracle::restore_sources`]).
pub fn fixture_msbuild_oracle() -> Oracle {
    Oracle::spawn_in_dir_with_env(&std::env::temp_dir(), &[])
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
                project_file: PathBuf::from("/").join(format!("{}.fsproj", p.name)),
                args: p
                    .project_refs
                    .iter()
                    .map(|r| format!("-r:/{r}.dll"))
                    .collect(),
                project_refs: p
                    .project_refs
                    .iter()
                    .map(|r| ProjectRef {
                        project: r.clone(),
                        reference: format!("/{r}.dll"),
                    })
                    .collect(),
            })
            .collect();
        for p in &projects {
            if p.files.is_empty() {
                return Err(GraphError::NoSources(p.name.clone()));
            }
            if let Some(f) = p.files.iter().find(|f| !is_contained(&f.name)) {
                return Err(GraphError::UncontainedFile(f.name.clone()));
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
                let path = project_dir.join(&f.name);
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent).expect("create a fixture source directory");
                }
                std::fs::write(path, &f.text).expect("write a fixture source");
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

    /// Every project `name` reaches through its references, in dependency
    /// order (a project after everything it references), `name` excluded.
    /// The SDK hands a build each of these, transitive ones included.
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

    /// Every project's fsc arguments, read off a design-time build of it
    /// under [`FIXTURE_CONFIGURATION`] (`oracle` is
    /// [`fixture_msbuild_oracle`]). Panics when the build reports none, or
    /// says fsc may run on arguments it cannot report: such a fixture cannot
    /// be graded.
    pub fn fsc_args(&self, oracle: &mut Oracle) -> FixtureArgs {
        let globals = [("Configuration".to_owned(), FIXTURE_CONFIGURATION.to_owned())];
        FixtureArgs(
            self.projects
                .iter()
                .map(|p| {
                    let invocation = oracle
                        .fsc_args(&self.fsproj(&p.name), &globals)
                        .unwrap_or_else(|errors| {
                            panic!(
                                "no fsc arguments for fixture project {}: {errors:?}",
                                p.name
                            )
                        });
                    let lines = invocation
                        .response_file
                        .lines()
                        .filter(|l| !l.is_empty())
                        .map(str::to_owned)
                        .collect();
                    (p.name.clone(), lines)
                })
                .collect(),
        )
    }

    /// The `-r:` argument in `p`'s arguments that is project `q`: the one
    /// whose file lies in `q`'s directory and is named after `q`. Panics
    /// unless exactly one is.
    fn reference_to(&self, args: &FixtureArgs, p: &PlainName, q: &PlainName) -> String {
        let dir = format!("{}/", self.dir(q).display());
        let found: Vec<&str> = references_in(args.of(p))
            .filter(|r| {
                r.starts_with(&dir)
                    && Path::new(r).file_stem().and_then(|s| s.to_str()) == Some(q.as_str())
            })
            .collect();
        match found.as_slice() {
            [one] => (*one).to_owned(),
            other => panic!(
                "{p}'s arguments reference {q} {} times: {other:?}",
                other.len()
            ),
        }
    }

    /// Check `check` with every project it reaches passed from source: each
    /// project's own arguments, with the `-r:` of every project in its
    /// [`closure`](Self::closure) registered as that project.
    pub fn source_request(&self, args: &FixtureArgs, check: &PlainName) -> GraphRequest {
        let projects = self
            .closure(check)
            .into_iter()
            .chain(std::iter::once(self.project(check)))
            .map(|p| GraphProject {
                id: p.name.clone(),
                project_file: self.fsproj(&p.name),
                args: args.of(&p.name).to_vec(),
                project_refs: self
                    .closure(&p.name)
                    .into_iter()
                    .map(|q| ProjectRef {
                        project: q.name.clone(),
                        reference: self.reference_to(args, &p.name, &q.name),
                    })
                    .collect(),
            })
            .collect();
        GraphRequest::new(projects, check.clone()).expect("a materialised fixture is a graph")
    }

    /// Check `check` alone, with its arguments as they stand: every project
    /// reference is then the DLL [`build_fixtures`] built for it, at the
    /// path the build compiles against. Panics if one is missing.
    pub fn dll_request(&self, args: &FixtureArgs, check: &PlainName) -> GraphRequest {
        for q in self.closure(check) {
            let dll = self.reference_to(args, check, &q.name);
            assert!(Path::new(&dll).is_file(), "{dll} was not built");
        }
        let project = GraphProject {
            id: check.clone(),
            project_file: self.fsproj(check),
            args: args.of(check).to_vec(),
            project_refs: Vec::new(),
        };
        GraphRequest::new(vec![project], check.clone()).expect("one project is a graph")
    }
}

/// Whether `name` is a `/`-separated relative path of [`PlainName`]s: a
/// positive domain every reader spells alike, so joining it to a project
/// directory stays inside it, and MSBuild reads the `Compile` item as the
/// file written (no list separator, escape, expression, wildcard,
/// backslash or whitespace for it to read differently).
fn is_contained(name: &str) -> bool {
    !name.is_empty() && name.split('/').all(|c| PlainName::new(c).is_ok())
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
        .chain(p.assembly_refs.iter().map(|path| {
            let path = xml_escape(&path.display().to_string());
            format!("    <Reference Include=\"{path}\"><HintPath>{path}</HintPath></Reference>\n")
        }))
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
    <LangVersion>{FIXTURE_LANG_VERSION}</LangVersion>
    <GenerateAssemblyInfo>false</GenerateAssemblyInfo>
    <GenerateTargetFrameworkAttribute>false</GenerateTargetFrameworkAttribute>
    <GenerateDocumentationFile>false</GenerateDocumentationFile>
    <DefineConstants>$(DefineConstants){defines}</DefineConstants>
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
/// under [`FIXTURE_CONFIGURATION`] with one `dotnet build` of a solution
/// listing them all, so MSBuild builds them in one process and in parallel.
/// Each sits in a solution folder of its own, so projects of different
/// fixtures may share a name. Panics, with the build's output, if it fails.
pub fn build_fixtures(fsprojs: &[PathBuf]) {
    let dir = tempfile::Builder::new()
        .prefix("borzoi-project-graph-build-")
        .tempdir()
        .expect("create a solution directory");
    let solution = dir.path().join("fixtures.slnx");
    let entries: String = fsprojs
        .iter()
        .enumerate()
        .map(|(i, p)| {
            format!(
                "  <Folder Name=\"/p{i}/\">\n    <Project Path=\"{}\" />\n  </Folder>\n",
                xml_escape(&p.display().to_string())
            )
        })
        .collect();
    std::fs::write(&solution, format!("<Solution>\n{entries}</Solution>\n"))
        .expect("write the fixture solution");
    let mut cmd = Command::new("dotnet");
    cmd.args(["build", "-c", FIXTURE_CONFIGURATION, "--nologo", "-v:q"])
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
            project_file: PathBuf::from(format!("/src/{id}/{id}.fsproj")),
            args: refs.iter().map(|r| format!("-r:/out/{r}.dll")).collect(),
            project_refs: refs
                .iter()
                .map(|r| ProjectRef {
                    project: name(r),
                    reference: format!("/out/{r}.dll"),
                })
                .collect(),
        }
    }

    #[test]
    fn plain_names_are_what_fcs_dump_accepts() {
        for ok in ["A", "WoofWare.Expect", "a-b_c.1"] {
            assert!(PlainName::new(ok).is_ok(), "{ok}");
        }
        for bad in ["", ".", "..", "a b", "a/b", "a,Version=1.0", "é"] {
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
        assert_eq!(
            json["projects"][1]["projectRefs"],
            serde_json::json!([{ "project": "a", "reference": "/out/a.dll" }])
        );
        assert_eq!(
            json["projects"][1]["args"],
            serde_json::json!(["-r:/out/a.dll"])
        );
    }

    #[test]
    fn a_request_refuses_a_malformed_graph() {
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
        let elsewhere = GraphProject {
            project_file: PathBuf::from("/src/a/a.fsproj"),
            ..project("b", &[])
        };
        assert_eq!(
            GraphRequest::new(vec![project("a", &[]), elsewhere], name("a")),
            Err(GraphError::DuplicateProjectFile(PathBuf::from(
                "/src/a/a.fsproj"
            )))
        );
        let relative = GraphProject {
            project_file: PathBuf::from("a.fsproj"),
            ..project("a", &[])
        };
        assert_eq!(
            GraphRequest::new(vec![relative], name("a")),
            Err(GraphError::RelativePath(PathBuf::from("a.fsproj")))
        );
        // A project reference must name one of the project's own `-r:`s.
        let unargued = GraphProject {
            args: Vec::new(),
            ..project("b", &["a"])
        };
        assert_eq!(
            GraphRequest::new(vec![project("a", &[]), unargued], name("b")),
            Err(GraphError::ReferenceNotInArgs {
                from: name("b"),
                reference: "/out/a.dll".to_owned()
            })
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_request_refuses_a_path_json_cannot_carry() {
        use std::os::unix::ffi::OsStrExt;
        let bad = PathBuf::from(std::ffi::OsStr::from_bytes(b"/src/\xff.fsproj"));
        let p = GraphProject {
            project_file: bad.clone(),
            ..project("a", &[])
        };
        assert_eq!(
            GraphRequest::new(vec![p], name("a")),
            Err(GraphError::NotUtf8(bad))
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
            let mut edges: Vec<(usize, usize)> =
                raw.into_iter().map(|(a, b)| (a % n, b % n)).collect();
            edges.sort();
            edges.dedup();
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

    fn lib_and_app() -> ProjectGraphFixture {
        ProjectGraphFixture::materialise(vec![
            FixtureProject {
                defines: vec!["LIB_ONLY".into()],
                ..FixtureProject::new(
                    name("Lib"),
                    vec![FixtureFile {
                        name: "Lib.fs".into(),
                        text: "module Lib\nlet x = 1\n".into(),
                    }],
                )
            },
            FixtureProject {
                project_refs: vec![name("Lib")],
                assembly_refs: vec![PathBuf::from("/opt/Extra.dll")],
                ..FixtureProject::new(
                    name("App"),
                    vec![FixtureFile {
                        name: "Program.fs".into(),
                        text: "module Program\nlet y = Lib.x\n".into(),
                    }],
                )
            },
        ])
        .expect("a graph")
    }

    #[test]
    fn a_fixture_lays_out_buildable_projects() {
        let fixture = lib_and_app();
        let app = std::fs::read_to_string(fixture.fsproj(&name("App"))).expect("read");
        assert!(app.contains(r#"<ProjectReference Include="../Lib/Lib.fsproj" />"#));
        assert!(app.contains(
            r#"<Reference Include="/opt/Extra.dll"><HintPath>/opt/Extra.dll</HintPath></Reference>"#
        ));
        assert!(app.contains("<GenerateAssemblyInfo>false</GenerateAssemblyInfo>"));
        assert!(app.contains(&format!(
            "<LangVersion>{FIXTURE_LANG_VERSION}</LangVersion>"
        )));
        let lib = std::fs::read_to_string(fixture.fsproj(&name("Lib"))).expect("read");
        assert!(lib.contains("<DefineConstants>$(DefineConstants);LIB_ONLY</DefineConstants>"));
    }

    /// A source request passes each project's own arguments, and registers
    /// the `-r:` of every project in its closure; a DLL request registers
    /// none.
    #[test]
    fn a_source_request_registers_each_closure_reference() {
        let fixture = lib_and_app();
        let lib_ref = format!(
            "{}/obj/Release/net10.0/ref/Lib.dll",
            fixture.dir(&name("Lib")).display()
        );
        let args = FixtureArgs(BTreeMap::from([
            (
                name("Lib"),
                vec!["-o:obj/Lib.dll".to_owned(), "Lib.fs".to_owned()],
            ),
            (
                name("App"),
                vec![
                    "-o:obj/App.dll".to_owned(),
                    "-r:/opt/Extra.dll".to_owned(),
                    format!("-r:{lib_ref}"),
                    "Program.fs".to_owned(),
                ],
            ),
        ]));
        let source = fixture.source_request(&args, &name("App"));
        let ids: Vec<&str> = source.projects().iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, ["Lib", "App"]);
        assert_eq!(source.projects()[1].args, args.of(&name("App")));
        assert_eq!(
            source.projects()[1].project_refs,
            [ProjectRef {
                project: name("Lib"),
                reference: lib_ref
            }]
        );
        assert!(source.projects()[0].project_refs.is_empty());
    }

    /// C → B → A gives C both, as its build references both.
    #[test]
    fn a_closure_is_transitive() {
        let p = |n: &str, refs: &[&str]| FixtureProject {
            project_refs: refs.iter().map(|r| name(r)).collect(),
            ..FixtureProject::new(
                name(n),
                vec![FixtureFile {
                    name: format!("{n}.fs"),
                    text: format!("module {n}\n"),
                }],
            )
        };
        let fixture =
            ProjectGraphFixture::materialise(vec![p("A", &[]), p("B", &["A"]), p("C", &["B"])])
                .expect("a graph");
        let names: Vec<&str> = fixture
            .closure(&name("C"))
            .into_iter()
            .map(|q| q.name.as_str())
            .collect();
        assert_eq!(names, ["A", "B"]);
    }

    #[test]
    fn a_fixture_refuses_a_source_outside_its_project() {
        for bad in [
            "../Escape.fs",
            "/abs/Escape.fs",
            "a/../../b.fs",
            "",
            "a;b.fs",
            "a%3Bb.fs",
            "$(X).fs",
            "*.fs",
            "..\\Outside.fs",
            "  Foo.fs  ",
            "a b.fs",
            "a//b.fs",
        ] {
            let p = FixtureProject::new(
                name("A"),
                vec![FixtureFile {
                    name: bad.into(),
                    text: String::new(),
                }],
            );
            assert_eq!(
                ProjectGraphFixture::materialise(vec![p]).map(|_| ()),
                Err(GraphError::UncontainedFile(bad.into())),
                "{bad}"
            );
        }
    }

    #[test]
    fn a_fixture_writes_a_nested_source() {
        let fixture = ProjectGraphFixture::materialise(vec![FixtureProject::new(
            name("A"),
            vec![FixtureFile {
                name: "src/Lib.fs".into(),
                text: "module Lib\n".into(),
            }],
        )])
        .expect("a graph");
        assert!(fixture.paths(&name("A"))[0].is_file());
    }

    #[test]
    fn a_fixture_refuses_a_cycle_before_writing() {
        let p = |n: &str, r: &str| FixtureProject {
            project_refs: vec![name(r)],
            ..FixtureProject::new(
                name(n),
                vec![FixtureFile {
                    name: "A.fs".into(),
                    text: String::new(),
                }],
            )
        };
        assert!(matches!(
            ProjectGraphFixture::materialise(vec![p("A", "B"), p("B", "A")]),
            Err(GraphError::Cycle(_))
        ));
    }
}
