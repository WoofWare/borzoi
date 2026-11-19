//! Project graphs for `fcs-dump uses-project-graph-batch`, and the fixture
//! layout the graph differentials share.
//!
//! FCS references an F# project the way an IDE does when it is handed the
//! project as an `FSharpReferencedProject.FSharpReference`: it checks the
//! project's sources and reads its signature from memory. That is the
//! semantics borzoi resolves `<ProjectReference>`s against, so it is the
//! oracle. A [`GraphRequest`] describes one such check as values: each
//! project's id, assembly name, target, sources, defines and references, a
//! reference being a DLL or a project of the request. `fcs-dump` builds the
//! fsc argument vector from one template (no framework but the references, a
//! fixed language version, the assembly name as `-o:`), so no raw compiler
//! switch crosses the wire, and the references are exactly the list the
//! borzoi side loads. The same template drives `fcs-dump`'s `compile` op,
//! which builds a project's DLL with FCS's own compiler.
//!
//! # D1(G, C)
//!
//! What the graph differential (`corpus-diff`'s `source_references` tests)
//! checks, and all it claims: over the generator's domain G (generated
//! library, middle and consumer projects, `source_reference_gen`), in
//! currency C (the consumer's whole-project file records and diagnostics,
//! `GraphResponse::files` and `GraphResponse::diagnostics`), FCS checking the
//! consumer with each referenced project from source answers exactly what it
//! answers with each referenced project as the DLL FCS's compiler built on the
//! same argument vector. Its one assumption: FCS's check and FCS's compile
//! agree on one argument vector. Nothing wider is claimed: not that the
//! argument vector is any real build's, nor that anything outside C agrees.
//!
//! A [`ProjectGraphFixture`] is a set of F# projects' sources written to a
//! fresh directory, one subdirectory per project. It builds both requests the
//! differential compares ([`ProjectGraphFixture::request`]) and the compile
//! requests that make the DLLs ([`ProjectGraphFixture::compile_request`]).
//!
//! This module knows the protocol and the layout. Spawning `fcs-dump` is the
//! caller's: each crate already locates and builds it its own way.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use borzoi_spawn::BoundedCommand;
use serde_json::Value;

/// A non-empty run of ASCII letters, digits, `.`, `_` and `-`, other than `.`
/// and `..`: a project id or an assembly name, never a path or a display
/// name, so it is safe as a directory name and on the wire.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlainName(String);

impl PlainName {
    pub fn new(name: &str) -> Result<Self, String> {
        let plain = !name.is_empty()
            && name != "."
            && name != ".."
            && name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'));
        if plain {
            Ok(PlainName(name.to_owned()))
        } else {
            Err(format!("{name:?} is not a plain name"))
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

/// What a project builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Library,
    Exe,
}

impl Target {
    fn as_str(self) -> &'static str {
        match self {
            Target::Library => "library",
            Target::Exe => "exe",
        }
    }
}

/// One reference of a project, in its place in the reference order (which
/// matters: of two references declaring one name, FCS takes the later).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reference {
    /// A compiled assembly, by absolute path.
    Dll(PathBuf),
    /// A project of the same request, which FCS is handed from source.
    Project(PlainName),
}

/// One project of a [`GraphRequest`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphProject {
    pub id: PlainName,
    /// The assembly name, which `fcs-dump` passes as `-o:<dir>/<name>.dll`.
    pub assembly_name: PlainName,
    pub target: Target,
    /// Absolute source paths, in Compile order.
    pub sources: Vec<PathBuf>,
    /// Conditional-compilation symbols.
    pub defines: Vec<String>,
    /// Exactly one DLL reference is `FSharp.Core.dll`.
    pub references: Vec<Reference>,
}

impl GraphProject {
    /// Whether `fcs-dump` would accept this project, apart from how its
    /// project references resolve.
    fn validate(&self) -> Result<(), String> {
        let id = &self.id;
        if self
            .assembly_name
            .as_str()
            .eq_ignore_ascii_case("FSharp.Core")
        {
            return Err(format!("{id}: a project may not be named FSharp.Core"));
        }
        let path_ok = |p: &Path| is_normal_absolute(p);
        if self.sources.is_empty() {
            return Err(format!("{id} has no sources"));
        }
        for s in &self.sources {
            let fs = s.extension().is_some_and(|e| e == "fs" || e == "fsi");
            if !path_ok(s) || !fs {
                return Err(format!(
                    "{id}: source {} is not an absolute .fs/.fsi",
                    s.display()
                ));
            }
            // fsc reads an argument that starts `/` with no other `/` as a
            // switch, so a source at the root has no spelling it reads.
            // Nor one whose third character is `:`, which fsc reads as a
            // short option (`/r:…`).
            if s.parent() == Some(Path::new("/"))
                || s.to_str().is_some_and(|t| t.chars().nth(2) == Some(':'))
            {
                return Err(format!(
                    "{id}: source {} has the shape of a switch",
                    s.display()
                ));
            }
        }
        if self.sources.iter().collect::<BTreeSet<_>>().len() != self.sources.len() {
            return Err(format!("{id}: a source is given twice"));
        }
        for d in &self.defines {
            let mut chars = d.chars();
            let symbol = chars
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');
            if !symbol {
                return Err(format!("{id}: define {d:?} is not a symbol"));
            }
        }
        let mut cores = 0;
        for (i, r) in self.references.iter().enumerate() {
            if self.references[..i].contains(r) {
                return Err(format!("{id}: reference {r:?} is given twice"));
            }
            if let Reference::Dll(p) = r {
                if !path_ok(p) {
                    return Err(format!(
                        "{id}: reference {} is not absolute UTF-8",
                        p.display()
                    ));
                }
                cores += usize::from(p.file_name().is_some_and(|n| n == "FSharp.Core.dll"));
            }
        }
        if cores != 1 {
            return Err(format!(
                "{id}: expected exactly one reference to FSharp.Core.dll"
            ));
        }
        self.unique_identities(|_| None)
    }

    /// Whether the project's own assembly name and its references' are
    /// distinct (case-insensitively): a DLL is the assembly its file's stem
    /// names, a project reference the one `assembly_of` gives (`None` when
    /// unknown here). Two references of one name leave FCS to pick one, so
    /// the request type has no such shape.
    fn unique_identities(
        &self,
        assembly_of: impl Fn(&PlainName) -> Option<String>,
    ) -> Result<(), String> {
        let mut seen = BTreeSet::from([self.assembly_name.as_str().to_ascii_lowercase()]);
        for r in &self.references {
            let name = match r {
                Reference::Dll(p) => p.file_stem().and_then(|s| s.to_str()).map(str::to_owned),
                Reference::Project(q) => assembly_of(q),
            };
            if let Some(name) = name
                && !seen.insert(name.to_ascii_lowercase())
            {
                return Err(format!(
                    "{}: two references, or a reference and the project, are assembly {name}",
                    self.id
                ));
            }
        }
        Ok(())
    }

    fn to_json(&self) -> Value {
        let path = |p: &Path| p.to_str().expect("validated UTF-8").to_owned();
        serde_json::json!({
            "id": self.id.as_str(),
            "assemblyName": self.assembly_name.as_str(),
            "target": self.target.as_str(),
            "sources": self.sources.iter().map(|s| path(s)).collect::<Vec<_>>(),
            "defines": self.defines,
            "references": self.references.iter().map(|r| match r {
                Reference::Dll(p) => serde_json::json!({ "dll": path(p) }),
                Reference::Project(q) => serde_json::json!({ "project": q.as_str() }),
            }).collect::<Vec<_>>(),
        })
    }

    fn project_refs(&self) -> impl Iterator<Item = &PlainName> {
        self.references.iter().filter_map(|r| match r {
            Reference::Project(q) => Some(q),
            Reference::Dll(_) => None,
        })
    }
}

/// One `check` request: the projects, and the one whose files to report.
/// Ids and assembly names are unique, every project reference names a
/// project of the request, and the references are acyclic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphRequest {
    projects: Vec<GraphProject>,
    check: PlainName,
}

impl GraphRequest {
    pub fn new(projects: Vec<GraphProject>, check: PlainName) -> Result<Self, String> {
        let mut ids = BTreeSet::new();
        let mut names = BTreeSet::new();
        for p in &projects {
            p.validate()?;
            if !ids.insert(&p.id) {
                return Err(format!("two projects have the id {}", p.id));
            }
            if !names.insert(p.assembly_name.as_str().to_ascii_lowercase()) {
                return Err(format!(
                    "two projects have the assembly name {}",
                    p.assembly_name
                ));
            }
        }
        for p in &projects {
            if let Some(q) = p.project_refs().find(|q| !ids.contains(q)) {
                return Err(format!("{} references unknown project {q}", p.id));
            }
            p.unique_identities(|q| {
                projects
                    .iter()
                    .find(|o| &o.id == q)
                    .map(|o| o.assembly_name.as_str().to_owned())
            })?;
        }
        if !ids.contains(&check) {
            return Err(format!("check names no project of the request: {check}"));
        }
        let edges: BTreeMap<&PlainName, Vec<&PlainName>> = projects
            .iter()
            .map(|p| (&p.id, p.project_refs().collect()))
            .collect();
        if let Some(id) = first_cycle(&edges) {
            return Err(format!("project reference cycle through {id}"));
        }
        Ok(GraphRequest { projects, check })
    }

    pub fn projects(&self) -> &[GraphProject] {
        &self.projects
    }

    pub fn check(&self) -> &PlainName {
        &self.check
    }

    /// The request as one line of JSON.
    pub fn to_json_line(&self) -> String {
        let projects: Vec<Value> = self.projects.iter().map(GraphProject::to_json).collect();
        serde_json::json!({ "op": "check", "projects": projects, "check": self.check.as_str() })
            .to_string()
    }
}

/// A project on a cycle of `edges`, if there is one.
fn first_cycle<'a>(edges: &BTreeMap<&'a PlainName, Vec<&'a PlainName>>) -> Option<&'a PlainName> {
    fn visit<'a>(
        id: &'a PlainName,
        edges: &BTreeMap<&'a PlainName, Vec<&'a PlainName>>,
        open: &mut BTreeSet<&'a PlainName>,
        done: &mut BTreeSet<&'a PlainName>,
    ) -> Option<&'a PlainName> {
        if done.contains(id) {
            return None;
        }
        if !open.insert(id) {
            return Some(id);
        }
        for q in edges.get(id).into_iter().flatten() {
            if let Some(c) = visit(q, edges, open, done) {
                return Some(c);
            }
        }
        open.remove(id);
        done.insert(id);
        None
    }
    let (mut open, mut done) = (BTreeSet::new(), BTreeSet::new());
    edges
        .keys()
        .find_map(|id| visit(id, edges, &mut open, &mut done))
}

/// Whether `p` is absolute, UTF-8 and already in its own normal form (no
/// `.` or `..` component, no repeated or trailing separator): the rule
/// `fcs-dump`'s parser applies (`Path.GetFullPath p = p`).
fn is_normal_absolute(p: &Path) -> bool {
    let Some(text) = p.to_str() else {
        return false;
    };
    let normal: PathBuf = p.components().collect();
    p.is_absolute()
        && p.components().all(|c| {
            !matches!(
                c,
                std::path::Component::CurDir | std::path::Component::ParentDir
            )
        })
        && normal.to_str() == Some(text)
}

/// A `compile` request, as one line of JSON. Made only by
/// [`compile_request_line`], so only a well-formed request reaches the oracle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompileRequest(String);

impl CompileRequest {
    pub fn as_line(&self) -> &str {
        &self.0
    }
}

/// The `compile` request for `project`, writing `<out_dir>/<assembly>.dll`.
/// Its references must all be DLLs.
pub fn compile_request_line(
    project: &GraphProject,
    out_dir: &Path,
) -> Result<CompileRequest, String> {
    project.validate()?;
    if project.project_refs().next().is_some() {
        return Err(format!(
            "{}: a compiled project references DLLs only",
            project.id
        ));
    }
    let out = out_dir
        .to_str()
        .filter(|_| is_normal_absolute(out_dir))
        .ok_or_else(|| format!("{} is not a normal absolute UTF-8 path", out_dir.display()))?;
    Ok(CompileRequest(
        serde_json::json!({ "op": "compile", "project": project.to_json(), "outDir": out })
            .to_string(),
    ))
}

/// A referenced project's entry in a [`GraphResponse`].
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct ReferencedProject {
    #[serde(rename = "Id")]
    pub id: String,
    #[serde(rename = "AssemblyName")]
    pub assembly_name: String,
    /// Its whole-project diagnostics from FCS's check from source.
    #[serde(rename = "Diagnostics")]
    pub diagnostics: Vec<Value>,
}

impl ReferencedProject {
    pub fn errors(&self) -> impl Iterator<Item = &Value> {
        errors_of(&self.diagnostics)
    }
}

/// A `check` response: the checked project's file records (`{ Path,
/// Diagnostics, Uses }`, from the whole-project check), its whole-project
/// diagnostics, and every project it reaches from source.
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct GraphResponse {
    #[serde(rename = "Files")]
    pub files: Vec<Value>,
    #[serde(rename = "Diagnostics")]
    pub diagnostics: Vec<Value>,
    #[serde(rename = "Referenced")]
    pub referenced: Vec<ReferencedProject>,
}

impl GraphResponse {
    pub fn errors(&self) -> impl Iterator<Item = &Value> {
        errors_of(&self.diagnostics)
    }
}

/// A `compile` response: the compiler's diagnostics, and the DLL this
/// compile wrote, `None` when it failed (a failed compile may leave an
/// earlier DLL in place, which is not this request's).
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct CompileResponse {
    #[serde(rename = "Diagnostics")]
    pub diagnostics: Vec<Value>,
    #[serde(rename = "Output")]
    pub output: Option<PathBuf>,
}

impl CompileResponse {
    pub fn errors(&self) -> impl Iterator<Item = &Value> {
        errors_of(&self.diagnostics)
    }
}

fn errors_of(diagnostics: &[Value]) -> impl Iterator<Item = &Value> {
    diagnostics.iter().filter(|d| d["Severity"] == "Error")
}

/// Parse one response line; a `BatchError` (the oracle refused the request)
/// is an `Err` holding its message.
pub fn parse_response<T: serde::de::DeserializeOwned>(line: &str) -> Result<T, String> {
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

/// The references every fixture project is checked and compiled against:
/// the installed SDK's own `FSharp.Core.dll` and every assembly of the newest
/// `Microsoft.NETCore.App.Ref` reference pack. One list, used by both sides
/// of every comparison, so the oracle reads exactly the set the caller hands
/// it. Panics, quoting `dotnet --list-sdks`, if no SDK carries both.
pub fn framework_references() -> &'static [PathBuf] {
    static REFS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    REFS.get_or_init(|| {
        let mut cmd = Command::new("dotnet");
        cmd.arg("--list-sdks");
        let out = BoundedCommand::new(cmd)
            .run()
            .expect("run `dotnet --list-sdks`");
        let listing = String::from_utf8_lossy(&out.stdout).into_owned();
        // `<version> [<sdk dir>]`, newest last.
        let (version, sdk_dir) = listing
            .lines()
            .filter_map(|l| {
                let (v, rest) = l.split_once(' ')?;
                Some((
                    v.trim().to_owned(),
                    PathBuf::from(rest.trim().trim_matches(['[', ']'])),
                ))
            })
            .max_by_key(|(v, _)| release_precedence(v))
            .unwrap_or_else(|| panic!("no SDK in `dotnet --list-sdks`:\n{listing}"));
        let core = sdk_dir.join(&version).join("FSharp/FSharp.Core.dll");
        assert!(core.is_file(), "{} is missing", core.display());
        let packs = sdk_dir
            .parent()
            .expect("the SDK directory has a parent")
            .join("packs/Microsoft.NETCore.App.Ref");
        let newest = |dir: &Path, key: &dyn Fn(&str) -> Precedence| {
            std::fs::read_dir(dir)
                .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
                .flatten()
                .map(|e| e.path())
                .filter(|p| p.is_dir())
                .max_by_key(|p| key(&p.file_name().unwrap_or_default().to_string_lossy()))
                .unwrap_or_else(|| panic!("nothing under {}", dir.display()))
        };
        let pack = newest(&packs, &release_precedence);
        let tfm_dir = newest(&pack.join("ref"), &|tfm| {
            (version_key(tfm), true, Vec::new())
        });
        let mut refs: Vec<PathBuf> = std::fs::read_dir(&tfm_dir)
            .unwrap_or_else(|e| panic!("read {}: {e}", tfm_dir.display()))
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|e| e == "dll"))
            .collect();
        refs.sort();
        refs.insert(0, core);
        refs
    })
}

/// What [`release_precedence`] orders versions by.
type Precedence = (Vec<u64>, bool, Vec<(bool, u64, String)>);

/// A version's precedence: its numeric release segments, then whether it
/// is a release, then its prerelease identifiers, so `10.0.100` ranks above
/// `10.0.100-rc.2`, `11.0.0-rc.1` above `11.0.0-preview.7`, and `10.0.8`
/// above `9.0.10`: a total order, so the newest pick never depends on the
/// order a directory lists its entries in.
fn release_precedence(version: &str) -> Precedence {
    match version.split_once('-') {
        // SemVer precedence for the prerelease: identifier by identifier, a
        // numeric one below an alphanumeric one, numerically among numbers.
        Some((release, prerelease)) => (
            version_key(release),
            false,
            prerelease
                .split('.')
                .map(|id| match id.parse::<u64>() {
                    Ok(n) => (false, n, String::new()),
                    Err(_) => (true, 0, id.to_owned()),
                })
                .collect(),
        ),
        None => (version_key(version), true, Vec::new()),
    }
}

/// The numeric value of each dot-separated segment of a version or TFM
/// (`net10.0` → `[10, 0]`), so `10.0.8` sorts after `9.0.10`.
fn version_key(name: &str) -> Vec<u64> {
    name.split('.')
        .map(|seg| {
            let digits: String = seg
                .chars()
                .skip_while(|c| !c.is_ascii_digit())
                .take_while(|c| c.is_ascii_digit())
                .collect();
            digits.parse().unwrap_or(0)
        })
        .collect()
}

/// One source file of a [`FixtureProject`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureFile {
    /// A plain file name, written in the project's directory.
    pub name: String,
    pub text: String,
}

/// One project of a [`ProjectGraphFixture`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureProject {
    pub name: PlainName,
    pub assembly_name: PlainName,
    /// In Compile order.
    pub files: Vec<FixtureFile>,
    /// Direct references; a project is also handed each transitive one, as
    /// the SDK hands a build.
    pub project_refs: Vec<PlainName>,
    pub defines: Vec<String>,
    pub target: Target,
}

impl FixtureProject {
    /// A library named `name`, assembly name included, with no references or
    /// defines.
    pub fn new(name: PlainName, files: Vec<FixtureFile>) -> Self {
        FixtureProject {
            assembly_name: name.clone(),
            name,
            files,
            project_refs: Vec::new(),
            defines: Vec::new(),
            target: Target::Library,
        }
    }
}

/// F# projects' sources written to a fresh directory, one subdirectory per
/// project.
#[derive(Debug)]
pub struct ProjectGraphFixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
    projects: Vec<FixtureProject>,
}

impl ProjectGraphFixture {
    /// Write `projects` to a fresh directory. Names are unique, every
    /// reference names a project of the fixture, and references are acyclic.
    pub fn materialise(projects: Vec<FixtureProject>) -> Result<Self, String> {
        let names: BTreeSet<&PlainName> = projects.iter().map(|p| &p.name).collect();
        if names.len() != projects.len() {
            return Err("two projects share a name".to_owned());
        }
        for p in &projects {
            if let Some(q) = p.project_refs.iter().find(|q| !names.contains(q)) {
                return Err(format!("{} references unknown project {q}", p.name));
            }
            for f in &p.files {
                PlainName::new(&f.name)?;
            }
        }
        let edges: BTreeMap<&PlainName, Vec<&PlainName>> = projects
            .iter()
            .map(|p| (&p.name, p.project_refs.iter().collect()))
            .collect();
        if let Some(id) = first_cycle(&edges) {
            return Err(format!("project reference cycle through {id}"));
        }
        let dir = tempfile::Builder::new()
            .prefix("borzoi-project-graph-")
            .tempdir()
            .map_err(|e| format!("create the fixture directory: {e}"))?;
        // Canonical, so the paths handed to FCS are the ones it reports.
        let root = dir
            .path()
            .canonicalize()
            .map_err(|e| format!("canonicalise the fixture directory: {e}"))?;
        // Each directory and file is created afresh, never opened: on a
        // case-insensitive file system `Lib` and `lib` (or `A.fs` and `a.fs`)
        // are one path, and a second write would replace the first's text.
        for p in &projects {
            let pdir = root.join(p.name.as_str());
            std::fs::create_dir(&pdir).map_err(|e| format!("mkdir {}: {e}", pdir.display()))?;
            for f in &p.files {
                let path = pdir.join(&f.name);
                std::fs::File::create_new(&path)
                    .and_then(|mut file| std::io::Write::write_all(&mut file, f.text.as_bytes()))
                    .map_err(|e| format!("write {}: {e}", path.display()))?;
            }
        }
        Ok(ProjectGraphFixture {
            _dir: dir,
            root,
            projects,
        })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn project(&self, name: &PlainName) -> &FixtureProject {
        self.projects
            .iter()
            .find(|p| &p.name == name)
            .unwrap_or_else(|| panic!("no fixture project {name}"))
    }

    /// The directory `name`'s sources are written to.
    pub fn dir(&self, name: &PlainName) -> PathBuf {
        self.root.join(name.as_str())
    }

    /// `name`'s source paths, in Compile order.
    pub fn paths(&self, name: &PlainName) -> Vec<PathBuf> {
        let dir = self.dir(name);
        self.project(name)
            .files
            .iter()
            .map(|f| dir.join(&f.name))
            .collect()
    }

    /// Every project `name` reaches through its references, in dependency
    /// order (each after what it references), `name` excluded.
    pub fn closure(&self, name: &PlainName) -> Vec<PlainName> {
        fn visit(
            fixture: &ProjectGraphFixture,
            name: &PlainName,
            seen: &mut BTreeSet<PlainName>,
            out: &mut Vec<PlainName>,
        ) {
            if !seen.insert(name.clone()) {
                return;
            }
            for r in &fixture.project(name).project_refs {
                visit(fixture, r, seen, out);
            }
            out.push(name.clone());
        }
        let (mut seen, mut out) = (BTreeSet::new(), Vec::new());
        visit(self, name, &mut seen, &mut out);
        out.pop();
        out
    }

    /// `name` as a request project: its sources and defines, and as
    /// references `framework` then each project of its closure, in
    /// dependency order, as the DLL `from_dll` maps it to or else from
    /// source.
    fn graph_project(
        &self,
        name: &PlainName,
        framework: &[PathBuf],
        from_dll: &BTreeMap<PlainName, PathBuf>,
    ) -> GraphProject {
        let p = self.project(name);
        let references = framework
            .iter()
            .cloned()
            .map(Reference::Dll)
            .chain(
                self.closure(name)
                    .into_iter()
                    .map(|q| match from_dll.get(&q) {
                        Some(dll) => Reference::Dll(dll.clone()),
                        None => Reference::Project(q),
                    }),
            )
            .collect();
        GraphProject {
            id: p.name.clone(),
            assembly_name: p.assembly_name.clone(),
            target: p.target,
            sources: self.paths(name),
            defines: p.defines.clone(),
            references,
        }
    }

    /// The `check` request for `check`: each project of its closure is
    /// referenced as the DLL `from_dll` maps it to, or else from source (and
    /// is then a project of the request, referencing its own closure the
    /// same way). An empty `from_dll` gives the all-source request; one
    /// holding every project of the closure, the all-DLL request.
    pub fn request(
        &self,
        check: &PlainName,
        framework: &[PathBuf],
        from_dll: &BTreeMap<PlainName, PathBuf>,
    ) -> GraphRequest {
        let projects: Vec<GraphProject> = self
            .closure(check)
            .into_iter()
            .filter(|q| !from_dll.contains_key(q))
            .chain(std::iter::once(check.clone()))
            .map(|q| self.graph_project(&q, framework, from_dll))
            .collect();
        GraphRequest::new(projects, check.clone()).expect("a fixture's request is well formed")
    }

    /// The `compile` request for `name`, every project of its closure
    /// referenced as the DLL `compiled` maps it to, writing under
    /// `<root>/out/<name>/`.
    pub fn compile_request(
        &self,
        name: &PlainName,
        framework: &[PathBuf],
        compiled: &BTreeMap<PlainName, PathBuf>,
    ) -> CompileRequest {
        for q in self.closure(name) {
            assert!(compiled.contains_key(&q), "{name} needs {q} compiled first");
        }
        let project = self.graph_project(name, framework, compiled);
        compile_request_line(&project, &self.root.join("out").join(name.as_str()))
            .expect("a fixture's compile request is well formed")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn name(s: &str) -> PlainName {
        PlainName::new(s).expect("plain")
    }

    fn core() -> Vec<PathBuf> {
        vec![PathBuf::from("/sdk/FSharp/FSharp.Core.dll")]
    }

    fn project(id: &str, refs: &[&str]) -> GraphProject {
        GraphProject {
            id: name(id),
            assembly_name: name(id),
            target: Target::Library,
            sources: vec![PathBuf::from(format!("/src/{id}/{id}.fs"))],
            defines: vec!["A_DEFINE".to_owned()],
            references: core()
                .into_iter()
                .map(Reference::Dll)
                .chain(refs.iter().map(|r| Reference::Project(name(r))))
                .collect(),
        }
    }

    #[test]
    fn a_release_ranks_above_its_prereleases() {
        let mut versions = ["10.0.100-rc.2", "10.0.100", "9.0.300", "10.0.100-preview.7"];
        versions.sort_by_key(|v| release_precedence(v));
        assert_eq!(
            versions,
            ["9.0.300", "10.0.100-preview.7", "10.0.100-rc.2", "10.0.100"]
        );
        assert!(release_precedence("11.0.0-rc.1") > release_precedence("11.0.0-preview.7"));
        assert!(release_precedence("11.0.0-rc.10") > release_precedence("11.0.0-rc.2"));
        assert!(release_precedence("10.0.8") > release_precedence("9.0.10"));
    }

    #[test]
    fn plain_names() {
        for ok in ["Ay", "My.Lib-2", "_x"] {
            assert!(PlainName::new(ok).is_ok(), "{ok}");
        }
        for bad in ["", ".", "..", "a/b", "a b", "ä"] {
            assert!(PlainName::new(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn a_request_is_one_line_of_typed_json() {
        let r = GraphRequest::new(
            vec![project("Ay", &[]), project("Bee", &["Ay"])],
            name("Bee"),
        )
        .expect("a graph");
        let line = r.to_json_line();
        assert!(!line.contains('\n'));
        let v: Value = serde_json::from_str(&line).expect("json");
        assert_eq!(v["op"], "check");
        assert_eq!(v["check"], "Bee");
        assert_eq!(
            v["projects"][1]["references"][1],
            serde_json::json!({ "project": "Ay" })
        );
        assert_eq!(v["projects"][1]["defines"], serde_json::json!(["A_DEFINE"]));
    }

    #[test]
    fn malformed_requests_are_refused() {
        let with = |f: &dyn Fn(&mut GraphProject)| {
            let mut p = project("Ay", &[]);
            f(&mut p);
            GraphRequest::new(vec![p], name("Ay"))
        };
        assert!(with(&|_| ()).is_ok());
        assert!(with(&|p| p.defines.push("A=B".to_owned())).is_err());
        assert!(with(&|p| p.sources.push(PathBuf::from("rel.fs"))).is_err());
        assert!(with(&|p| p.sources.push(p.sources[0].clone())).is_err());
        assert!(with(&|p| p.references.clear()).is_err());
        assert!(with(&|p| p.assembly_name = name("FSharp.Core")).is_err());
        assert!(with(&|p| p.references.push(Reference::Project(name("Nobody")))).is_err());
        assert!(GraphRequest::new(vec![project("Ay", &[])], name("Bee")).is_err());
        assert!(
            GraphRequest::new(vec![project("Ay", &[]), project("Ay", &[])], name("Ay")).is_err()
        );
    }

    /// Whether the relation over `n` nodes has a cycle, by removing nodes
    /// nothing alive references (Kahn): independent of [`first_cycle`].
    fn has_cycle_by_kahn(n: usize, edges: &[(usize, usize)]) -> bool {
        let mut alive: BTreeSet<usize> = (0..n).collect();
        while let Some(v) = alive.iter().copied().find(|&v| {
            !edges
                .iter()
                .any(|&(from, to)| from == v && alive.contains(&to))
        }) {
            alive.remove(&v);
        }
        !alive.is_empty()
    }

    proptest! {
        /// A request is refused exactly when the graph has a cycle: as a
        /// cycle, or, for a project referencing itself, as a reference of the
        /// project's own assembly name.
        #[test]
        fn a_cycle_is_refused_exactly_when_there_is_one(
            n in 1usize..6,
            raw in proptest::collection::vec((0usize..6, 0usize..6), 0..10),
        ) {
            let mut edges: Vec<(usize, usize)> =
                raw.into_iter().map(|(a, b)| (a % n, b % n)).collect();
            edges.sort();
            edges.dedup();
            let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
            let projects: Vec<GraphProject> = (0..n)
                .map(|i| {
                    let refs: Vec<&str> = edges
                        .iter()
                        .filter(|&&(from, _)| from == i)
                        .map(|&(_, to)| names[to].as_str())
                        .collect();
                    project(&names[i], &refs)
                })
                .collect();
            let self_loop = edges.iter().any(|&(a, b)| a == b);
            let result = GraphRequest::new(projects, name("p0"));
            if has_cycle_by_kahn(n, &edges) {
                let refused_for_the_cycle = result.as_ref().is_err_and(|e| {
                    e.contains("cycle") || (self_loop && e.contains("reference and the project"))
                });
                prop_assert!(refused_for_the_cycle, "{result:?}");
            } else {
                prop_assert!(result.is_ok(), "an acyclic graph is accepted: {result:?}");
            }
        }
    }

    fn lib_mid_app() -> ProjectGraphFixture {
        let file = |n: &str| FixtureFile {
            name: format!("{n}.fs"),
            text: format!("module {n}\n"),
        };
        ProjectGraphFixture::materialise(vec![
            FixtureProject::new(name("Lib"), vec![file("Lib")]),
            FixtureProject {
                project_refs: vec![name("Lib")],
                ..FixtureProject::new(name("Mid"), vec![file("Mid")])
            },
            FixtureProject {
                project_refs: vec![name("Mid")],
                defines: vec!["APP".to_owned()],
                ..FixtureProject::new(name("App"), vec![file("App")])
            },
        ])
        .expect("a graph")
    }

    /// A project is handed every project of its closure, transitive ones
    /// included, after the framework and in dependency order; from source
    /// unless `from_dll` maps it.
    #[test]
    fn requests_reference_the_closure_in_order() {
        let fixture = lib_mid_app();
        assert_eq!(fixture.closure(&name("App")), [name("Lib"), name("Mid")]);
        let source = fixture.request(&name("App"), &core(), &BTreeMap::new());
        let ids: Vec<&str> = source.projects().iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, ["Lib", "Mid", "App"]);
        let app = &source.projects()[2];
        assert_eq!(
            app.references[1..],
            [
                Reference::Project(name("Lib")),
                Reference::Project(name("Mid"))
            ]
        );
        assert_eq!(app.defines, ["APP"]);
        assert_eq!(app.sources, [fixture.dir(&name("App")).join("App.fs")]);
        assert!(app.sources[0].is_file());

        let compiled: BTreeMap<PlainName, PathBuf> = [
            (name("Lib"), PathBuf::from("/out/Lib.dll")),
            (name("Mid"), PathBuf::from("/out/Mid.dll")),
        ]
        .into();
        let dll = fixture.request(&name("App"), &core(), &compiled);
        assert_eq!(dll.projects().len(), 1);
        assert_eq!(
            dll.projects()[0].references[1..],
            [
                Reference::Dll(PathBuf::from("/out/Lib.dll")),
                Reference::Dll(PathBuf::from("/out/Mid.dll"))
            ]
        );
        let line = fixture.compile_request(&name("Mid"), &core(), &compiled);
        let v: Value = serde_json::from_str(line.as_line()).expect("json");
        assert_eq!(v["op"], "compile");
        assert_eq!(
            v["project"]["references"][1],
            serde_json::json!({ "dll": "/out/Lib.dll" })
        );
    }

    /// A project's references, and the project itself, are distinct by
    /// assembly name: a DLL and a project reference of one name cannot be
    /// built, nor two DLLs of one stem, nor a reference named like the project.
    #[test]
    fn references_are_distinct_by_assembly_identity() {
        let mut bee = project("Bee", &["Ay"]);
        bee.references
            .insert(1, Reference::Dll(PathBuf::from("/disk/ay.dll")));
        assert!(GraphRequest::new(vec![project("Ay", &[]), bee], name("Bee")).is_err());
        let mut two = project("Ay", &[]);
        two.references
            .push(Reference::Dll(PathBuf::from("/a/X.dll")));
        two.references
            .push(Reference::Dll(PathBuf::from("/b/x.dll")));
        assert!(GraphRequest::new(vec![two], name("Ay")).is_err());
        let mut own = project("Ay", &[]);
        own.references
            .push(Reference::Dll(PathBuf::from("/disk/Ay.dll")));
        assert!(GraphRequest::new(vec![own.clone()], name("Ay")).is_err());
        assert!(compile_request_line(&own, Path::new("/out")).is_err());
    }

    /// The path rule is `fcs-dump`'s: absolute and already normal, for
    /// sources, DLLs and a compile's output directory alike.
    #[test]
    fn paths_must_be_in_normal_form() {
        for bad in [
            "/src/sub/../Lib.fs",
            "/src/./Lib.fs",
            "/src//Lib.fs",
            "src/Lib.fs",
        ] {
            let mut p = project("Ay", &[]);
            p.sources = vec![PathBuf::from(bad)];
            assert!(
                GraphRequest::new(vec![p], name("Ay")).is_err(),
                "source {bad}"
            );
            let mut p = project("Ay", &[]);
            p.references.push(Reference::Dll(PathBuf::from(
                bad.replace("Lib.fs", "X.dll"),
            )));
            assert!(GraphRequest::new(vec![p], name("Ay")).is_err(), "dll {bad}");
            let out = bad.replace("/Lib.fs", "");
            assert!(
                compile_request_line(&project("Ay", &[]), Path::new(&out)).is_err(),
                "out dir {out}"
            );
        }
        assert!(compile_request_line(&project("Ay", &[]), Path::new("/out/Ay")).is_ok());
        // A source at the root has the shape of a switch to fsc.
        let mut p = project("Ay", &[]);
        p.sources = vec![PathBuf::from("/Lib.fs")];
        assert!(GraphRequest::new(vec![p], name("Ay")).is_err(), "/Lib.fs");
        let mut p = project("Ay", &[]);
        p.sources = vec![PathBuf::from("/r:/Lib.fs")];
        assert!(
            GraphRequest::new(vec![p], name("Ay")).is_err(),
            "/r:/Lib.fs"
        );
    }

    /// Two projects, or two files, whose names differ only in case are
    /// refused where the file system folds case, and never overwrite one
    /// another.
    #[test]
    fn a_fixture_never_writes_one_path_twice() {
        let file = |n: &str, t: &str| FixtureFile {
            name: n.to_owned(),
            text: t.to_owned(),
        };
        let result = ProjectGraphFixture::materialise(vec![
            FixtureProject::new(name("Lib"), vec![file("Main.fs", "module A\n")]),
            FixtureProject::new(name("lib"), vec![file("Main.fs", "module B\n")]),
        ]);
        match result {
            Ok(f) => {
                let a = std::fs::read_to_string(f.dir(&name("Lib")).join("Main.fs"));
                assert_eq!(
                    a.expect("read"),
                    "module A\n",
                    "a case-sensitive file system"
                );
            }
            Err(e) => assert!(e.contains("mkdir"), "{e}"),
        }
    }

    #[test]
    fn a_fixture_refuses_a_cycle_or_an_unknown_reference() {
        let p = |n: &str, refs: &[&str]| FixtureProject {
            project_refs: refs.iter().map(|r| name(r)).collect(),
            ..FixtureProject::new(name(n), Vec::new())
        };
        assert!(ProjectGraphFixture::materialise(vec![p("A", &["B"]), p("B", &["A"])]).is_err());
        assert!(ProjectGraphFixture::materialise(vec![p("A", &["C"])]).is_err());
    }
}
