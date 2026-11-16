//! Friend assemblies (`InternalsVisibleTo`), held to FCS over a generated grid.
//!
//! When a referenced assembly names the checked one in an
//! `[<assembly: InternalsVisibleTo>]`, FCS widens the access rights it adds that
//! assembly's contents under (`AddNonLocalCcu`, `CheckDeclarations.fs:325`, for
//! the CCU's F# entities; `IsTyconAccessibleViaVisibleTo`,
//! `AccessibilityLogic.fs:124`, for its IL types), so the friend's internal
//! entities enter the name environment as public ones do: they bind, and they
//! shadow. Name resolution reads an assembly through its public view, so for
//! a friend it reads less than FCS does.
//!
//! # The grid
//!
//! A cell is an internal entity of one [`Kind`] in a referenced assembly, in a
//! namespace of its own, crossed with a [`Collision`]: nothing else of its
//! name, a public one in another assembly's namespace opened earlier, a public
//! one in the same namespace in another assembly, or one the checked file
//! declares before its `open`. Every cell is checked under each [`Variant`]
//! of friendship: the referenced assemblies name the checked project
//! (`Friend`), name another (`Stranger`), name it in a spelling the reader does
//! not certify (`Unparsed`), name it through an attribute whose blob the reader
//! does not decode (`Undecodable`), or name it while the checked project's own
//! name is untrusted (`Untrusted`).
//!
//! The referenced assemblies of a variant are an F# one and a C# one (the IL
//! type cells), both carrying the variant's attribute, beside a rival
//! assembly holding every public collision partner. The oracle checks each
//! variant's project as the assembly [`CONSUMER`] (`-o:`), without which FCS
//! names it after its last file and no cell would be a friend.
//!
//! # The property
//!
//! For every probe, our resolution is a decline, or names the binder FCS
//! binds: the same referenced assembly, the checked project, or nothing. The
//! binder's owner is the currency, and it discriminates every cell's
//! candidates: each candidate of a cell sits in a different assembly.
//! [`liveness`] pins the cells where FCS binds the internal entity, so a
//! fixture that stops granting friendship fails rather than passing
//! vacuously, and the whole table is pinned in an exact manifest. The few
//! probes that commit wrongly for a cause other than friendship are listed,
//! with their issue, in [`KNOWN_WRONG`].
//!
//! Under every variant but `Stranger` the env grades the referenced
//! assemblies' non-public surface as unread (`AssemblyEnv::public_view_incomplete`),
//! so every probe there declines; the grid's job is to show that each such
//! cell would otherwise commit wrongly, and that a `No` verdict leaves the
//! public view's commits standing.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::common::{
    build_generated_cs_fixture, build_generated_fs_fixture, ensure_fsharp_core_dll,
    ensure_system_runtime_dll, invoke_fcs_dump_project_named, parse_fcs_uses_project, temp_fs_tree,
};
use borzoi_assembly::{Ecma335Assembly, EcmaView, FriendEntry};
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange};
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_sema::{
    AssemblyEnv, ConsumerName, ProjectFile, Resolution, SourceFile, SyntaxRecovery, infer_project,
    qualified_names, resolve_project_files,
};

/// The checked project's assembly name, which the friend variants' attribute
/// names.
const CONSUMER: &str = "FriendGridConsumer";

/// The assembly holding every public collision partner.
const RIVAL: &str = "FriendGridRival";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// `type internal Widget`.
    Type,
    /// `module internal Tools`.
    Module,
    /// `type internal Alias = int`.
    Abbreviation,
    /// `type internal Alias = int` under a value of its name the checked
    /// file declares before its `open`: in expression position the
    /// abbreviation's constructor shadows the value. The abbreviation exists
    /// only in the signature pickle, so its namespace has no `TypeDef` row.
    AbbreviationConstructor,
    /// `exception internal Boom`.
    Exception,
    /// `type internal Inner` in a public `module Host`.
    Nested,
    /// `type Shape = internal | Circle | Square`: the cases of a public
    /// union with an internal representation.
    UnionCase,
    /// `member internal s.Shout` extending `System.String`, in a public
    /// module.
    Extension,
    /// `let internal helper` in a public module.
    Value,
    /// `module internal List`, shadowing FSharp.Core's under an `open`.
    CoreModule,
    /// `internal class Widget` of a C# assembly.
    IlType,
    /// A public C# type's public instance method, `g.Spin()` on a `g: Gadget`, which only
    /// inference binds: the control that shows inference's readings are
    /// withdrawn for a possible friend and stand for a stranger.
    PublicMember,
    /// `"abc".Length`, with no `open`: a BCL member inference reads off a
    /// literal's type, through no resolver reading, so only inference's own
    /// seal withdraws it for a possible friend.
    LiteralMember,
}

const KINDS: &[Kind] = &[
    Kind::Type,
    Kind::Module,
    Kind::Abbreviation,
    Kind::AbbreviationConstructor,
    Kind::Exception,
    Kind::Nested,
    Kind::UnionCase,
    Kind::Extension,
    Kind::Value,
    Kind::CoreModule,
    Kind::IlType,
    Kind::PublicMember,
    Kind::LiteralMember,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Collision {
    /// Nothing else of the name (FSharp.Core's `List`, for
    /// [`Kind::CoreModule`]).
    None,
    /// A public one in the rival's namespace `FGR.C<n>`, opened first.
    OtherNamespace,
    /// A public one in the rival, in the internal entity's own namespace.
    SameNamespace,
    /// One the checked file declares before its `open`.
    Project,
    /// The checked file declares a module named like the entity's
    /// namespace, `C<n>`, and then opens the namespace's parent, `FG`, which
    /// brings the child namespace `C<n>` into scope by its short name.
    ParentNamespace,
}

const COLLISIONS: &[Collision] = &[
    Collision::None,
    Collision::OtherNamespace,
    Collision::SameNamespace,
    Collision::Project,
    Collision::ParentNamespace,
];

/// Who the referenced assemblies' `InternalsVisibleTo` names, and how.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Variant {
    /// `InternalsVisibleTo("FriendGridConsumer")`.
    Friend,
    /// `InternalsVisibleTo("FriendGridOther")`.
    Stranger,
    /// The consumer in a spelling `AssemblyName` reads the name off but the
    /// reader does not certify: quoted (F#), or after white space (C#).
    Unparsed,
    /// The consumer, through an `InternalsVisibleToAttribute` the assembly
    /// declares itself with an `obj` parameter: FCS classifies the attribute
    /// by its type's name and decodes the boxed string, the reader decodes no
    /// `obj` argument.
    Undecodable,
    /// [`Variant::Friend`]'s assemblies, with the checked project's name
    /// untrusted.
    Untrusted,
}

const VARIANTS: &[Variant] = &[
    Variant::Friend,
    Variant::Stranger,
    Variant::Unparsed,
    Variant::Undecodable,
    Variant::Untrusted,
];

impl Variant {
    /// The variant whose fixture assemblies this one reads.
    fn fixture(self) -> Variant {
        match self {
            Variant::Untrusted => Variant::Friend,
            other => other,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Variant::Friend => "Friend",
            Variant::Stranger => "Stranger",
            Variant::Unparsed => "Unparsed",
            Variant::Undecodable => "Undecodable",
            Variant::Untrusted => "Untrusted",
        }
    }

    /// The F# assembly-attribute lines granting this variant's friendship.
    fn fs_attribute(self) -> String {
        let attr = |arg: &str| {
            format!(
                "module AttrHost =\n    \
                 [<assembly: System.Runtime.CompilerServices.InternalsVisibleTo({arg})>]\n    \
                 do ()\n"
            )
        };
        match self.fixture() {
            Variant::Friend => format!("namespace FG.Attrs\n{}", attr(&format!("\"{CONSUMER}\""))),
            Variant::Stranger => format!("namespace FG.Attrs\n{}", attr("\"FriendGridOther\"")),
            Variant::Unparsed => format!(
                "namespace FG.Attrs\n{}",
                attr(&format!("\"\\\"{CONSUMER}\\\"\""))
            ),
            Variant::Undecodable => format!(
                "namespace System.Runtime.CompilerServices\n\
                 [<System.AttributeUsage(System.AttributeTargets.Assembly, AllowMultiple = true)>]\n\
                 type InternalsVisibleToAttribute(name: obj) =\n    \
                 inherit System.Attribute()\n    \
                 member _.Name = name\n\
                 namespace FG.Attrs\n{}",
                attr(&format!("\"{CONSUMER}\""))
            ),
            Variant::Untrusted => unreachable!("fixture() maps it to Friend"),
        }
    }

    fn cs_attribute(self) -> String {
        match self.fixture() {
            Variant::Friend => format!(
                "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"{CONSUMER}\")]\n"
            ),
            Variant::Stranger => {
                "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"FriendGridOther\")]\n"
                    .to_string()
            }
            Variant::Unparsed => format!(
                "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\" {CONSUMER}\")]\n"
            ),
            Variant::Undecodable => format!(
                "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo((object)\"{CONSUMER}\")]\n\
                 namespace System.Runtime.CompilerServices {{\n\
                 [System.AttributeUsage(System.AttributeTargets.Assembly, AllowMultiple = true)]\n\
                 internal sealed class InternalsVisibleToAttribute : System.Attribute {{\n\
                 public InternalsVisibleToAttribute(object name) {{ }}\n}}\n}}\n"
            ),
            Variant::Untrusted => unreachable!("fixture() maps it to Friend"),
        }
    }

    fn fs_dir(self) -> (String, String) {
        let v = self.fixture().label();
        (
            format!("friend_grid_{}_env", v.to_lowercase()),
            format!("FriendGrid{v}"),
        )
    }

    fn cs_dir(self) -> (String, String) {
        let v = self.fixture().label();
        (
            format!("friend_grid_cs_{}_env", v.to_lowercase()),
            format!("FriendGridCs{v}"),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Cell {
    kind: Kind,
    collision: Collision,
}

/// Every cell of the grid, in a fixed order; a cell's namespace is
/// `FG.C<index>`.
fn cells() -> Vec<Cell> {
    KINDS
        .iter()
        .flat_map(|&kind| {
            COLLISIONS
                .iter()
                .filter(move |&&c| match kind {
                    Kind::CoreModule | Kind::PublicMember | Kind::LiteralMember => {
                        c == Collision::None
                    }
                    Kind::AbbreviationConstructor => c == Collision::Project,
                    // Only a constructor shows the namespace at the head.
                    _ if c == Collision::ParentNamespace => {
                        matches!(kind, Kind::Type | Kind::IlType)
                    }
                    _ => true,
                })
                .map(move |&collision| Cell { kind, collision })
        })
        .collect()
}

impl Kind {
    /// The cell's entity, with `access` (`"internal "` or `""`) where the
    /// kind puts it; `tag` distinguishes the declaring assembly's members.
    fn fs_decl(self, access: &str, tag: u32) -> String {
        match self {
            Kind::Type | Kind::IlType => {
                format!("type {access}Widget() =\n    static member Make() = {tag}")
            }
            Kind::Module => format!("module {access}Tools =\n    let run () = {tag}"),
            Kind::Abbreviation | Kind::AbbreviationConstructor => {
                format!("type {access}Alias = int")
            }
            Kind::Exception => format!("exception {access}Boom of string"),
            Kind::Nested => format!(
                "module Host =\n    type {access}Inner() =\n        static member Make() = {tag}"
            ),
            Kind::UnionCase if access.is_empty() => {
                "type Shape =\n    | Circle\n    | Square".to_string()
            }
            Kind::UnionCase => format!("type Shape =\n    {access}\n    | Circle\n    | Square"),
            Kind::Extension => format!(
                "module Exts =\n    type System.String with\n        member {access}s.Shout() = s.Length + {tag}"
            ),
            Kind::Value => format!("module Vals =\n    let {access}helper = {tag}"),
            Kind::CoreModule => {
                format!("module {access}List =\n    let map (f: int -> int) (x: int) = f x + {tag}")
            }
            // Declared in C#, or nowhere.
            Kind::PublicMember | Kind::LiteralMember => unreachable!("no F# declaration"),
        }
    }

    /// The same-named declaration the checked file makes before its `open`
    /// ([`Collision::Project`]): what the `open` would bring into its scope.
    fn project_decl(self) -> String {
        match self {
            Kind::Extension => {
                "type System.String with\n    member s.Shout() = s.Length + 3".to_string()
            }
            Kind::Value => "let helper = 3".to_string(),
            Kind::AbbreviationConstructor => "let Alias (n: int) = n".to_string(),
            other => other.fs_decl("", 3),
        }
    }

    /// The module path under the cell's namespace that the checked file
    /// opens, beside the namespace itself.
    fn opened_module(self) -> Option<&'static str> {
        match self {
            Kind::Extension => Some("Exts"),
            Kind::Value => Some("Vals"),
            _ => None,
        }
    }

    /// The checked file's use of the entity, and the spans probed in it.
    fn probe(self) -> (&'static str, &'static [&'static str]) {
        match self {
            Kind::Type | Kind::IlType => ("let p = Widget.Make()", &["Widget", "Make"]),
            Kind::Module => ("let p = Tools.run ()", &["Tools", "run"]),
            Kind::Abbreviation => ("let p (x: Alias) = x", &["Alias"]),
            Kind::AbbreviationConstructor => ("let p = Alias()", &["Alias"]),
            Kind::Exception => ("let p = Boom \"x\"", &["Boom"]),
            Kind::Nested => ("let p = Host.Inner.Make()", &["Inner", "Make"]),
            Kind::UnionCase => ("let p = Circle", &["Circle"]),
            Kind::Extension => ("let p = \"a\".Shout()", &["Shout"]),
            Kind::Value => ("let p = helper", &["helper"]),
            Kind::CoreModule => ("let p = List.map id 1", &["List", "map"]),
            Kind::PublicMember => ("let p (g: Gadget) = g.Spin()", &["Gadget", "Spin"]),
            Kind::LiteralMember => ("let p = \"abc\".Length", &["Length"]),
        }
    }
}

/// The F# source of a variant's referenced assembly: its attribute, then
/// every F# cell's internal entity.
fn friend_fs_source(variant: Variant) -> Vec<String> {
    let mut blocks = vec![variant.fs_attribute()];
    for (n, cell) in cells().iter().enumerate() {
        if matches!(
            cell.kind,
            Kind::IlType | Kind::PublicMember | Kind::LiteralMember
        ) {
            continue;
        }
        blocks.push(format!(
            "namespace FG.C{n}\n{}\n",
            cell.kind.fs_decl("internal ", 1)
        ));
    }
    vec![blocks.join("\n")]
}

fn friend_cs_source(variant: Variant) -> String {
    let mut out = variant.cs_attribute();
    for (n, cell) in cells().iter().enumerate() {
        match cell.kind {
            Kind::IlType => out.push_str(&format!(
                "namespace FG.C{n} {{ internal class Widget {{ public static int Make() => 1; }} }}\n"
            )),
            // C#, whose methods take one argument group: an F# member's
            // groups are not read, and inference declines such a call.
            Kind::PublicMember => out.push_str(&format!(
                "namespace FG.C{n} {{ public class Gadget {{ public int Spin() => 1; }} }}\n"
            )),
            _ => {}
        }
    }
    out
}

/// The rival's source: each cell's public collision partner.
fn rival_source() -> Vec<String> {
    let mut blocks = Vec::new();
    for (n, cell) in cells().iter().enumerate() {
        let ns = match cell.collision {
            Collision::OtherNamespace => format!("FGR.C{n}"),
            Collision::SameNamespace => format!("FG.C{n}"),
            Collision::None | Collision::Project | Collision::ParentNamespace => continue,
        };
        blocks.push(format!("namespace {ns}\n{}\n", cell.kind.fs_decl("", 2)));
    }
    vec![blocks.join("\n")]
}

/// The checked file of cell `n`.
fn use_source(n: usize, cell: Cell) -> String {
    let opens = |ns: &str| {
        let mut lines = vec![format!("open {ns}")];
        if let Some(m) = cell.kind.opened_module() {
            lines.push(format!("open {ns}.{m}"));
        }
        lines.join("\n")
    };
    let mut lines = vec![format!("module P{n}")];
    match cell.collision {
        Collision::None | Collision::SameNamespace => {}
        Collision::OtherNamespace => lines.push(opens(&format!("FGR.C{n}"))),
        Collision::Project => lines.push(cell.kind.project_decl()),
        Collision::ParentNamespace => {
            lines.push(format!("module C{n} =\n    let Widget () = 3"));
            lines.push("open FG".to_string());
        }
    }
    if cell.kind != Kind::LiteralMember && cell.collision != Collision::ParentNamespace {
        lines.push(opens(&format!("FG.C{n}")));
    }
    lines.push(probe_of(n, cell).0);
    lines.join("\n") + "\n"
}

/// The checked file's use of cell `n`'s entity, and the words probed in it.
fn probe_of(n: usize, cell: Cell) -> (String, &'static [&'static str]) {
    match cell.collision {
        Collision::ParentNamespace => (format!("let p = C{n}.Widget()"), &["Widget"]),
        _ => {
            let (line, words) = cell.kind.probe();
            (line.to_string(), words)
        }
    }
}

/// The fixture assemblies, built once per binary.
struct Fixtures {
    rival: PathBuf,
    /// `(F#, C#)` per [`Variant::fixture`], in [`VARIANTS`] order (the
    /// untrusted variant's entry is unused).
    friends: Vec<(Variant, PathBuf, PathBuf)>,
}

fn fixtures() -> &'static Fixtures {
    static BUILT: OnceLock<Fixtures> = OnceLock::new();
    BUILT.get_or_init(|| {
        let rival = build_generated_fs_fixture("friend_grid_rival_env", RIVAL, rival_source());
        let friends = VARIANTS
            .iter()
            .filter(|v| v.fixture() == **v)
            .map(|&v| {
                let (fs_dir, fs_dll) = v.fs_dir();
                let (cs_dir, cs_dll) = v.cs_dir();
                (
                    v,
                    build_generated_fs_fixture(&fs_dir, &fs_dll, friend_fs_source(v)),
                    build_generated_cs_fixture(&cs_dir, &cs_dll, &friend_cs_source(v)),
                )
            })
            .collect();
        Fixtures { rival, friends }
    })
}

/// Who bound a probe.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Owner {
    Assembly(String),
    Project,
    Nothing,
}

impl std::fmt::Display for Owner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Owner::Assembly(a) => write!(f, "{a}"),
            Owner::Project => write!(f, "project"),
            Owner::Nothing => write!(f, "nothing"),
        }
    }
}

/// Our verdict on one probe.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Ours {
    Commit(Owner),
    Decline,
}

/// One graded probe.
struct Graded {
    key: String,
    fcs: Owner,
    /// Whether FCS reported an error in the probe's file (a non-friend
    /// naming an internal entity, say).
    fcs_errored: bool,
    ours: Ours,
}

impl Graded {
    fn wrong(&self) -> bool {
        matches!(&self.ours, Ours::Commit(o) if *o != self.fcs)
    }

    fn entry(&self) -> String {
        let ours = match &self.ours {
            Ours::Commit(o) if *o == self.fcs => "agree".to_string(),
            Ours::Commit(o) => format!("WRONG:{o}"),
            Ours::Decline => "decline".to_string(),
        };
        let checked = if self.fcs_errored { "error" } else { "clean" };
        format!("{}\tfcs={}\t{checked}\t{ours}", self.key, self.fcs)
    }
}

fn our_owner(env: &AssemblyEnv, res: Resolution) -> Ours {
    let assembly = |h| Ours::Commit(Owner::Assembly(env.entity(h).assembly.name.clone()));
    match res {
        Resolution::Entity(h) => assembly(h),
        Resolution::Member { parent, .. } => assembly(parent),
        Resolution::UnionCase { union, .. } => assembly(union),
        Resolution::Local(_) | Resolution::Item(_) | Resolution::EarlierFileType { .. } => {
            Ours::Commit(Owner::Project)
        }
        Resolution::Unresolved => Ours::Commit(Owner::Nothing),
        Resolution::Deferred(_) => Ours::Decline,
    }
}

/// The env a variant's project resolves against.
fn variant_env(variant: Variant, refs: &[&Path]) -> AssemblyEnv {
    let consumer = match variant {
        Variant::Untrusted => ConsumerName::Unknown,
        _ => ConsumerName::Known(CONSUMER.to_string()),
    };
    // The core references beside the fixtures, so a member reached through a
    // type's base chain (`System.Object`) is one inference can read.
    let system_runtime = ensure_system_runtime_dll();
    let netstandard = system_runtime
        .parent()
        .expect("System.Runtime.dll sits in a ref dir")
        .join("netstandard.dll");
    let bytes: Vec<Vec<u8>> = [ensure_fsharp_core_dll(), system_runtime, netstandard]
        .into_iter()
        .chain(refs.iter().map(|p| p.to_path_buf()))
        .map(|p| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}")))
        .collect();
    let views: Vec<Ecma335Assembly> = bytes
        .iter()
        .map(|b| Ecma335Assembly::parse(b).expect("parse fixture dll"))
        .collect();
    AssemblyEnv::from_views_as(&views, &consumer).expect("build AssemblyEnv")
}

/// Grade every probe of every cell under `variant`.
fn grade_variant(variant: Variant) -> Vec<Graded> {
    let fx = fixtures();
    let (_, fs, cs) = fx
        .friends
        .iter()
        .find(|(v, _, _)| *v == variant.fixture())
        .expect("variant fixture");
    let refs: Vec<&Path> = vec![fx.rival.as_path(), fs.as_path(), cs.as_path()];
    let cells = cells();
    let sources: Vec<(String, String)> = cells
        .iter()
        .enumerate()
        .map(|(n, &c)| (format!("P{n}.fs"), use_source(n, c)))
        .collect();
    let named: Vec<(&str, &str)> = sources
        .iter()
        .map(|(f, s)| (f.as_str(), s.as_str()))
        .collect();
    let (root, written) = temp_fs_tree(&format!("friend_grid_{}", variant.label()), &named);
    let paths: Vec<&Path> = written.iter().map(|(p, _)| p.as_path()).collect();
    let json = invoke_fcs_dump_project_named(&paths, &refs, Some(CONSUMER));
    let fcs_files = parse_fcs_uses_project(&json, &written);
    let _ = std::fs::remove_dir_all(&root);

    let env = variant_env(variant, &refs);
    let parsed: Vec<(ImplFile, SyntaxRecovery)> = written
        .iter()
        .map(|(_, src)| {
            let p = parse(src);
            assert!(
                p.errors.is_empty(),
                "parse errors in {src:?}: {:?}",
                p.errors
            );
            let recovery = SyntaxRecovery::of(&p);
            (ImplFile::cast(p.root).expect("impl file"), recovery)
        })
        .collect();
    let files: Vec<SourceFile> = parsed
        .iter()
        .map(|(f, _)| SourceFile::Impl(f.clone()))
        .collect();
    let file_paths: Vec<PathBuf> = written.iter().map(|(p, _)| p.clone()).collect();
    let project: Vec<ProjectFile> = files
        .iter()
        .cloned()
        .zip(parsed.iter().map(|(_, r)| r.clone()))
        .zip(qualified_names(&files, &file_paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect();
    let proj = resolve_project_files(&project, &env);
    // Inference publishes member bindings the resolver leaves unrecorded (an
    // instance member reached through a value's type), so both are graded.
    let inferred = infer_project(&project, &proj, &env);

    let mut out = Vec::new();
    for (n, (cell, (path, src))) in cells.iter().zip(&written).enumerate() {
        let fu = fcs_files
            .iter()
            .find(|f| f.path.file_name() == path.file_name())
            .unwrap_or_else(|| panic!("FCS reported nothing for {path:?}"));
        let (probe_line, words) = probe_of(n, *cell);
        let probe_line = probe_line.as_str();
        let line_at = src.rfind(probe_line).expect("probe line");
        for &word in words {
            let start = line_at
                + probe_line
                    .find(word)
                    .unwrap_or_else(|| panic!("{word} in {probe_line}"));
            let end = start + word.len();
            // FCS spans a member of a dotted path from the path's head
            // (`Widget.Make`), so its record of a probe is the one of the
            // probe's name ending where the probe does. A use FCS records
            // with no assembly is not one this
            // currency can grade, so it must not read as "binds nothing".
            let record = fu
                .uses
                .iter()
                .find(|u| u.end == end && u.start <= start && u.name == word)
                // A constructor through an abbreviation is named after the
                // type it constructs.
                .or_else(|| fu.uses.iter().find(|u| u.start == start && u.end == end));
            let fcs = record.map_or(Owner::Nothing, |u| match u.assembly.as_deref() {
                Some(CONSUMER) => Owner::Project,
                Some(a) => Owner::Assembly(a.to_string()),
                None => panic!("{path:?}: FCS's record of {word} names no assembly"),
            });
            // Every reading either phase publishes at the probe: a wrong one
            // is the verdict if there is one, else any commit.
            // Each phase's readings are the ones over a range that ends at the
            // probe within its line (`Make`, or the whole `Widget.Make`),
            // whatever range FCS reported, or whether it reported one.
            let ends_at_probe = |range: &TextRange| {
                usize::from(range.end()) == end && usize::from(range.start()) >= line_at
            };
            let mut readings: Vec<Ours> = proj
                .file(n)
                .resolutions()
                .iter()
                .filter(|(range, _)| ends_at_probe(range))
                .map(|(_, r)| our_owner(&env, *r))
                .collect();
            if let Some(f) = inferred.file(n) {
                readings.extend(
                    f.member_resolutions()
                        .iter()
                        .filter(|(range, _)| ends_at_probe(range))
                        .map(|(_, r)| our_owner(&env, *r)),
                );
            }
            let ours = readings
                .iter()
                .find(|o| matches!(o, Ours::Commit(owner) if *owner != fcs))
                .or_else(|| readings.iter().find(|o| matches!(o, Ours::Commit(_))))
                .cloned()
                .unwrap_or(Ours::Decline);
            out.push(Graded {
                key: format!(
                    "{}:{:?}:{:?}:{word}",
                    variant.label(),
                    cell.kind,
                    cell.collision
                ),
                fcs,
                fcs_errored: !fu.errors.is_empty(),
                ours,
            });
        }
    }
    out
}

/// Every probe, graded.
fn graded() -> &'static Vec<Graded> {
    static GRADED: OnceLock<Vec<Graded>> = OnceLock::new();
    GRADED.get_or_init(|| VARIANTS.iter().flat_map(|&v| grade_variant(v)).collect())
}

/// The probes known to commit to a binder FCS does not bind, each with the
/// issue tracking it. Not friendship: a union with an internal
/// representation hides its cases from the projection, while FCS binds them
/// for a non-friend too (#998).
const KNOWN_WRONG: &[(&str, u32)] = &[
    ("Stranger:UnionCase:OtherNamespace:Circle", 998),
    ("Stranger:UnionCase:SameNamespace:Circle", 998),
    ("Stranger:UnionCase:Project:Circle", 998),
];

#[test]
fn every_commit_names_the_binder_fcs_binds() {
    let graded = graded();
    let known = |g: &Graded| KNOWN_WRONG.iter().any(|(key, _)| *key == g.key);
    let wrong: Vec<String> = graded
        .iter()
        .filter(|g| g.wrong() && !known(g))
        .map(Graded::entry)
        .collect();
    assert!(
        wrong.is_empty(),
        "{} of {} probes commit to a binder FCS does not bind:\n{}",
        wrong.len(),
        graded.len(),
        wrong.join("\n")
    );
    // A known divergence that no longer diverges must leave the list, so the
    // list cannot outlive its cause.
    for (key, issue) in KNOWN_WRONG {
        let probe = graded
            .iter()
            .find(|g| g.key == *key)
            .unwrap_or_else(|| panic!("no probe {key}"));
        assert!(
            probe.wrong(),
            "{key} (#{issue}) no longer commits wrongly: {}",
            probe.entry()
        );
    }
}

#[test]
fn the_grid_is_pinned() {
    let manifest =
        Manifest::from_entries(graded().iter().map(Graded::entry)).expect("manifest entries");
    check_manifest(
        "friend_assembly_grid",
        &manifest,
        &regenerate("friend_assembly_grid::the_grid_is_pinned"),
    );
}

/// The friendship is live: in every friend variant, FCS binds the internal
/// entity at the probe of each collision-free F# and IL cell, so the oracle
/// is checking the project as the assembly the attributes name.
#[test]
fn liveness() {
    let graded = graded();
    for variant in [
        Variant::Friend,
        Variant::Unparsed,
        Variant::Undecodable,
        Variant::Untrusted,
    ] {
        for kind in [Kind::Type, Kind::Module, Kind::Exception, Kind::IlType] {
            let key_prefix = format!("{}:{kind:?}:None:", variant.label());
            let probe = graded
                .iter()
                .find(|g| g.key.starts_with(&key_prefix))
                .unwrap_or_else(|| panic!("no probe {key_prefix}"));
            assert!(
                matches!(&probe.fcs, Owner::Assembly(a) if a.starts_with("FriendGrid") && a != RIVAL),
                "{}: FCS bound {} where the friend's internal entity should bind",
                probe.key,
                probe.fcs
            );
        }
    }
    // The public-member controls: inference binds each for a stranger, and
    // withdraws it wherever an assembly may see the project as a friend.
    for probe in ["PublicMember:None:Spin", "LiteralMember:None:Length"] {
        let control = |variant: Variant| {
            let key = format!("{}:{probe}", variant.label());
            graded
                .iter()
                .find(|g| g.key == key)
                .unwrap_or_else(|| panic!("no probe {key}"))
        };
        let stranger = control(Variant::Stranger);
        assert!(
            matches!(&stranger.ours, Ours::Commit(o) if *o == stranger.fcs),
            "the stranger's public member must commit: {}",
            stranger.entry()
        );
        for variant in [
            Variant::Friend,
            Variant::Unparsed,
            Variant::Undecodable,
            Variant::Untrusted,
        ] {
            let probe = control(variant);
            assert_eq!(probe.ours, Ours::Decline, "{}", probe.entry());
        }
    }
}

/// What the reader makes of each variant's attribute, in both of its
/// assemblies: the variants are the friendship verdicts they claim to be,
/// which the grid's expectations rest on.
#[test]
fn the_fixtures_declare_what_their_variants_say() {
    let fx = fixtures();
    for (variant, fs, cs) in &fx.friends {
        for dll in [fs, cs] {
            let bytes = std::fs::read(dll).unwrap_or_else(|e| panic!("read {dll:?}: {e}"));
            let view = Ecma335Assembly::parse(&bytes).expect("parse fixture dll");
            let entries = view.friend_declarations().entries;
            let ok = match variant {
                Variant::Friend => entries == [FriendEntry::Named(CONSUMER.to_string())],
                Variant::Stranger => entries == [FriendEntry::Named("FriendGridOther".to_string())],
                Variant::Unparsed | Variant::Undecodable => {
                    matches!(entries.as_slice(), [FriendEntry::Unread(_)])
                }
                Variant::Untrusted => unreachable!("not a fixture of its own"),
            };
            assert!(ok, "{variant:?} {dll:?}: {entries:?}");
        }
    }
    // FSharp.Core and the rival name no friend at all.
    for dll in [ensure_fsharp_core_dll(), fx.rival.clone()] {
        let bytes = std::fs::read(&dll).unwrap_or_else(|e| panic!("read {dll:?}: {e}"));
        let view = Ecma335Assembly::parse(&bytes).expect("parse dll");
        assert_eq!(view.friend_declarations().entries, [], "{dll:?}");
    }
}
