//! The extension-scope gate's **assembly side**, held to FCS over a generated
//! grid of the shapes an extension member of a referenced assembly can take
//! and the ways a call can reach it.
//!
//! The gate answers "absent" for a call's name only when no in-scope
//! extension of that name could join FCS's method group. On the assembly side
//! that answer comes from what the reader projects, through the namespace
//! query (`AssemblyEnv::extension_named_in_scope`) for an opened or enclosing
//! namespace; an `open` outside the certified domain declines every call. The
//! query is only as complete as the projection, and the projection is not
//! what FCS reads: a property's
//! accessor under `[<Extension>]` projects as a property, a `[<CompiledName>]`
//! moves the metadata name off the logical one, a dropped type is not there
//! at all. This grid generates those shapes instead of waiting for a review to
//! find them one at a time.
//!
//! # The grid
//!
//! One fixture assembly (`tests/fixtures/ext_assembly_grid_env`, its source
//! emitted from [`Cell`]s by [`fixture_source`]) holds one namespace per cell:
//! a `Receiver` with an intrinsic method of the extension's call name (taking
//! `obj`, returning `bool`), its base class and interface, and one extension
//! member. A cell is:
//!
//! - [`Style`]: C#-style, in a type that carries `[<Extension>]` or one that
//!   does not (FCS reads no extension there), or an F# optional extension
//!   (`type T with` in a module);
//! - [`Kind`]: a method, a property getter or setter, an indexer, or an
//!   event's `add` accessor;
//! - [`AttrOn`]: for a C#-style accessor, `[<Extension>]` on the accessor or
//!   on the property;
//! - [`Renamed`]: whether the member carries `[<CompiledName>]`, a witness
//!   twin's, or one a kept extension shares;
//! - [`Target`]: what the extension extends: the receiver, its base class,
//!   its interface, or any type (a generic `this`);
//! - [`Container`]: a plain, generic or F# record C#-style container, and
//!   [`Synth`]: whether the member carries `[<CompilerGenerated>]`;
//! - [`Home`]: the namespace itself, a module, a nested module, an
//!   `[<AutoOpen>]` module or a `[<RequireQualifiedAccess>]` one;
//! - [`Reach`]: how the calling file reaches it: every form of `open` F#
//!   has (a namespace, a module or a type; absolute, `global.` or relative;
//!   through a module or type abbreviation), the enclosing namespace, and an
//!   `open` of a namespace or module an earlier project file also declares;
//! - [`Drop`]: whether the reader is made to drop the extension's top-level
//!   type, as it drops one it cannot decode ([`DroppingView`]).
//!
//! # The properties
//!
//! 1. **Soundness at the call.** Every commit agrees with FCS, and wherever
//!    FCS binds the call to the extension (its type is not the intrinsic's
//!    `System.Boolean`), the gate declines the call's name.
//! 2. **Completeness of the projection** (call-free). Every member FCS reads
//!    as an extension in the fixture (`fcs-dump`'s `extension-members`) is in
//!    its namespace's answer, under the name a call spells.
//! 3. **The certified domain.** The gate reads a cell's `open` as enumerated
//!    exactly when its form is certified ([`certified`]).
//!
//! [`liveness`] pins the cells FCS must bind, so a fixture that stops
//! producing extensions fails rather than passing vacuously.

use std::path::Path;

use crate::common::ext_scope::{Probe, check_files};
use crate::common::{
    ensure_ext_assembly_grid_built, ensure_ext_assembly_grid_internal_built,
    ensure_fsharp_core_dll, ensure_system_runtime_dll, invoke_fcs_dump_extension_members,
    temp_fs_tree,
};
use borzoi_assembly::{
    AssemblyIdentity, AssemblyProjectionSkips, Ecma335Assembly, EcmaView, Entity, FSharpResource,
    ImportError, SkippedProjectionItem, TypeForwarder,
};
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile};
use borzoi_oracle_harness::par_map::par_map;
use borzoi_sema::{
    AssemblyEnv, ProjectFile, SourceFile, SyntaxRecovery, qualified_names, resolve_project_files,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Style {
    /// `[<Extension>] type Holder = …`.
    CsMarked,
    /// `type Holder = …` without the type's marker: FCS reads no extension.
    CsUnmarked,
    /// `type T with member …` in a module.
    FsOptional,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Method,
    Getter,
    Setter,
    Indexer,
    EventAdd,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AttrOn {
    Member,
    Accessor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Renamed {
    No,
    Yes,
    /// `[<CompiledName("W<n>$W")>]` beside a member `W<n>`: the metadata
    /// shape of a witness twin, which the reader hides as compiler output.
    Witness,
    /// `[<CompiledName("Same<n>")>]`, shared with a second extension of
    /// another name that survives the reader's view: a hidden extension
    /// that shares a compiled name with a kept one.
    Shared,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Target {
    Receiver,
    Base,
    Interface,
    Generic,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Container {
    Plain,
    Generic,
    /// An F# record, whose members the reader projects through the F# view
    /// (which hides what fsc synthesises).
    Record,
    /// `[<Extension>] type Holder = G.C<n>.AliasImpl<n>.AliasTarget`: an
    /// attributed abbreviation of an unmarked type in a namespace the call's
    /// `open` does not reach, so only the alias brings its extensions into
    /// scope.
    Alias,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Synth {
    No,
    /// The member carries `[<CompilerGenerated>]`, which the reader's F#
    /// view hides and FCS does not.
    Yes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Home {
    Namespace,
    Module,
    /// `module internal Exts`, the fixture granting the calling project
    /// friendship (`InternalsVisibleTo`).
    InternalModule,
    /// `namespace G.C<n>.Hidden<n>`, holding internal extension holders only
    /// (an internal C#-style container, or an internal `[<AutoOpen>]`
    /// module), so name resolution sees no namespace there at all.
    HiddenNamespace,
    /// [`Home::HiddenNamespace`] with its holders public: a namespace that
    /// holds nothing but them, which the visibility perturbation turns
    /// internal-only.
    SoleNamespace,
    /// `module Hidden<n>` inside an internal `[<AutoOpen>] module Auto<n>` of
    /// `namespace G.C<n>`: opening the namespace (or declaring a file in it)
    /// makes `Hidden<n>` answer to its short name, through a module name
    /// resolution cannot see. The query of `G.C<n>`, which covers its whole
    /// tree, answers for the call too, so only the classification pins what
    /// the certification makes of it.
    HiddenAuto,
    /// [`Home::HiddenAuto`] with `Auto<n>` public.
    SoleAuto,
    Nested,
    AutoOpen,
    Rqa,
}

/// How the calling file reaches the extension: every form of `open` F#
/// has, and none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reach {
    /// `open G.C<n>`.
    OpenNamespace,
    /// `open global.G.C<n>`.
    GlobalNamespace,
    /// `namespace G`, then `open C<n>`: a namespace relative to the enclosing
    /// one.
    RelativeNamespace,
    /// `open G.C<n>.Exts`: an assembly module.
    OpenModule,
    /// `open global.G.C<n>.Exts`.
    GlobalModule,
    /// `open G.C<n>`, then `open Exts`: a module relative to an opened
    /// namespace.
    RelativeModule,
    /// `namespace G.C<n>`, then `open Exts`: a module relative to the
    /// enclosing namespace.
    EnclosingRelativeModule,
    /// `module A<n> = G.C<n>.Exts`, then `open A<n>`.
    AliasModule,
    /// An earlier file's `module A<n> = Exts` in `namespace G.C<n>`, then
    /// `open G.C<n>.A<n>`.
    AliasEarlierFile,
    /// `open type G.C<n>.Holder`.
    OpenType,
    /// `type H<n> = G.C<n>.Holder`, then `open type H<n>`.
    OpenTypeAlias,
    /// No `open`: the file is declared in `namespace G.C<n>`.
    Enclosing,
    /// `open G.C<n>` of a namespace an earlier project file also declares.
    SharedNamespace,
    /// `open G.C<n>.Exts` of a module path an earlier project file also
    /// declares.
    SharedModule,
    /// [`Reach::SharedModule`], the module opened relative to an `open` of
    /// an enclosing namespace (`open G` then `open C1.Exts`), which no drop
    /// sits in.
    SharedModuleRelative,
    /// `open G.C<n>.Exts` of an assembly module whose path an earlier
    /// project file declares as a *namespace*.
    SharedNamespaceOverModule,
    /// `open G.C<n>.Hidden<n>` of an assembly namespace holding internal
    /// extensions only, whose path an earlier project file declares as a
    /// *module*.
    SharedModuleOverNamespace,
    /// `namespace G.C<n>`, then `open Hidden<n>`, where an earlier project
    /// file declares a root module `Hidden<n>`: the written path names the
    /// project module, and the relative reading (`G.C<n>.Hidden<n>`) names
    /// the cell's hidden home.
    RelativeEnclosingOverRoot,
    /// [`Reach::RelativeEnclosingOverRoot`] from a top-level module, the
    /// relative reading through `open G.C<n>`.
    RelativeOpenedOverRoot,
}

impl Reach {
    const ALL: [Reach; 19] = [
        Reach::OpenNamespace,
        Reach::GlobalNamespace,
        Reach::RelativeNamespace,
        Reach::OpenModule,
        Reach::GlobalModule,
        Reach::RelativeModule,
        Reach::EnclosingRelativeModule,
        Reach::AliasModule,
        Reach::AliasEarlierFile,
        Reach::OpenType,
        Reach::OpenTypeAlias,
        Reach::Enclosing,
        Reach::SharedNamespace,
        Reach::SharedModule,
        Reach::SharedModuleRelative,
        Reach::SharedNamespaceOverModule,
        Reach::SharedModuleOverNamespace,
        Reach::RelativeEnclosingOverRoot,
        Reach::RelativeOpenedOverRoot,
    ];

    /// Whether the reach goes through a module, which needs a module home
    /// that may be opened.
    fn through_module(self) -> bool {
        matches!(
            self,
            Reach::OpenModule
                | Reach::GlobalModule
                | Reach::RelativeModule
                | Reach::EnclosingRelativeModule
                | Reach::AliasModule
                | Reach::AliasEarlierFile
                | Reach::SharedModule
                | Reach::SharedModuleRelative
                | Reach::SharedNamespaceOverModule
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Drop {
    No,
    Yes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Cell {
    style: Style,
    kind: Kind,
    attr_on: AttrOn,
    renamed: Renamed,
    target: Target,
    container: Container,
    synth: Synth,
    home: Home,
    reach: Reach,
    drop: Drop,
}

impl Cell {
    fn csharp(self) -> bool {
        matches!(self.style, Style::CsMarked | Style::CsUnmarked)
    }

    /// Whether the cell is one F# can write and a file can reach.
    fn valid(self) -> bool {
        let accessor = matches!(self.kind, Kind::Getter | Kind::Setter | Kind::Indexer);
        let shape = match self.style {
            Style::FsOptional => {
                self.attr_on == AttrOn::Member
                    && self.container == Container::Plain
                    && self.target != Target::Generic
                    && self.home != Home::Namespace
            }
            Style::CsMarked | Style::CsUnmarked => {
                self.kind != Kind::EventAdd
                    && (accessor || self.attr_on == AttrOn::Member)
                    && (self.target != Target::Generic || self.kind == Kind::Method)
            }
        };
        let has_module = self.home != Home::Namespace;
        let reach = if self.reach.through_module() {
            has_module && self.home != Home::Rqa
        } else if matches!(self.reach, Reach::OpenType | Reach::OpenTypeAlias) {
            self.csharp() && self.container != Container::Generic
        } else {
            true
        };
        // The unmarked container is a control, and a drop a perturbation of
        // the plain shapes: neither needs every other dimension.
        let bounded = (self.style != Style::CsUnmarked
            || (self.container == Container::Plain && self.renamed == Renamed::No))
            && (self.drop == Drop::No
                || (self.renamed == Renamed::No
                    && self.container == Container::Plain
                    && self.synth == Synth::No
                    && self.target == Target::Receiver))
            && (self.renamed != Renamed::Shared
                || (self.csharp()
                    && self.kind == Kind::Method
                    && self.synth == Synth::Yes
                    && self.target == Target::Receiver
                    && self.container != Container::Generic))
            && (self.renamed != Renamed::Witness
                || (self.csharp()
                    && self.kind == Kind::Method
                    && self.synth == Synth::No
                    && self.target == Target::Receiver
                    && self.container != Container::Generic))
            && (self.synth == Synth::No
                || (self.csharp()
                    && matches!(self.renamed, Renamed::No | Renamed::Shared)
                    && self.target == Target::Receiver
                    && self.container != Container::Generic));
        // A hidden home is reached only through a project module that shares
        // its path or its short name, and those reaches need one. The auto
        // module's path is not one an `open` can write in full.
        let sole = matches!(
            self.home,
            Home::HiddenNamespace | Home::SoleNamespace | Home::HiddenAuto | Home::SoleAuto
        );
        let over_project_module = matches!(
            self.reach,
            Reach::SharedModuleOverNamespace
                | Reach::RelativeEnclosingOverRoot
                | Reach::RelativeOpenedOverRoot
        );
        let auto = matches!(self.home, Home::HiddenAuto | Home::SoleAuto);
        let hidden = sole == over_project_module
            && !(auto && self.reach == Reach::SharedModuleOverNamespace)
            && (!sole
                || (matches!(self.style, Style::CsMarked | Style::FsOptional)
                    && self.kind == Kind::Method
                    && self.renamed == Renamed::No
                    && self.synth == Synth::No
                    && self.container == Container::Plain
                    && self.target == Target::Receiver
                    && self.drop == Drop::No));
        // The alias is a perturbation of the plain method's container.
        let alias = self.container != Container::Alias
            || (self.style == Style::CsMarked
                && self.kind == Kind::Method
                && self.attr_on == AttrOn::Member
                && self.renamed == Renamed::No
                && self.synth == Synth::No
                && self.target == Target::Receiver
                && self.drop == Drop::No
                && matches!(self.home, Home::Namespace | Home::Module)
                && matches!(
                    self.reach,
                    Reach::OpenNamespace
                        | Reach::SharedNamespace
                        | Reach::Enclosing
                        | Reach::OpenModule
                ));
        // The internal module is a perturbation of the plain method's home.
        let internal = self.home != Home::InternalModule
            || (self.kind == Kind::Method
                && self.renamed == Renamed::No
                && self.synth == Synth::No
                && self.container == Container::Plain
                && self.target == Target::Receiver
                && self.drop == Drop::No);
        shape && reach && bounded && internal && hidden && alias
    }

    /// The method name a call of cell `n` spells. Each cell's names are its
    /// own (an indexer's `Item` aside), so one cell's extension cannot answer
    /// for another's.
    fn call_name(self, n: usize) -> String {
        match self.kind {
            Kind::Method => format!("Ext{n}"),
            Kind::Getter => format!("get_P{n}"),
            Kind::Setter => format!("set_P{n}"),
            Kind::Indexer => "get_Item".to_string(),
            Kind::EventAdd => format!("add_E{n}"),
        }
    }

    fn call_args(self) -> &'static str {
        match self.kind {
            Kind::Method | Kind::Getter | Kind::Indexer => "(1)",
            Kind::Setter => "(1, 0L)",
            Kind::EventAdd => "(System.EventHandler(fun _ _ -> ()))",
        }
    }

    /// The receiver's intrinsic of the call's name, which FCS picks when no
    /// extension joins the group.
    fn intrinsic(self, n: usize) -> String {
        match self.kind {
            Kind::Setter => format!("member _.{}(o: obj, v: obj) = true", self.call_name(n)),
            _ => format!("member _.{}(o: obj) = true", self.call_name(n)),
        }
    }

    /// The module path holding the extension, if any.
    fn module_path(self) -> Option<&'static str> {
        match self.home {
            Home::Namespace
            | Home::HiddenNamespace
            | Home::SoleNamespace
            | Home::HiddenAuto
            | Home::SoleAuto => None,
            Home::Module | Home::InternalModule | Home::AutoOpen | Home::Rqa => Some("Exts"),
            Home::Nested => Some("Outer.Exts"),
        }
    }

    /// The top-level type a drop removes.
    fn top_level(self) -> &'static str {
        match self.home {
            Home::Namespace => "Holder",
            Home::HiddenNamespace | Home::SoleNamespace => match self.style {
                Style::FsOptional => "Exts",
                _ => "Holder",
            },
            Home::HiddenAuto | Home::SoleAuto => "Auto",
            Home::Module | Home::InternalModule | Home::AutoOpen | Home::Rqa => "Exts",
            Home::Nested => "Outer",
        }
    }

    fn all() -> Vec<Cell> {
        let mut cells = Vec::new();
        for style in [Style::CsMarked, Style::CsUnmarked, Style::FsOptional] {
            for kind in [
                Kind::Method,
                Kind::Getter,
                Kind::Setter,
                Kind::Indexer,
                Kind::EventAdd,
            ] {
                for attr_on in [AttrOn::Member, AttrOn::Accessor] {
                    for renamed in [Renamed::No, Renamed::Yes, Renamed::Witness, Renamed::Shared] {
                        for target in [
                            Target::Receiver,
                            Target::Base,
                            Target::Interface,
                            Target::Generic,
                        ] {
                            for (container, synth) in [
                                (Container::Plain, Synth::No),
                                (Container::Plain, Synth::Yes),
                                (Container::Generic, Synth::No),
                                (Container::Record, Synth::No),
                                (Container::Record, Synth::Yes),
                                (Container::Alias, Synth::No),
                            ] {
                                for home in [
                                    Home::Namespace,
                                    Home::Module,
                                    Home::InternalModule,
                                    Home::HiddenNamespace,
                                    Home::SoleNamespace,
                                    Home::HiddenAuto,
                                    Home::SoleAuto,
                                    Home::Nested,
                                    Home::AutoOpen,
                                    Home::Rqa,
                                ] {
                                    for reach in Reach::ALL {
                                        for drop in [Drop::No, Drop::Yes] {
                                            let cell = Cell {
                                                style,
                                                kind,
                                                attr_on,
                                                renamed,
                                                target,
                                                container,
                                                synth,
                                                home,
                                                reach,
                                                drop,
                                            };
                                            if cell.valid() {
                                                cells.push(cell);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        cells
    }
}

const EXTENSION: &str = "System.Runtime.CompilerServices.Extension";

/// The most calling files one FCS project check of the grid holds.
const CHUNK: usize = 300;

/// The namespace of cell `n`.
fn namespace(n: usize) -> String {
    format!("G.C{n}")
}

/// The extension member's declaration lines, unindented.
fn member_lines(n: usize, cell: Cell) -> Vec<String> {
    let mut lines = Vec::new();
    if cell.renamed == Renamed::Witness {
        lines.push(format!("[<CompiledName(\"W{n}$W\")>]"));
    }
    if cell.renamed == Renamed::Shared {
        lines.push(format!("[<CompiledName(\"Same{n}\")>]"));
    }
    if cell.renamed == Renamed::Yes {
        lines.push("[<CompiledName(\"Renamed\")>]".to_string());
    }
    if cell.synth == Synth::Yes {
        lines.push("[<System.Runtime.CompilerServices.CompilerGenerated>]".to_string());
    }
    let target = match cell.target {
        Target::Receiver => "Receiver",
        Target::Base => "Base",
        Target::Interface => "IR",
        Target::Generic => "'T",
    };
    match cell.style {
        Style::FsOptional => {
            let decl = match cell.kind {
                Kind::Method => format!("member r.Ext{n}(i: int) = 0L"),
                Kind::Getter => format!("member r.P{n} with get (i: int) = 0L"),
                Kind::Setter => format!("member r.P{n} with set (i: int) (v: int64) = ()"),
                Kind::Indexer => "member r.Item with get (i: int) = 0L".to_string(),
                Kind::EventAdd => {
                    lines.push("[<CLIEvent>]".to_string());
                    format!(
                        "member r.E{n} = (Event<System.EventHandler, System.EventArgs>()).Publish"
                    )
                    .to_string()
                }
            };
            lines.push(decl);
            let mut out = vec![format!("type {target} with")];
            out.extend(lines.into_iter().map(|l| format!("    {l}")));
            out
        }
        Style::CsMarked | Style::CsUnmarked => {
            let on_member = cell.attr_on == AttrOn::Member;
            if on_member {
                lines.push(format!("[<{EXTENSION}>]"));
            }
            let acc = if on_member {
                String::new()
            } else {
                format!("[<{EXTENSION}>] ")
            };
            let generic = if cell.target == Target::Generic {
                "<'T>"
            } else {
                ""
            };
            let decl = match cell.kind {
                Kind::Method => format!("static member Ext{n}{generic}(r: {target}, i: int) = 0L"),
                Kind::Getter => {
                    format!("static member P{n} with {acc}get (r: {target}, i: int) = 0L")
                }
                Kind::Setter => {
                    format!(
                        "static member P{n} with {acc}set (r: {target}, i: int) (v: int64) = ()"
                    )
                }
                Kind::Indexer => {
                    format!("static member Item with {acc}get (r: {target}, i: int) = 0L")
                }
                Kind::EventAdd => unreachable!("no C#-style event cell"),
            };
            lines.push(decl);
            if cell.container == Container::Alias {
                // The target's members are declared by `alias_target`.
                return vec![
                    format!("[<{EXTENSION}>]"),
                    format!("type Holder = {}.AliasImpl{n}.AliasTarget", namespace(n)),
                ];
            }
            let mut out = Vec::new();
            if cell.style == Style::CsMarked {
                out.push(format!("[<{EXTENSION}>]"));
            }
            let typars = if cell.container == Container::Generic {
                "<'U>"
            } else {
                ""
            };
            out.push(format!("type Holder{typars} ="));
            if cell.container == Container::Record {
                out.push("    { X: int }".to_string());
            }
            if cell.renamed == Renamed::Witness {
                out.push(format!("    static member W{n}() = 0"));
            }
            if cell.renamed == Renamed::Shared {
                out.push(format!("    [<{EXTENSION}>]"));
                out.push(format!("    [<CompiledName(\"Same{n}\")>]"));
                out.push(format!(
                    "    static member Other{n}(r: Receiver, s: string) = 0L"
                ));
            }
            out.extend(lines.into_iter().map(|l| format!("    {l}")));
            out
        }
    }
}

/// The namespace fragment declaring the unmarked type an alias cell's
/// `Holder` abbreviates, then the cell's namespace again.
fn alias_target(n: usize, cell: Cell) -> Vec<String> {
    let ns = namespace(n);
    let plain = member_lines(
        n,
        Cell {
            container: Container::Plain,
            ..cell
        },
    );
    let mut out = vec![format!("namespace {ns}.AliasImpl{n}"), String::new()];
    // Every line of the plain holder but its own marker.
    out.extend(plain.into_iter().skip(1).map(|l| {
        l.replace("type Holder =", "type AliasTarget =")
            .replace("r: Receiver", &format!("r: {ns}.Receiver"))
    }));
    out.push(String::new());
    out.push(format!("namespace {ns}"));
    out.push(String::new());
    out
}

/// Cell `n`'s namespace block of the fixture.
fn cell_source(n: usize, cell: Cell) -> String {
    let mut out = vec![
        format!("namespace {}", namespace(n)),
        String::new(),
        "type Base() = class end".to_string(),
        "type IR = interface end".to_string(),
        "type Receiver() =".to_string(),
        "    inherit Base()".to_string(),
        "    interface IR".to_string(),
        format!("    {}", cell.intrinsic(n)),
        String::new(),
    ];
    if cell.container == Container::Alias {
        out.extend(alias_target(n, cell));
    }
    let body = member_lines(n, cell);
    let indent = |lines: Vec<String>, by: usize| -> Vec<String> {
        lines
            .into_iter()
            .map(|l| format!("{}{l}", " ".repeat(by)))
            .collect()
    };
    match cell.home {
        Home::Namespace => out.extend(body),
        Home::Module => {
            out.push("module Exts =".to_string());
            out.extend(indent(body, 4));
        }
        Home::InternalModule => {
            out.push("module internal Exts =".to_string());
            out.extend(indent(body, 4));
        }
        Home::HiddenNamespace | Home::SoleNamespace => {
            // Its own namespace, with the receiver's types written in full.
            out.push(format!("namespace {}.Hidden{n}", namespace(n)));
            out.push(String::new());
            let ns = namespace(n);
            let internal = if cell.home == Home::HiddenNamespace {
                "internal "
            } else {
                ""
            };
            let body: Vec<String> = body
                .into_iter()
                .map(|l| {
                    l.replace("type Holder", &format!("type {internal}Holder"))
                        .replace("r: Receiver", &format!("r: {ns}.Receiver"))
                        .replace("type Receiver with", &format!("type {ns}.Receiver with"))
                })
                .collect();
            if cell.style == Style::FsOptional {
                out.push("[<AutoOpen>]".to_string());
                out.push(format!("module {internal}Exts ="));
                out.extend(indent(body, 4));
            } else {
                out.extend(body);
            }
        }
        Home::HiddenAuto | Home::SoleAuto => {
            let internal = if cell.home == Home::HiddenAuto {
                "internal "
            } else {
                ""
            };
            out.push("[<AutoOpen>]".to_string());
            out.push(format!("module {internal}Auto{n} ="));
            out.push(format!("    module Hidden{n} ="));
            out.extend(indent(body, 8));
        }
        Home::AutoOpen => {
            out.push("[<AutoOpen>]".to_string());
            out.push("module Exts =".to_string());
            out.extend(indent(body, 4));
        }
        Home::Rqa => {
            out.push("[<RequireQualifiedAccess>]".to_string());
            out.push("module Exts =".to_string());
            out.extend(indent(body, 4));
        }
        Home::Nested => {
            out.push("module Outer =".to_string());
            out.push("    module Exts =".to_string());
            out.extend(indent(body, 8));
        }
    }
    out.join("\n") + "\n"
}

/// The projects the gate test has FCS check: each cell is its own namespace
/// and calling file, so the cells (split by whether the reader is made to
/// drop their type) are checked in independent projects of at most
/// [`CHUNK`] calling files.
fn fcs_projects(cells: &[Cell]) -> Vec<(Drop, Vec<(usize, Cell)>)> {
    [Drop::No, Drop::Yes]
        .into_iter()
        .flat_map(|drop| {
            let mine: Vec<(usize, Cell)> = cells
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, c)| c.drop == drop)
                .collect();
            mine.chunks(CHUNK)
                .map(|chunk| (drop, chunk.to_vec()))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Cell `n`'s block with every extension holder `internal`: the visibility
/// perturbation (the receiver and its base and interface stay public).
fn internalize(block: String) -> String {
    block
        .lines()
        .map(|l| {
            let trimmed = l.trim_start();
            let indent = &l[..l.len() - trimmed.len()];
            for holder in [
                "type Holder",
                "module Exts =",
                "module Outer =",
                "module Auto",
            ] {
                if let Some(rest) = trimmed.strip_prefix(holder) {
                    let keyword = holder.split(' ').next().expect("a keyword");
                    let name = &holder[keyword.len() + 1..];
                    return format!("{indent}{keyword} internal {name}{rest}");
                }
            }
            l.to_string()
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

/// The cells one generated fixture file holds.
const CELLS_PER_FILE: usize = 1000;

/// The fixture's source files: the friendship header, then the cells'
/// blocks in batches of [`CELLS_PER_FILE`].
fn fixture_source(cells: &[Cell], internal: bool) -> Vec<String> {
    // Friendship for the calling projects of the internal-module cells. The
    // oracle names each project after one of its files, so the first and
    // last file of every project the gate test checks is a friend.
    let mut friends = vec!["Shared".to_string()];
    for (_, chunk) in fcs_projects(cells) {
        for &(n, _) in [chunk.first(), chunk.last()].into_iter().flatten() {
            friends.push(format!("Use{n}"));
        }
    }
    let mut out = vec![
        "namespace G.Friends".to_string(),
        "module Attrs =".to_string(),
    ];
    out.extend(friends.iter().map(|f| {
        format!("    [<assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"{f}\")>]")
    }));
    out.push("    do ()".to_string());
    let header = out.join("\n") + "\n";
    let blocks: Vec<String> = cells
        .iter()
        .enumerate()
        .map(|(n, &c)| {
            let block = cell_source(n, c);
            if internal { internalize(block) } else { block }
        })
        .collect();
    std::iter::once(header)
        .chain(blocks.chunks(CELLS_PER_FILE).map(|batch| batch.join("\n")))
        .collect()
}

/// The calling file of cell `n`, and its probed call.
fn use_source(n: usize, cell: Cell) -> (String, Probe) {
    let ns = namespace(n);
    let call = format!("(asR{n} x).{}{}", cell.call_name(n), cell.call_args());
    let binder = format!("c{n}");
    let module = || cell.module_path().expect("a module home");
    let holder = || match cell.module_path() {
        Some(m) => format!("{ns}.{m}.Holder"),
        None => format!("{ns}.Holder"),
    };
    // A file `module Use<n>` that opens with `opens`.
    let top = |opens: String| {
        format!(
            "module Use{n}\nlet asR{n} (r: {ns}.Receiver) = r\n{opens}\nlet {binder} x = {call}\n"
        )
    };
    // A file declared in `namespace in_ns` whose module `Use<n>` opens with
    // `opens` (none if empty).
    let nested = |in_ns: &str, opens: String| {
        let opens = if opens.is_empty() {
            String::new()
        } else {
            format!("    {opens}\n")
        };
        format!(
            "namespace {in_ns}\nmodule Use{n} =\n{opens}    let asR{n} (r: {ns}.Receiver) = r\n    let {binder} x = {call}\n"
        )
    };
    let source = match cell.reach {
        Reach::OpenNamespace | Reach::SharedNamespace => top(format!("open {ns}")),
        Reach::GlobalNamespace => top(format!("open global.{ns}")),
        Reach::RelativeNamespace => nested("G", format!("open C{n}")),
        Reach::OpenModule | Reach::SharedModule | Reach::SharedNamespaceOverModule => {
            top(format!("open {ns}.{}", module()))
        }
        Reach::SharedModuleOverNamespace => top(format!("open {ns}.Hidden{n}")),
        Reach::RelativeEnclosingOverRoot => nested(&ns, format!("open Hidden{n}")),
        Reach::RelativeOpenedOverRoot => top(format!("open {ns}\nopen Hidden{n}")),
        Reach::GlobalModule => top(format!("open global.{ns}.{}", module())),
        Reach::RelativeModule => top(format!("open {ns}\nopen {}", module())),
        Reach::EnclosingRelativeModule => nested(&ns, format!("open {}", module())),
        Reach::AliasModule => top(format!("module A{n} = {ns}.{}\nopen A{n}", module())),
        Reach::AliasEarlierFile => top(format!("open {ns}.A{n}")),
        Reach::OpenType => top(format!("open type {}", holder())),
        Reach::OpenTypeAlias => top(format!("type H{n} = {}\nopen type H{n}", holder())),
        Reach::Enclosing => nested(&ns, String::new()),
        Reach::SharedModuleRelative => top(format!("open G\nopen C{n}.{}", module())),
    };
    (
        source,
        Probe {
            file: 0,
            binder,
            text: call,
        },
    )
}

/// Whether the extension gate must read the calling file's `open` as
/// enumerated: only inside the certified domain (an `open` whose written
/// path is a namespace, read at that path, no split of which holds a
/// dropped type, and whose every other candidate reading holds nothing in
/// the assemblies). Every other form is unenumerated, and a file with no
/// `open` has none to read.
fn certified(cell: Cell) -> bool {
    match cell.reach {
        Reach::OpenNamespace | Reach::GlobalNamespace | Reach::SharedNamespace => {
            cell.drop == Drop::No
        }
        Reach::Enclosing | Reach::SharedModuleOverNamespace => true,
        _ => false,
    }
}

/// The earlier project file's declaration that shares cell `n`'s namespace
/// or module path, for the reaches that need one.
fn shared_source(n: usize, cell: Cell) -> Option<String> {
    let ns = namespace(n);
    match cell.reach {
        Reach::SharedNamespace => Some(format!(
            "namespace {ns}\nmodule Shared{n} =\n    let v{n} = 1\n"
        )),
        Reach::SharedModuleOverNamespace => Some(format!(
            "namespace {ns}\nmodule Hidden{n} =\n    let v{n} = 1\n"
        )),
        Reach::RelativeEnclosingOverRoot | Reach::RelativeOpenedOverRoot => Some(format!(
            "namespace global\nmodule Hidden{n} =\n    let v{n} = 1\n"
        )),
        Reach::SharedNamespaceOverModule => Some(format!(
            "namespace {ns}.{}\nmodule SharedNs{n} =\n    let v{n} = 1\n",
            cell.module_path().expect("a module home")
        )),
        Reach::AliasEarlierFile => Some(format!(
            "namespace {ns}\nmodule A{n} = {ns}.{}\n",
            cell.module_path().expect("a module home")
        )),
        Reach::SharedModule | Reach::SharedModuleRelative => {
            Some(match cell.module_path().expect("a module home") {
                "Outer.Exts" => {
                    format!(
                        "namespace {ns}\nmodule Outer =\n    module Exts =\n        let v{n} = 1\n"
                    )
                }
                m => format!("namespace {ns}\nmodule {m} =\n    let v{n} = 1\n"),
            })
        }
        _ => None,
    }
}

/// An assembly view that drops the named top-level types of `drop`,
/// recording each as the reader records a type it cannot decode.
struct DroppingView<'a> {
    inner: &'a Ecma335Assembly,
    drop: &'a [(Vec<String>, &'static str)],
}

/// Whether `e` is one of `types`, a list of `(namespace, top-level name)`.
fn names_one_of(e: &Entity, types: &[(Vec<String>, &'static str)]) -> bool {
    types.iter().any(|(ns, name)| {
        e.namespace == *ns && (e.name == *name || e.name.starts_with(&format!("{name}`")))
    })
}

impl EcmaView for DroppingView<'_> {
    fn identity(&self) -> &AssemblyIdentity {
        self.inner.identity()
    }

    fn assembly_refs(&self) -> Vec<AssemblyIdentity> {
        self.inner.assembly_refs()
    }

    fn enumerate_type_defs_with_skips(
        &self,
    ) -> Result<(Vec<Entity>, AssemblyProjectionSkips), ImportError> {
        let (entities, mut skips) = self.inner.enumerate_type_defs_with_skips()?;
        let mut kept = Vec::new();
        for e in entities {
            if names_one_of(&e, self.drop) {
                skips.dropped_types.push(SkippedProjectionItem {
                    name: format!("{}.{}", e.namespace.join("."), e.name),
                    reason: "dropped by the grid".to_string(),
                });
            } else {
                kept.push(e);
            }
        }
        Ok((kept, skips))
    }

    fn assembly_auto_opens(&self) -> Result<Vec<String>, ImportError> {
        self.inner.assembly_auto_opens()
    }

    fn type_forwarders(&self) -> Result<Vec<TypeForwarder>, ImportError> {
        self.inner.type_forwarders()
    }

    fn qualified_names(&self) -> Option<Vec<String>> {
        self.inner.qualified_names()
    }

    fn fsharp_resources(&self) -> Result<Vec<FSharpResource>, ImportError> {
        self.inner.fsharp_resources()
    }

    fn doc_id_dialect(&self) -> Result<borzoi_assembly::doc_id::DocIdDialect, ImportError> {
        self.inner.doc_id_dialect()
    }
}

/// The env of the SDK's core references and the fixture, the reader made to
/// drop each `(namespace, top-level type)` of `drop`.
fn env_of(fixture: &Path, drop: Vec<(Vec<String>, &'static str)>) -> AssemblyEnv {
    let core = std::fs::read(ensure_fsharp_core_dll()).expect("read FSharp.Core.dll");
    let sysrt_path = ensure_system_runtime_dll();
    let netstd_path = sysrt_path
        .parent()
        .expect("ref dir")
        .join("netstandard.dll");
    let sysrt = std::fs::read(&sysrt_path).expect("read System.Runtime.dll");
    let netstd = std::fs::read(&netstd_path).expect("read netstandard.dll");
    let grid = std::fs::read(fixture).expect("read the grid fixture");
    let core = Ecma335Assembly::parse(&core).expect("parse FSharp.Core.dll");
    let sysrt = Ecma335Assembly::parse(&sysrt).expect("parse System.Runtime.dll");
    let netstd = Ecma335Assembly::parse(&netstd).expect("parse netstandard.dll");
    let grid = Ecma335Assembly::parse(&grid).expect("parse the grid fixture");
    let views: Vec<DroppingView> = [&core, &sysrt, &netstd, &grid]
        .into_iter()
        .map(|inner| DroppingView { inner, drop: &drop })
        .collect();
    AssemblyEnv::from_views(&views).expect("build the grid's env")
}

/// The cells FCS must bind to the extension: the plain shape of each kind
/// and style, reached by an `open` of what holds it. A fixture that stops
/// producing extensions fails here instead of passing vacuously.
fn liveness(cell: Cell) -> bool {
    cell.drop == Drop::No
        && cell.renamed == Renamed::No
        && cell.target == Target::Receiver
        && cell.container == Container::Plain
        && cell.synth == Synth::No
        && match cell.style {
            Style::CsMarked => {
                cell.home == Home::Namespace
                    && cell.reach == Reach::OpenNamespace
                    && (cell.kind == Kind::Method || cell.attr_on == AttrOn::Accessor)
            }
            Style::FsOptional => cell.home == Home::Module && cell.reach == Reach::OpenModule,
            Style::CsUnmarked => false,
        }
}

#[test]
fn the_gate_declines_every_extension_fcs_binds_through_an_assembly() {
    let cells = Cell::all();
    let dll = ensure_ext_assembly_grid_built(|| fixture_source(&cells, false));
    let drops: Vec<(Vec<String>, &'static str)> = cells
        .iter()
        .enumerate()
        .filter(|(_, c)| c.drop == Drop::Yes)
        .map(|(n, c)| {
            (
                namespace(n).split('.').map(str::to_owned).collect(),
                c.top_level(),
            )
        })
        .collect();
    let whole = env_of(dll, Vec::new());
    let dropped = env_of(dll, drops);

    let mut failures = Vec::new();
    let mut bound = 0usize;
    let mut graded = 0usize;
    let chunks = fcs_projects(&cells);
    let results = par_map(chunks.len(), |i| {
        let (drop, mine) = &chunks[i];
        let env = if *drop == Drop::No { &whole } else { &dropped };
        let shared: String = mine
            .iter()
            .filter_map(|&(n, c)| shared_source(n, c))
            .collect::<Vec<_>>()
            .join("\n");
        let mut sources: Vec<(String, String)> = Vec::new();
        if !shared.is_empty() {
            sources.push(("Shared.fs".to_string(), shared));
        }
        let mut probes = Vec::new();
        for &(n, c) in mine {
            let (src, mut probe) = use_source(n, c);
            probe.file = sources.len();
            sources.push((format!("Use{n}.fs"), src));
            probes.push(probe);
        }
        let refs: Vec<(&str, String)> = sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.clone()))
            .collect();
        check_files(env, &[dll], &refs, &probes)
    });
    for ((drop, mine), checked) in chunks.iter().zip(&results) {
        failures.extend(
            checked
                .unsound
                .iter()
                .map(|u| format!("{drop:?}: unsound: {u}")),
        );
        if checked.calls.len() != mine.len() {
            failures.push(format!(
                "{drop:?}: {} of {} calls graded",
                checked.calls.len(),
                mine.len()
            ));
            continue;
        }
        for (&(n, cell), outcome) in mine.iter().zip(&checked.calls) {
            let label = format!("C{n} {cell:?}");
            let Some(fcs) = outcome.fcs.as_deref() else {
                if liveness(cell) {
                    failures.push(format!("{label}: FCS typed nothing at a cell it must bind"));
                }
                continue;
            };
            if outcome.opens_unenumerated == certified(cell) {
                failures.push(format!(
                    "{label}: the gate reads the `open` as {}, outside the certified domain's verdict",
                    if outcome.opens_unenumerated { "unenumerated" } else { "enumerated" }
                ));
            }
            graded += 1;
            let binds = fcs != "System.Boolean";
            bound += usize::from(binds);
            if binds && outcome.gate.is_none() {
                failures.push(format!(
                    "{label}: FCS binds the extension (`{fcs}`), and the gate lets it stand; ours {:?}",
                    outcome.ours
                ));
            }
            if liveness(cell) && !binds {
                failures.push(format!(
                    "{label}: FCS must bind the extension, and types `{fcs}`"
                ));
            }
        }
    }
    eprintln!(
        "{} cells: {graded} graded, FCS binds the extension in {bound}",
        cells.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn every_extension_fcs_reads_in_the_assembly_is_projected() {
    let cells = Cell::all();
    let dll = ensure_ext_assembly_grid_built(|| fixture_source(&cells, false));
    let whole = env_of(dll, Vec::new());
    let (root, written) = temp_fs_tree("ext_assembly_grid", &[("Anchor.fs", "module Anchor\n")]);
    let members = invoke_fcs_dump_extension_members(&written[0].0, dll);
    let _ = std::fs::remove_dir_all(&root);
    let mut failures = Vec::new();
    for m in &members {
        let is_static = !m.is_instance;
        let namespace: Vec<String> = m.namespace.split('.').map(str::to_owned).collect();
        let label = format!(
            "{} `{}` ({}, compiled `{}`)",
            m.entity, m.name, m.style, m.compiled_name
        );
        if !borzoi_sema::test_support::extension_named_in_namespace(
            &whole, &namespace, &m.name, is_static,
        ) {
            failures.push(format!(
                "{label}: not in the answer for namespace {}",
                m.namespace
            ));
        }
    }
    let candidates = cells
        .iter()
        .filter(|c| c.style != Style::CsUnmarked && c.container == Container::Plain)
        .count();
    eprintln!(
        "{} extension members FCS reads; {candidates} cells declare one it could",
        members.len()
    );
    assert!(
        members.len() * 2 >= candidates,
        "FCS reads {} extension members in a fixture of {candidates} candidate cells",
        members.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// One calling project: its `(path, source)` files and, per calling file,
/// its index and the call's method name.
type CallingProject = (Vec<(String, String)>, Vec<(usize, String)>);

/// The calling projects of `cells`, each a chunk of at most [`CHUNK`]
/// calling files after the earlier file their reaches share.
fn calling_projects(cells: &[(usize, Cell)]) -> Vec<CallingProject> {
    cells
        .chunks(CHUNK)
        .map(|chunk| {
            let shared: String = chunk
                .iter()
                .filter_map(|&(n, c)| shared_source(n, c))
                .collect::<Vec<_>>()
                .join("\n");
            let mut sources: Vec<(String, String)> = Vec::new();
            if !shared.is_empty() {
                sources.push(("Shared.fs".to_string(), shared));
            }
            let mut calls = Vec::new();
            for &(n, c) in chunk {
                let (src, _) = use_source(n, c);
                calls.push((sources.len(), c.call_name(n)));
                sources.push((format!("Use{n}.fs"), src));
            }
            (sources, calls)
        })
        .collect()
}

/// Whether the gate declines each call of `project` with `env`'s assemblies
/// in scope, resolving it without inference (the gate reads resolution
/// alone).
fn gate_declines(env: &AssemblyEnv, project: &CallingProject) -> Vec<bool> {
    let (sources, calls) = project;
    let parsed: Vec<(ImplFile, SyntaxRecovery)> = sources
        .iter()
        .map(|(_, s)| {
            let p = parse(s);
            let recovery = SyntaxRecovery::of(&p);
            (ImplFile::cast(p.root).expect("impl file"), recovery)
        })
        .collect();
    let paths: Vec<std::path::PathBuf> = sources.iter().map(|(p, _)| p.into()).collect();
    let files: Vec<SourceFile> = parsed
        .iter()
        .map(|(f, _)| SourceFile::Impl(f.clone()))
        .collect();
    let project: Vec<ProjectFile> = files
        .iter()
        .cloned()
        .zip(parsed.iter().map(|(_, r)| r.clone()))
        .zip(qualified_names(&files, &paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect();
    let resolved = resolve_project_files(&project, env);
    calls
        .iter()
        .map(|(file, name)| {
            borzoi_sema::test_support::extension_gate_decline(
                resolved.file(*file),
                env,
                name,
                false,
            )
            .is_some()
        })
        .collect()
}

/// The visibility perturbation: every extension holder of the fixture
/// (container type, module, enclosing module) turned `internal`, the
/// receiver staying public. With friendship granted FCS sees an internal
/// extension as it sees a public one, so the gate's assembly side must not
/// read visibility at all: no call the public fixture's gate declines may
/// read as absent against the internal twin. FCS-free: it compares the gate
/// with itself.
#[test]
fn turning_an_extension_internal_never_makes_it_absent() {
    let cells = Cell::all();
    let public = ensure_ext_assembly_grid_built(|| fixture_source(&cells, false));
    let internal = ensure_ext_assembly_grid_internal_built(|| fixture_source(&cells, true));
    let public_env = env_of(public, Vec::new());
    let internal_env = env_of(internal, Vec::new());
    let indexed: Vec<(usize, Cell)> = cells.iter().copied().enumerate().collect();
    let projects = calling_projects(&indexed);
    let answers = par_map(projects.len(), |i| {
        (
            gate_declines(&public_env, &projects[i]),
            gate_declines(&internal_env, &projects[i]),
        )
    });
    let mut failures = Vec::new();
    let mut declined = 0usize;
    for ((_, calls), (public, internal)) in projects.iter().zip(&answers) {
        for (k, (file, name)) in calls.iter().enumerate() {
            declined += usize::from(public[k]);
            if public[k] && !internal[k] {
                let n: usize = name
                    .trim_start_matches(|c: char| !c.is_ascii_digit())
                    .parse()
                    .unwrap_or(usize::MAX);
                let cell = cells.get(n).map(|c| format!("{c:?}")).unwrap_or_default();
                failures.push(format!(
                    "file {file} `{name}`: declined against the public fixture, absent \
                     against the internal one; {cell}"
                ));
            }
        }
    }
    eprintln!(
        "{} cells: the public fixture's gate declines {declined}; {} turn absent when internal",
        cells.len(),
        failures.len()
    );
    assert!(
        declined * 2 > cells.len(),
        "only {declined} declines to perturb"
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
