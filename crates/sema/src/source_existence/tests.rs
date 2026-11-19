//! The walk's own cases, FCS-free: what each input channel declines or
//! approximates, and what an incomplete certificate does.

// The walk's syntax dispatch is what the parent module's lint holds; a test's
// match over its own outcomes reports the rest.
#![allow(clippy::wildcard_enum_match_arm)]

use super::*;
use crate::qnof::qualified_names;
use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_cst::syntax::{ImplFile, SigFile};
use std::path::PathBuf;

/// The project of `files` (name, text), parsed with no defines.
fn project(files: &[(&str, &str)]) -> Vec<ProjectFile> {
    project_with(files, &[])
}

/// Our reading of `files` under `routes`, or certified by spelling.
fn read_with(files: &[(&str, &str)], routes: Option<MarkerRoutes>) -> SourceExistence {
    let project = project(files);
    let refs: Vec<&ProjectFile> = project.iter().collect();
    let routes = routes.unwrap_or_else(|| certify_by_spelling(&refs));
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    source_existence(Producer::Evaluated {
        items: &items,
        routes: &routes,
        providers: ProviderReferences::None,
    })
}

fn read(files: &[(&str, &str)]) -> SourceExistence {
    read_with(files, None)
}

/// Every member head shape the generator met is named: a static property
/// with no receiver (a bare-name pattern), backticked names, an indexer, and
/// names that are keywords.
#[test]
fn bare_member_heads_are_named() {
    for src in [
        "module M\nexception internal Item of string\n",
        "module M\ntype System.String with\n    member x.Item with get () = 1 and set (v: int) = ()\n",
        "module M\ntype System.String with\n    member x.ToString = 1\n",
        "module M\nmodule internal ``member`` =\n    let x = 1\n",
        "exception internal Item of string\nmodule X =\n    let y = 1\n",
        "module M\ntype public ``member`` = delegate of int -> int\n",
        "module M\ntype System.String with\n    static member ``odd member`` = 2\n",
        "module M\ntype System.String with\n    member x.``odd member``() = 1\n",
        "module M\ntype System.Int32 with\n    static member ``odd member``() = 1\n",
    ] {
        let r = read(&[("A.fs", src)]);
        assert!(matches!(r, SourceExistence::Read(_)), "{src}: {r:?}");
    }
}

/// [`project`] with `defines` defined.
fn project_with(files: &[(&str, &str)], defines: &[&str]) -> Vec<ProjectFile> {
    // The parser's own set type, inferred from `ParseOptions::symbols`.
    let symbols = defines.iter().map(|d| (*d).to_owned()).collect();
    let mut parsed = Vec::new();
    let mut recoveries = Vec::new();
    for (name, text) in files {
        let kind = if name.ends_with(".fsi") {
            FileKind::Sig
        } else {
            FileKind::Impl
        };
        let p = parse_with_options(
            text,
            ParseOptions {
                file_kind: kind,
                symbols: &symbols,
                lang: borzoi_cst::language_version::LanguageVersion::DEFAULT,
            },
        );
        recoveries.push(SyntaxRecovery::of(&p));
        parsed.push(match kind {
            FileKind::Sig => SourceFile::Sig(SigFile::cast(p.root).expect("sig")),
            FileKind::Impl => SourceFile::Impl(ImplFile::cast(p.root).expect("impl")),
        });
    }
    let paths: Vec<PathBuf> = files
        .iter()
        .map(|(n, _)| PathBuf::from("/p").join(n))
        .collect();
    let qnofs = qualified_names(&parsed, &paths);
    parsed
        .into_iter()
        .zip(recoveries)
        .zip(qnofs)
        .map(|((f, r), q)| ProjectFile::new(f, q, r))
        .collect()
}

/// The pickle rows of a `Read`, or a panic naming `what`.
fn rows(r: &SourceExistence, what: &str) -> Vec<PickledEntityRow> {
    match r {
        SourceExistence::Read(s) => match &s.index.pickle {
            PickleLayer::Read(rows) => rows.clone(),
            other => panic!("{what}: pickle {other:?}"),
        },
        SourceExistence::Unread(why) => panic!("{what}: unread {why:?}"),
    }
}

fn has_entity(r: &SourceExistence, logical: &str, compiled: &str, kind: PickledEntityKind) -> bool {
    matches!(r, SourceExistence::Read(_))
        && rows(r, logical).iter().any(|row| {
            row.logical_name == logical && row.compiled_name == compiled && row.kind == kind
        })
}

fn extension_names(r: &SourceExistence) -> Vec<Vec<String>> {
    match r {
        SourceExistence::Read(s) => s.index.extensions.iter().map(|e| e.names.clone()).collect(),
        SourceExistence::Unread(_) => Vec::new(),
    }
}

/// What a witness observed of the walk.
#[derive(Debug)]
enum Observed {
    /// Read with no approximation, and the witness's row predicate held.
    Exact,
    /// Read, naming these approximations.
    Approximated(BTreeSet<Approximation>),
    /// Unread.
    Unread(ExistenceUnread),
    /// The caller's channel: reading the same source two ways the caller
    /// chooses between gave different rows.
    CallerDecides,
    /// The witness's row predicate failed.
    Wrong(String),
}

fn observe(r: SourceExistence, holds: impl Fn(&SourceExistence) -> bool) -> Observed {
    match &r {
        SourceExistence::Unread(why) => Observed::Unread(why.clone()),
        SourceExistence::Read(s) if !s.approximations.is_empty() => {
            Observed::Approximated(s.approximations.clone())
        }
        SourceExistence::Read(_) if holds(&r) => Observed::Exact,
        SourceExistence::Read(s) => Observed::Wrong(format!("{:#?}", s.index)),
    }
}

/// One witness of `channel`: a producer exhibiting it, and what the walk
/// made of it.
fn witness(channel: Channel) -> Observed {
    use PickledEntityKind as K;
    let one = |src: &str| read(&[("Lib.fs", src)]);
    match channel {
        Channel::UnreadableItem => {
            let project = project(&[("A.fs", "module A\nlet x = 1\n")]);
            let routes = MarkerRoutes::Certified(BTreeMap::new());
            let items = [
                CompileItem::Parsed(&project[0]),
                CompileItem::Unreadable("B.fs"),
            ];
            observe(
                source_existence(Producer::Evaluated {
                    items: &items,
                    routes: &routes,
                    providers: ProviderReferences::None,
                }),
                |_| true,
            )
        }
        Channel::FoldRefused => observe(source_existence(Producer::FoldRefused("why")), |_| true),
        Channel::UnservedTfm => {
            observe(source_existence(Producer::UnservedTfm("net8.0")), |_| true)
        }
        Channel::Defines => {
            let src = [(
                "Lib.fs",
                "namespace N\n#if A_ONLY\ntype Shown = int\n#endif\n",
            )];
            let read_under = |defines: &[&str]| {
                let project = project_with(&src, defines);
                let routes = MarkerRoutes::Certified(BTreeMap::new());
                let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
                source_existence(Producer::Evaluated {
                    items: &items,
                    routes: &routes,
                    providers: ProviderReferences::None,
                })
            };
            let (a, b) = (read_under(&["A_ONLY"]), read_under(&[]));
            if has_entity(&a, "Shown", "Shown", K::Abbreviation)
                && !has_entity(&b, "Shown", "Shown", K::Abbreviation)
            {
                Observed::CallerDecides
            } else {
                Observed::Wrong(format!("{a:?} / {b:?}"))
            }
        }
        Channel::LanguageVersion => {
            // The version decides the parse: `#elif` is an error before 11.
            let src = "namespace N\n#if A\ntype X = int\n#elif B\ntype Y = int\n#endif\n";
            let parse_at = |lang| {
                let p = parse_with_options(
                    src,
                    ParseOptions {
                        file_kind: FileKind::Impl,
                        symbols: &Default::default(),
                        lang,
                    },
                );
                p.errors.is_empty()
            };
            use borzoi_cst::language_version::LanguageVersion as L;
            if parse_at(L::DEFAULT) != parse_at(L::V8_0) {
                Observed::CallerDecides
            } else {
                Observed::Wrong("the language version decides nothing here".to_owned())
            }
        }
        Channel::GeneratedItems => {
            let without = read(&[("A.fs", "module A\nlet x = 1\n")]);
            let with = read(&[
                ("A.fs", "module A\nlet x = 1\n"),
                (
                    "AssemblyInfo.fs",
                    "namespace FSharp\n[<assembly: AutoOpen(\"A\")>]\ndo ()\n",
                ),
            ]);
            if without != with {
                Observed::CallerDecides
            } else {
                Observed::Wrong("a generated item changes nothing".to_owned())
            }
        }
        Channel::Recovered => observe(one("module M\nlet x = (1 +\n"), |_| true),
        Channel::HashReference => observe(one("module M\n#r \"x.dll\"\nlet x = 1\n"), |_| true),
        Channel::SignaturePair => observe(
            read(&[
                ("Lib.fsi", "module M\nval x: int\n"),
                ("Lib.fs", "module M\nlet x = 1\ntype Hidden = int\n"),
            ]),
            |_| true,
        ),
        Channel::HeaderlessFile => observe(one("let x = 1\n"), |r| {
            has_entity(r, "Lib", "Lib", K::Module)
        }),
        Channel::AnonymousModuleName => observe(read(&[("Lïb.fs", "let x = 1\n")]), |_| true),
        Channel::Namespace => observe(
            one("namespace A.B\ntype T = int\nnamespace global\ntype U = int\n"),
            |r| has_entity(r, "A", "A", K::Namespace) && has_entity(r, "B", "B", K::Namespace),
        ),
        Channel::Module => observe(
            one("module A.M\nmodule rec Inner =\n    let x = 1\n"),
            |r| has_entity(r, "M", "M", K::Module) && has_entity(r, "Inner", "Inner", K::Module),
        ),
        Channel::ModuleAbbreviation => observe(
            one("module M\nmodule Real =\n    let x = 1\nmodule Alias = Real\n"),
            |r| {
                !rows(r, "alias")
                    .iter()
                    .any(|row| row.logical_name == "Alias")
            },
        ),
        // `FooModule` may be `FooModuleModule`, which canonical spelling
        // keeps apart.
        Channel::ModuleSuffix => observe(
            one("namespace N\nmodule FooModule =\n    let x = 1\n"),
            |_| true,
        ),
        Channel::TypeDefinition => observe(
            one("namespace N\ntype C() = member _.X = 1\ntype U = A | B\n"),
            |r| has_entity(r, "C", "C", K::Type) && has_entity(r, "U", "U", K::Type),
        ),
        // Canonical spelling strips the arity: the walk writes none.
        Channel::GenericArity => observe(
            one("namespace N\ntype G<'a, [<Measure>] 'u> = { X: 'a }\n"),
            |r| has_entity(r, "G", "G", K::Type),
        ),
        Channel::Abbreviation => observe(one("namespace N\ntype I = int\n"), |r| {
            has_entity(r, "I", "I", K::Abbreviation)
        }),
        Channel::AbbreviationOrUnion => observe(one("namespace N\ntype I = Somewhere\n"), |_| true),
        Channel::EntityKind => observe(one("namespace N\n[<Measure>] type m\n"), |r| {
            has_entity(r, "m", "m", K::Type)
        }),
        Channel::Exception => observe(one("namespace N\nexception E of string\n"), |r| {
            has_entity(r, "E", "E", K::Exception)
        }),
        Channel::Accessibility => observe(
            one("namespace N\nmodule internal M =\n    type T = int\n"),
            |r| {
                rows(r, "access")
                    .iter()
                    .any(|row| row.logical_name == "T" && row.public)
            },
        ),
        Channel::TypeProviderUse => observe(one("namespace N\ntype T = P<\"x\">\n"), |_| true),
        Channel::AutoOpenAttribute => observe(
            one("namespace N\n[<AutoOpen>]\nmodule M =\n    let x = 1\n"),
            |r| {
                rows(r, "auto")
                    .iter()
                    .any(|row| row.logical_name == "M" && row.auto_open)
            },
        ),
        Channel::ExtensionAttribute => observe(
            one(
                "namespace N\n[<System.Runtime.CompilerServices.Extension>]\ntype E =\n    static member X = 1\n",
            ),
            |r| {
                rows(r, "ext")
                    .iter()
                    .any(|row| row.logical_name == "E" && row.extension)
            },
        ),
        Channel::CompiledNameAttribute => observe(
            one("namespace N\n[<CompiledName(\"R\")>]\ntype T() = class end\n"),
            |r| has_entity(r, "T", "R", K::Type),
        ),
        Channel::AttributeTarget => observe(
            one(
                "module M\ntype System.String with\n    [<return: CompiledName(\"Q\")>]\n    member s.Orig() = 1\n",
            ),
            |r| extension_names(r) == vec![vec!["Orig".to_owned(), "String.Orig".to_owned()]],
        ),
        Channel::UnreadableCompiledName => observe(
            one("namespace N\n[<CompiledName(Some.Constant)>]\ntype T() = class end\n"),
            |_| true,
        ),
        Channel::AssemblyAutoOpen => observe(
            one("namespace N\n[<assembly: AutoOpen(\"N\")>]\ndo ()\n"),
            |r| matches!(r, SourceExistence::Read(s) if s.assembly_auto_opens == ["N"]),
        ),
        Channel::AssemblyAutoOpenUnreadable => observe(
            one("namespace N\n[<assembly: AutoOpen(Some.Constant)>]\ndo ()\n"),
            |_| true,
        ),
        Channel::TypeProviderAssembly => observe(
            one(
                "namespace N\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\n",
            ),
            |_| true,
        ),
        Channel::UncertifiedAttribute => observe(
            read_with(
                &[(
                    "Lib.fs",
                    "namespace N\n[<AutoOpen>]\nmodule M =\n    let x = 1\n",
                )],
                Some(MarkerRoutes::Certified(BTreeMap::new())),
            ),
            |_| true,
        ),
        Channel::OptionalExtensionMember => observe(
            one("module M\ntype System.String with\n    member s.Shout = s\n"),
            |r| {
                extension_names(r).contains(&vec![
                    "Shout".to_owned(),
                    "String.get_Shout".to_owned(),
                    "get_Shout".to_owned(),
                ])
            },
        ),
        Channel::IntrinsicAugmentation => observe(
            one("module M\ntype R = { X: int }\ntype R with\n    member r.Y = 1\n"),
            |r| extension_names(r).is_empty(),
        ),
        Channel::AugmentationKind => observe(
            one(
                "module M\ntype T =\n    inherit System.Object\n    abstract M: int\ntype T with\n    member t.N = 1\n",
            ),
            |_| true,
        ),
        Channel::CSharpExtensionMember => observe(
            one(
                "module M\ntype E =\n    [<System.Runtime.CompilerServices.Extension>]\n    static member Twice(s: string) = s\n",
            ),
            |r| extension_names(r).contains(&vec!["Twice".to_owned()]),
        ),
        Channel::ExtensionBinding => observe(
            one(
                "module M\n[<System.Runtime.CompilerServices.Extension>]\nlet shout (s: string) = s\n",
            ),
            |r| extension_names(r).contains(&vec!["shout".to_owned()]),
        ),
        Channel::BindingPattern => observe(
            one("module M\n[<System.Runtime.CompilerServices.Extension>]\nlet (a, b) = (1, 2)\n"),
            |_| true,
        ),
        Channel::ImpliedExtensionAttribute => observe(
            one(
                "namespace N\nmodule M =\n    [<System.Runtime.CompilerServices.Extension>]\n    let shout (s: string) = s\n",
            ),
            |r| {
                rows(r, "implied")
                    .iter()
                    .any(|row| row.logical_name == "M" && !row.extension)
            },
        ),
        Channel::UnnamedDeclaration => observe(
            one("module M\n[<System.Runtime.CompilerServices.Extension>]\nlet _ = 1\n"),
            |_| true,
        ),
        Channel::ReadingsBudget => {
            // Twenty nested modules whose names end in `Module`: each
            // doubles the paths under it.
            let mut src = String::from("namespace N\n");
            for depth in 0..20 {
                let indent = "    ".repeat(depth);
                src.push_str(&format!("{indent}module M{depth}Module =\n"));
            }
            src.push_str(&format!("{}let x = 1\n", "    ".repeat(20)));
            observe(read(&[("Lib.fs", &src)]), |_| true)
        }
        Channel::RejectedShape => observe(
            one("module M\ntype System.String with\n    abstract M: int\n"),
            |_| true,
        ),
        // The second `f` takes `f@7`: the walk emits every name it may.
        Channel::ClassLet => observe(
            one(
                "module M\nopen System.Runtime.CompilerServices\ntype T() =\n    [<Extension>]\n    static let f (s: string) = s\n    [<Extension>]\n    static let f (s: string) = s\n    member _.G = f \"x\"\n",
            ),
            |_| true,
        ),
        Channel::OutsideDomain => observe(one("module M\ntype X.Y = { N: int }\n"), |_| true),
        Channel::LineDirective => observe(
            one(
                "module M\n# 10 \"Other.fs\"\ntype T() =\n    [<System.Runtime.CompilerServices.Extension>]\n    static let f (s: string) = s\n    member _.G = f \"x\"\n",
            ),
            |_| true,
        ),
    }
}

/// Every channel's witness does what the inventory says the walk does with
/// it. A channel added to [`Channel`] fails to compile until it has a
/// treatment and a witness.
#[test]
fn the_inventory_is_what_the_walk_does() {
    let mut failures = Vec::new();
    for &channel in Channel::ALL {
        let observed = witness(channel);
        let agrees = match (channel.treatment(), &observed) {
            (Treatment::Modelled, Observed::Exact) => true,
            (Treatment::Approximated(a), Observed::Approximated(names)) => names.contains(&a),
            (Treatment::Declined, Observed::Unread(_)) => true,
            (Treatment::Caller, Observed::CallerDecides) => true,
            (Treatment::Unconsumed, Observed::Exact | Observed::Approximated(_)) => true,
            _ => false,
        };
        if !agrees {
            let walk = match &observed {
                Observed::Wrong(rows) => format!("read wrong rows:\n{rows}"),
                other => format!("{other:?}"),
            };
            failures.push(format!(
                "{channel:?}: inventory {:?}, walk {walk}",
                channel.treatment()
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Every reason the walk declines, and every approximation it names, is
/// some channel's treatment: none is reachable that the inventory does not
/// list.
#[test]
fn every_decline_and_approximation_is_a_channel() {
    let approximations: BTreeSet<Approximation> = Channel::ALL
        .iter()
        .filter_map(|c| match c.treatment() {
            Treatment::Approximated(a) => Some(a),
            _ => None,
        })
        .collect();
    for a in [
        Approximation::SignaturePair,
        Approximation::UncertainAttribute,
        Approximation::AbbreviationOrUnion,
        Approximation::AugmentationKind,
        Approximation::ModuleSuffix,
        Approximation::BindingPattern,
        Approximation::RejectedShape,
        Approximation::ClassLetName,
    ] {
        // An exhaustive match: a new approximation must be listed here.
        match a {
            Approximation::SignaturePair
            | Approximation::UncertainAttribute
            | Approximation::AbbreviationOrUnion
            | Approximation::AugmentationKind
            | Approximation::ModuleSuffix
            | Approximation::BindingPattern
            | Approximation::RejectedShape
            | Approximation::ClassLetName => {}
        }
        assert!(approximations.contains(&a), "{a:?} is no channel's");
    }
    let declines: Vec<(ExistenceUnread, Channel)> = vec![
        (
            ExistenceUnread::UnreadableItem(String::new()),
            Channel::UnreadableItem,
        ),
        (
            ExistenceUnread::FoldRefused(String::new()),
            Channel::FoldRefused,
        ),
        (
            ExistenceUnread::UnservedTfm(String::new()),
            Channel::UnservedTfm,
        ),
        (ExistenceUnread::Recovered(0), Channel::Recovered),
        (ExistenceUnread::HashReference(0), Channel::HashReference),
        (ExistenceUnread::TypeProvider(0), Channel::TypeProviderUse),
        (
            ExistenceUnread::UnreadableAutoOpen(0),
            Channel::AssemblyAutoOpenUnreadable,
        ),
        (
            ExistenceUnread::UnreadableCompiledName(0),
            Channel::UnreadableCompiledName,
        ),
        (
            ExistenceUnread::UnnamedDeclaration(0),
            Channel::UnnamedDeclaration,
        ),
        (
            ExistenceUnread::AnonymousModuleName(0),
            Channel::AnonymousModuleName,
        ),
        (ExistenceUnread::TooManyReadings, Channel::ReadingsBudget),
        (ExistenceUnread::LineDirective(0), Channel::LineDirective),
        (
            ExistenceUnread::OutsideDomain(0, Leaf::TypeHead),
            Channel::OutsideDomain,
        ),
    ];
    for (why, channel) in &declines {
        match why {
            ExistenceUnread::UnreadableItem(_)
            | ExistenceUnread::FoldRefused(_)
            | ExistenceUnread::UnservedTfm(_)
            | ExistenceUnread::Recovered(_)
            | ExistenceUnread::HashReference(_)
            | ExistenceUnread::TypeProvider(_)
            | ExistenceUnread::UnreadableAutoOpen(_)
            | ExistenceUnread::UnreadableCompiledName(_)
            | ExistenceUnread::UnnamedDeclaration(_)
            | ExistenceUnread::AnonymousModuleName(_)
            | ExistenceUnread::TooManyReadings
            | ExistenceUnread::LineDirective(_)
            | ExistenceUnread::OutsideDomain(..) => {}
        }
        assert_eq!(channel.treatment(), Treatment::Declined, "{why:?}");
        match witness(*channel) {
            Observed::Unread(seen) => assert_eq!(
                std::mem::discriminant(&seen),
                std::mem::discriminant(why),
                "{channel:?}'s witness declines for another reason"
            ),
            other => panic!("{channel:?}'s witness: {other:?}"),
        }
    }
}

/// A certificate that omits a written name reads that name as under
/// `Unknown`: it may denote any marker, and the walk says it approximated.
#[test]
fn an_omitted_name_widens_to_unknown() {
    let src = [(
        "Lib.fs",
        "namespace N\n[<AutoOpen>]\nmodule M =\n    let x = 1\n",
    )];
    let mut map = BTreeMap::new();
    map.insert(
        vec!["AutoOpen".to_owned()],
        BTreeSet::from([Marker::AutoOpen]),
    );
    let certified = read_with(&src, Some(MarkerRoutes::Certified(map)));
    let omitted = read_with(&src, Some(MarkerRoutes::Certified(BTreeMap::new())));
    let unknown = read_with(&src, Some(MarkerRoutes::Unknown));
    let flags = |r: &SourceExistence| -> BTreeSet<(bool, bool)> {
        rows(r, "flags")
            .iter()
            .filter(|row| row.logical_name == "M")
            .map(|row| (row.auto_open, row.extension))
            .collect()
    };
    assert_eq!(flags(&certified), BTreeSet::from([(true, false)]));
    assert_eq!(
        flags(&omitted),
        flags(&unknown),
        "an omitted name reads as Unknown"
    );
    // Every reading's facts: the attribute may be `[<AutoOpen>]` and
    // `[<Extension>]` both.
    assert_eq!(flags(&omitted), BTreeSet::from([(true, true)]));
    let SourceExistence::Read(s) = &omitted else {
        panic!("{omitted:?}")
    };
    assert!(
        s.approximations
            .contains(&Approximation::UncertainAttribute)
    );
    let SourceExistence::Read(s) = &certified else {
        panic!("{certified:?}")
    };
    assert!(s.approximations.is_empty(), "{:?}", s.approximations);
}

/// A name the certificate says denotes no marker is no marker, even spelled
/// as one: the shadow a reference may declare.
#[test]
fn a_certified_shadow_is_no_marker() {
    let src = [(
        "Lib.fs",
        "namespace N\n[<AutoOpen>]\nmodule M =\n    let x = 1\n",
    )];
    let mut map = BTreeMap::new();
    map.insert(vec!["AutoOpen".to_owned()], BTreeSet::new());
    let r = read_with(&src, Some(MarkerRoutes::Certified(map)));
    assert!(
        rows(&r, "shadow")
            .iter()
            .any(|row| row.logical_name == "M" && !row.auto_open),
        "{r:?}"
    );
}

/// A certificate that vouches for `[<Extension>]` but omits another
/// attribute of the same binding: the other may be `[<CompiledName>]`, so
/// the walk emits both names and says it approximated.
#[test]
fn a_partial_certificate_loses_exactness() {
    let src = [(
        "Lib.fs",
        "module M\n[<System.Runtime.CompilerServices.Extension; System.Obsolete(\"Old\")>]\nlet f (x: string) = x\n",
    )];
    let mut map = BTreeMap::new();
    map.insert(
        ["System", "Runtime", "CompilerServices", "Extension"]
            .map(str::to_owned)
            .to_vec(),
        BTreeSet::from([Marker::Extension]),
    );
    let r = read_with(&src, Some(MarkerRoutes::Certified(map)));
    let SourceExistence::Read(s) = &r else {
        panic!("{r:?}")
    };
    assert!(
        s.approximations
            .contains(&Approximation::UncertainAttribute),
        "{:?}",
        s.approximations
    );
    let names = extension_names(&r);
    assert!(names.contains(&vec!["f".to_owned()]), "{names:?}");
    assert!(
        names.contains(&vec!["Old".to_owned(), "f".to_owned()]),
        "{names:?}"
    );
}

/// A provider applied to a literal-bound identifier parses as an ordinary
/// type application: with a reference that may be a provider, the walk
/// cannot tell it from one and declines; with none, it is no provider.
#[test]
fn a_type_application_may_be_a_provider_only_where_a_reference_may_be_one() {
    let src = [(
        "Lib.fs",
        "namespace N\nmodule C =\n    [<Literal>]\n    let N = 2\ntype T = Gen<C.N>\ntype L = int list\n",
    )];
    // A bare name: FCS hands a provider an empty argument list.
    let bare = [(
        "Lib.fs",
        "namespace N\ntype T = Provider.Generated\ntype I = int\n",
    )];
    let bare_project = project(&bare);
    let bare_refs: Vec<&ProjectFile> = bare_project.iter().collect();
    let bare_routes = certify_by_spelling(&bare_refs);
    let bare_items: Vec<CompileItem<'_>> = bare_project.iter().map(CompileItem::Parsed).collect();
    assert!(
        matches!(
            source_existence(Producer::Evaluated {
                items: &bare_items,
                routes: &bare_routes,
                providers: ProviderReferences::Possible,
            }),
            SourceExistence::Unread(ExistenceUnread::TypeProvider(0))
        ),
        "a possible provider's bare type declines"
    );
    let project = project(&src);
    let refs: Vec<&ProjectFile> = project.iter().collect();
    let routes = certify_by_spelling(&refs);
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    let read = |providers| {
        source_existence(Producer::Evaluated {
            items: &items,
            routes: &routes,
            providers,
        })
    };
    assert!(
        matches!(
            read(ProviderReferences::Possible),
            SourceExistence::Unread(ExistenceUnread::TypeProvider(0))
        ),
        "a possible provider's application declines"
    );
    assert!(
        matches!(read(ProviderReferences::None), SourceExistence::Read(_)),
        "with no provider referenced, an application is a type"
    );
}
