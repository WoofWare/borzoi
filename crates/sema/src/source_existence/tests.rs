//! The walk's own cases, FCS-free: what each input channel declines or
//! approximates, what each form classifies, the module suffix, the input
//! bound, and what an incomplete certificate does.

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

/// Our reading of `files` under `routes` (or certified by spelling) and
/// `providers`, with the forms the walk classified.
fn read_full(
    files: &[(&str, &str)],
    routes: Option<MarkerRoutes>,
    providers: ProviderReferences,
) -> (SourceExistence, BTreeSet<Form>) {
    let project = project(files);
    let refs: Vec<&ProjectFile> = project.iter().collect();
    let routes = routes.unwrap_or_else(|| certify_by_spelling(&refs));
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    super::read(Producer::Evaluated {
        items: &items,
        routes: &routes,
        providers,
        output: BuiltOutput::Absent,
    })
}

fn read_with(files: &[(&str, &str)], routes: Option<MarkerRoutes>) -> SourceExistence {
    read_full(files, routes, ProviderReferences::None).0
}

fn read(files: &[(&str, &str)]) -> SourceExistence {
    read_with(files, None)
}

/// The rows of a `Read`, or a panic naming `what`.
fn rows(r: &SourceExistence, what: &str) -> Vec<PickledEntityRow> {
    match r {
        SourceExistence::Read(s) => s.entities.clone(),
        SourceExistence::Unread(why) => panic!("{what}: unread {why:?}"),
    }
}

fn has_entity(r: &SourceExistence, logical: &str, compiled: &str, kind: PickledEntityKind) -> bool {
    matches!(r, SourceExistence::Read(_))
        && rows(r, logical).iter().any(|row| {
            row.logical_name == logical && row.compiled_name == compiled && row.kind == kind
        })
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
        SourceExistence::Read(s) => Observed::Wrong(format!("{:#?}", s.entities)),
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
                    output: BuiltOutput::Absent,
                }),
                |_| true,
            )
        }
        Channel::FoldRefused => observe(source_existence(Producer::FoldRefused("why")), |_| true),
        // A stale build's module and auto-open, which the source lacks, are
        // in the surface beside the source's own.
        Channel::BuiltOutput => {
            let project = project(&[("A.fs", "module A\nlet x = 1\n")]);
            let routes = MarkerRoutes::Certified(BTreeMap::new());
            let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
            let stale = PickledEntityRow {
                namespace: Vec::new(),
                enclosing: Vec::new(),
                logical_name: "Stale".to_owned(),
                compiled_name: "Stale".to_owned(),
                kind: K::Module,
                public: true,
                auto_open: false,
                extension: false,
            };
            let index = ExistenceIndex {
                il: Vec::new(),
                pickle: PickleLayer::Read(vec![stale.clone()]),
                extensions: Vec::new(),
            };
            let auto_opens = ["Stale".to_owned()];
            let r = source_existence(Producer::Evaluated {
                items: &items,
                routes: &routes,
                providers: ProviderReferences::None,
                output: BuiltOutput::Read {
                    index: &index,
                    assembly_auto_opens: &auto_opens,
                },
            });
            let holds = |r: &SourceExistence| match r {
                SourceExistence::Read(s) => {
                    matches!(s.index().pickle, PickleLayer::Read(rows)
                        if rows.contains(&stale) && rows.iter().any(|row| row.logical_name == "A"))
                        && s.assembly_auto_opens == ["Stale"]
                }
                SourceExistence::Unread(_) => false,
            };
            if holds(&r) {
                observe(r, |_| true)
            } else {
                Observed::Wrong(format!("{r:?}"))
            }
        }
        Channel::UnreadableBuiltOutput => {
            let project = project(&[("A.fs", "module A\nlet x = 1\n")]);
            let routes = MarkerRoutes::Certified(BTreeMap::new());
            let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
            observe(
                source_existence(Producer::Evaluated {
                    items: &items,
                    routes: &routes,
                    providers: ProviderReferences::None,
                    output: BuiltOutput::Unreadable,
                }),
                |_| true,
            )
        }
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
                    output: BuiltOutput::Absent,
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
        // `FooModule` may be `FooModuleModule`: both readings.
        Channel::ModuleSuffix => observe(
            one("namespace N\nmodule FooModule =\n    let x = 1\n"),
            |_| true,
        ),
        Channel::TypeDefinition => observe(
            one("namespace N\ntype C() = member _.X = 1\ntype U = A | B\n"),
            |r| has_entity(r, "C", "C", K::Type) && has_entity(r, "U", "U", K::Type),
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
        Channel::CompiledNameAttribute => observe(
            one("namespace N\n[<CompiledName(\"R\")>]\ntype T() = class end\n"),
            |r| has_entity(r, "T", "R", K::Type),
        ),
        // An entity keeps every attribute of its lists, whatever its target.
        Channel::AttributeTarget => observe(
            one("namespace N\n[<return: AutoOpen>]\nmodule M =\n    let x = 1\n"),
            |r| {
                rows(r, "target")
                    .iter()
                    .any(|row| row.logical_name == "M" && row.auto_open)
            },
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
        // A target FCS does not know: a child no classifier reads.
        Channel::Unreadable => observe(
            one("namespace N\n[<bogus: AutoOpen>]\nmodule M =\n    let x = 1\n"),
            |_| true,
        ),
        Channel::InputBound => observe(
            one(&format!(
                "namespace N\ntype {} = int\n",
                "T".repeat(MAX_NAME_BYTES + 1)
            )),
            |_| true,
        ),
        // An extension member of any shape adds no row and no flag.
        Channel::ExtensionMembers => observe(
            one(
                "namespace Ns\nopen System.Runtime.CompilerServices\n[<Extension>]\ntype E =\n    [<Extension>]\n    static member M(s: string) = s\ntype System.Collections.Generic.List<'T> with\n    member l.N = 1\n",
            ),
            |r| {
                rows(r, "extension")
                    .iter()
                    .all(|row| !row.extension && row.logical_name != "N")
            },
        ),
    }
}

/// Every channel's witness does what the inventory says the walk does with
/// it.
#[test]
fn the_inventory_is_what_the_walk_does() {
    let mut failures = Vec::new();
    for &channel in Channel::ALL {
        let observed = witness(channel);
        let agrees = match (channel.treatment(), &observed) {
            (Treatment::Modelled | Treatment::ExtensionNames, Observed::Exact) => true,
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
        Approximation::ModuleSuffix,
        Approximation::BuiltOutput,
    ] {
        // An exhaustive match: a new approximation must be listed here.
        match a {
            Approximation::SignaturePair
            | Approximation::UncertainAttribute
            | Approximation::AbbreviationOrUnion
            | Approximation::ModuleSuffix
            | Approximation::BuiltOutput => {}
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
            ExistenceUnread::AnonymousModuleName(0),
            Channel::AnonymousModuleName,
        ),
        (ExistenceUnread::TooManyReadings, Channel::InputBound),
        (
            ExistenceUnread::Unreadable(0, Leaf::Attribute),
            Channel::Unreadable,
        ),
        (
            ExistenceUnread::UnreadableOutput,
            Channel::UnreadableBuiltOutput,
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
            | ExistenceUnread::AnonymousModuleName(_)
            | ExistenceUnread::TooManyReadings
            | ExistenceUnread::Unreadable(..)
            | ExistenceUnread::UnreadableOutput => {}
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

/// Every form's witness is classified as that form, and the walk reads or
/// declines it as the form's verdict says: the FCS-free half of
/// `source_existence_domain`.
#[test]
fn every_form_witness_is_classified_as_its_form() {
    let mut failures = Vec::new();
    for &form in Form::ALL {
        let (r, forms) = read_full(
            &[("Lib.fs", form.witness())],
            None,
            ProviderReferences::None,
        );
        if !forms.contains(&form) {
            failures.push(format!("{form:?}: its witness classifies {forms:?}"));
        }
        let read = matches!(r, SourceExistence::Read(_));
        if read != (form.verdict() == Verdict::Read) {
            failures.push(format!(
                "{form:?}: verdict {:?}, walk {r:?}",
                form.verdict()
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
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
    let flags = |r: &SourceExistence| -> BTreeSet<bool> {
        rows(r, "flags")
            .iter()
            .filter(|row| row.logical_name == "M")
            .map(|row| row.auto_open)
            .collect()
    };
    assert_eq!(flags(&certified), BTreeSet::from([true]));
    assert_eq!(
        flags(&omitted),
        flags(&unknown),
        "an omitted name reads as Unknown"
    );
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

/// A named type in an abbreviation's target may be a generative provider's
/// only where a reference may be one: with one, the walk cannot tell it from
/// one and declines; with none, it is no provider.
#[test]
fn a_named_target_may_be_a_provider_only_where_a_reference_may_be_one() {
    let src = [(
        "Lib.fs",
        "namespace N\nmodule C =\n    [<Literal>]\n    let N = 2\ntype T = Gen<C.N>\ntype L = int list\n",
    )];
    let (possible, _) = read_full(&src, None, ProviderReferences::Possible);
    assert!(
        matches!(
            possible,
            SourceExistence::Unread(ExistenceUnread::TypeProvider(0))
        ),
        "{possible:?}"
    );
    let (none, _) = read_full(&src, None, ProviderReferences::None);
    assert!(matches!(none, SourceExistence::Read(_)), "{none:?}");
    // A bare name: FCS hands a provider an empty argument list.
    let bare = [(
        "Lib.fs",
        "namespace N\ntype T = Provider.Generated\ntype I = int * int\n",
    )];
    let (bare_possible, _) = read_full(&bare, None, ProviderReferences::Possible);
    assert!(
        matches!(
            bare_possible,
            SourceExistence::Unread(ExistenceUnread::TypeProvider(0))
        ),
        "{bare_possible:?}"
    );
    // A structural target is no provider's.
    let structural = [("Lib.fs", "namespace N\ntype I = int * int\n")];
    let (r, _) = read_full(&structural, None, ProviderReferences::Possible);
    assert!(matches!(r, SourceExistence::Read(_)), "{r:?}");
}

/// A module whose name ends in `Module` has both readings, the written
/// name and the suffixed one FCS may give it, whatever its attributes and
/// neighbours, its contents under each; a module whose name does not end in
/// `Module` has one, since canonical spelling strips the suffix. A path
/// holding two such modules declines, so nothing is walked more than twice.
#[test]
fn a_module_ending_in_module_has_both_readings() {
    use PickledEntityKind as K;
    let attr = "[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]";
    for (routes, src) in [
        (
            None,
            format!("namespace N\n{attr}\nmodule FooModule =\n    type T = int\n"),
        ),
        (
            None,
            "namespace N\nmodule FooModule =\n    type T = int\n".to_owned(),
        ),
        (
            None,
            "namespace N\ntype FooModule = int\nmodule FooModule =\n    type T = int\n".to_owned(),
        ),
        (
            Some(MarkerRoutes::Unknown),
            format!("namespace N\n{attr}\nmodule FooModule =\n    type T = int\n"),
        ),
        (None, "module N.FooModule\ntype T = int\n".to_owned()),
    ] {
        let r = read_with(&[("Lib.fs", &src)], routes);
        let SourceExistence::Read(surface) = &r else {
            panic!("{src}: {r:?}")
        };
        assert!(
            surface
                .approximations
                .contains(&Approximation::ModuleSuffix),
            "{src}"
        );
        for reading in ["FooModule", "FooModuleModule"] {
            assert!(
                has_entity(&r, reading, reading, K::Module),
                "{src}: {reading}"
            );
            assert!(
                rows(&r, reading).iter().any(|row| row.logical_name == "T"
                    && row.enclosing.last().map(String::as_str) == Some(reading)),
                "{src}: `T` under {reading}"
            );
        }
    }
    let r = read(&[("Lib.fs", "namespace N\nmodule Foo =\n    type T = int\n")]);
    let SourceExistence::Read(surface) = &r else {
        panic!("{r:?}")
    };
    assert!(
        !surface
            .approximations
            .contains(&Approximation::ModuleSuffix)
    );
    assert!(!has_entity(&r, "FooModule", "FooModule", K::Module));
    // Two on one path.
    let r = read(&[(
        "Lib.fs",
        "namespace N\nmodule OuterModule =\n    module InnerModule =\n        type T = int\n",
    )]);
    assert!(
        matches!(r, SourceExistence::Unread(ExistenceUnread::TooManyReadings)),
        "{r:?}"
    );
}

/// Past each bound of the input the walk declines before it walks; at the
/// bound it reads.
#[test]
fn the_input_bound_declines_past_each_limit() {
    let bound = |r: &SourceExistence| {
        matches!(r, SourceExistence::Unread(ExistenceUnread::TooManyReadings))
    };
    // A name.
    let at = read(&[(
        "Lib.fs",
        &format!("namespace N\ntype {} = int\n", "T".repeat(MAX_NAME_BYTES)),
    )]);
    assert!(matches!(at, SourceExistence::Read(_)), "{at:?}");
    let past = read(&[(
        "Lib.fs",
        &format!(
            "namespace N\ntype {} = int\n",
            "T".repeat(MAX_NAME_BYTES + 1)
        ),
    )]);
    assert!(bound(&past), "{past:?}");
    // The depth: namespace segments, then nested modules.
    let nested = |depth: usize| {
        let mut src = String::from("namespace N\n");
        for d in 0..depth {
            src.push_str(&format!("{}module M{d} =\n", "    ".repeat(d)));
        }
        src.push_str(&format!("{}let x = 1\n", "    ".repeat(depth)));
        read(&[("Lib.fs", &src)])
    };
    assert!(matches!(nested(MAX_DEPTH - 1), SourceExistence::Read(_)));
    assert!(bound(&nested(MAX_DEPTH)), "{:?}", nested(MAX_DEPTH));
    // The declarations.
    let many = |n: usize| {
        let mut src = String::from("namespace N\n");
        for k in 0..n {
            src.push_str(&format!("type T{k} = int\n"));
        }
        read(&[("Lib.fs", &src)])
    };
    assert!(matches!(
        many(MAX_DECLARATIONS - 1),
        SourceExistence::Read(_)
    ));
    assert!(bound(&many(MAX_DECLARATIONS)), "past the declarations");
    // A literal that may become a compiled name, or an assembly auto-open
    // path, is a name.
    for src in [
        format!(
            "namespace N\n[<CompiledName(\"{}\")>]\ntype T = int\n",
            "R".repeat(MAX_NAME_BYTES + 1)
        ),
        format!(
            "namespace N\n[<assembly: AutoOpen(\"{}\")>]\ndo ()\n",
            "R".repeat(MAX_NAME_BYTES + 1)
        ),
    ] {
        let r = read(&[("Lib.fs", &src)]);
        assert!(bound(&r), "a long literal: {r:?}");
    }
    // A headerless file's implicit module path, from its name, is a path.
    let name: String = (0..=MAX_DEPTH)
        .map(|k| format!("P{k}."))
        .collect::<String>()
        + "fs";
    let r = read(&[(name.as_str(), "let x = 1\n")]);
    assert!(bound(&r), "a deep implicit module path: {r:?}");
}

/// A child no classifier names declines with its leaf: an attribute target
/// FCS does not know.
#[test]
fn an_unconsumed_child_declines_with_its_leaf() {
    let r = read(&[(
        "Lib.fs",
        "namespace N\n[<bogus: AutoOpen>]\nmodule M =\n    let x = 1\n",
    )]);
    assert!(
        matches!(
            r,
            SourceExistence::Unread(ExistenceUnread::Unreadable(0, Leaf::Attribute))
        ),
        "{r:?}"
    );
    // A token the header's classifier does not name: a top-level `let … in`.
    let r = read(&[("Lib.fs", "module M\nlet f x = x in\nf 1 |> ignore\n")]);
    assert!(
        matches!(
            r,
            SourceExistence::Unread(ExistenceUnread::Unreadable(0, Leaf::FileHeader))
        ),
        "{r:?}"
    );
}
