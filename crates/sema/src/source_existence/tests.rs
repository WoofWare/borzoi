use std::path::PathBuf;

use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_cst::syntax::{ImplFile, SigFile};

use super::*;
use crate::qnof::qualified_names;

/// `files` (name and text, in Compile order) as Compile items, parsed with
/// `COMPILED` defined.
fn project(files: &[(&str, &str)]) -> Vec<ProjectFile> {
    let symbols = ["COMPILED".to_owned()].into_iter().collect();
    let mut parsed = Vec::new();
    let mut recoveries = Vec::new();
    for (name, text) in files {
        let kind = if name.ends_with(".fsi") {
            FileKind::Sig
        } else {
            FileKind::Impl
        };
        let parse = parse_with_options(
            text,
            ParseOptions {
                file_kind: kind,
                symbols: &symbols,
                lang: borzoi_cst::language_version::LanguageVersion::V10_0,
            },
        );
        recoveries.push(SyntaxRecovery::of(&parse));
        parsed.push(match kind {
            FileKind::Sig => SourceFile::Sig(SigFile::cast(parse.root).expect("a signature root")),
            FileKind::Impl => {
                SourceFile::Impl(ImplFile::cast(parse.root).expect("an implementation root"))
            }
        });
    }
    let paths: Vec<PathBuf> = files
        .iter()
        .map(|(n, _)| PathBuf::from("/fixture").join(n))
        .collect();
    let names = qualified_names(&parsed, &paths);
    parsed
        .into_iter()
        .zip(names)
        .zip(recoveries)
        .map(|((f, q), r)| ProjectFile::new(f, q, r))
        .collect()
}

fn walk(files: &[(&str, &str)], budget: Budget) -> (SourceExistence, BTreeSet<Form>) {
    let project = project(files);
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    read(
        Producer {
            items: &items,
            providers: ProviderReferences::None,
        },
        budget,
    )
}

/// A form's witness as Compile items: a signature and its implementation
/// for `SignatureFile`, one implementation file otherwise.
fn witness_files(form: Form) -> Vec<(&'static str, &'static str)> {
    match form.witness().split_once("//--\n") {
        Some((sig, imp)) => vec![("Lib.fsi", sig), ("Lib.fs", imp)],
        None => vec![("Lib.fs", form.witness())],
    }
}

/// Every form's witness is classified into the form, and is read or declines
/// as its verdict says, a declined one with its own form as the reason.
#[test]
fn every_witness_is_its_form() {
    let mut wrong = Vec::new();
    for &form in Form::ALL {
        let (read, forms) = walk(&witness_files(form), Budget::DEFAULT);
        if !forms.contains(&form) {
            wrong.push(format!("{form:?}: not classified, {forms:?}"));
        }
        let kept = match (form.verdict(), &read) {
            (Verdict::Read, SourceExistence::Read(_)) => true,
            (Verdict::Declined, SourceExistence::Unread(ExistenceUnread::Declined(_, f))) => {
                *f == form
            }
            _ => false,
        };
        if !kept {
            wrong.push(format!("{form:?}: {:?} gave {read:?}", form.verdict()));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Each entity carrier of an attribute list declines as an entity's, and
/// each other carrier the walk names reads, with no row of its own.
#[test]
fn attribute_carriers_are_classified() {
    let entity = [
        "module D\n[<A>]\nmodule M =\n    let x = 1\n",
        "[<A>]\nmodule D.M\nlet x = 1\n",
        "module D\n[<A>]\ntype T = { X: int }\n",
        "module D\ntype T = { X: int }\nand [<A>] U = { Y: int }\n",
        "module D\n[<A>]\nexception E of string\n",
    ];
    for src in entity {
        let (read, _) = walk(&[("Lib.fs", src)], Budget::DEFAULT);
        assert!(
            matches!(
                read,
                SourceExistence::Unread(ExistenceUnread::Declined(0, Form::EntityAttribute))
            ),
            "{src:?}: {read:?}"
        );
    }
    let other = [
        "module D\n[<A>]\nlet x = 1\n",
        "module D\nlet [<A>] x = 1\n",
        "module D\ntype T() =\n    [<A>]\n    member _.M = 1\n",
        "module D\ntype R = { [<A>] X: int }\n",
        "module D\ntype U = | [<A>] C of int\n",
        "module D\nlet f ([<A>] x: int) = x\n",
        "module D\ntype T() =\n    [<A>]\n    let x = 1\n    member _.M = x\n",
        "module D\ntype T<[<A>] 'a> = { X: 'a }\n",
        "module D\ntype E = | [<A>] X = 1\n",
        "module D\ntype T [<A>] (x: int) =\n    member _.X = x\n",
        "module D\ntype T() =\n    [<A>]\n    val mutable x: int\n",
        "module D\ntype T() =\n    member _.P with [<A>] get () = 1\n",
    ];
    for src in other {
        let (read, forms) = walk(&[("Lib.fs", src)], Budget::DEFAULT);
        assert!(
            matches!(read, SourceExistence::Read(_)) && forms.contains(&Form::OtherAttribute),
            "{src:?}: {read:?} {forms:?}"
        );
    }
}

/// The rows of a small producer: every namespace prefix, every module, type
/// and exception, and nothing for an augmentation, a `let` or an open.
#[test]
fn the_rows_are_the_declarations() {
    let src = "namespace A.B\nopen System\ntype T = { X: int }\ntype T with\n    member t.Y = 1\nmodule M =\n    let x = 1\n    exception E of string\n    module N = begin end\n";
    let (read, _) = walk(&[("Lib.fs", src)], Budget::DEFAULT);
    let SourceExistence::Read(surface) = read else {
        panic!("{read:?}");
    };
    let rows: Vec<String> = surface
        .entities
        .iter()
        .map(|r| {
            format!(
                "{:?} {}|{}|{}",
                r.kind,
                r.namespace.join("."),
                r.enclosing.join("."),
                r.logical_name
            )
        })
        .collect();
    let mut expected = vec![
        "Namespace ||A".to_owned(),
        "Namespace A||B".to_owned(),
        "Type A.B||T".to_owned(),
        "Module A.B||M".to_owned(),
        "Exception A.B|M|E".to_owned(),
        "Module A.B|M|N".to_owned(),
    ];
    let mut rows = rows;
    rows.sort();
    expected.sort();
    assert_eq!(rows, expected);
}

/// A recovered file, an unreadable item and a signature file each decline A
/// whatever the other items hold.
#[test]
fn an_unreadable_or_recovered_item_declines() {
    let (read, _) = walk(&[("Lib.fs", "module D\nlet x = \n")], Budget::DEFAULT);
    assert_eq!(read, SourceExistence::Unread(ExistenceUnread::Recovered(0)));
    let project = project(&[("Lib.fs", "module D\nlet x = 1\n")]);
    let items = [
        CompileItem::Parsed(&project[0]),
        CompileItem::Unreadable("/fixture/Gone.fs"),
    ];
    let read = source_existence(
        Producer {
            items: &items,
            providers: ProviderReferences::None,
        },
        Budget::DEFAULT,
    );
    assert_eq!(
        read,
        SourceExistence::Unread(ExistenceUnread::UnreadableItem(
            "/fixture/Gone.fs".to_owned()
        ))
    );
}

/// An FSharp.Core-name target declines when a reference may be a type
/// provider, which may supply a type of that name.
#[test]
fn a_possible_provider_declines_a_named_target() {
    let project = project(&[("Lib.fs", "module D\ntype A = int\n")]);
    let items = [CompileItem::Parsed(&project[0])];
    let read = source_existence(
        Producer {
            items: &items,
            providers: ProviderReferences::Possible,
        },
        Budget::DEFAULT,
    );
    assert_eq!(
        read,
        SourceExistence::Unread(ExistenceUnread::TypeProvider(0))
    );
}
