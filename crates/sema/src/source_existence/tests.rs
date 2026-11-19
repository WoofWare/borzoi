//! The walk's own cases, FCS-free: what each input channel declines or
//! approximates, and what an incomplete certificate does.

use super::*;
use crate::qnof::qualified_names;
use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_cst::syntax::{ImplFile, SigFile};
use std::path::PathBuf;

/// The project of `files` (name, text), parsed with no defines.
fn project(files: &[(&str, &str)]) -> Vec<ProjectFile> {
    let symbols = Default::default();
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

/// Our reading of `files` under `routes`, or certified by spelling.
fn read_with(files: &[(&str, &str)], routes: Option<MarkerRoutes>) -> SourceExistence {
    let project = project(files);
    let refs: Vec<&ProjectFile> = project.iter().collect();
    let routes = routes.unwrap_or_else(|| certify_by_spelling(&refs));
    let items: Vec<CompileItem<'_>> = project.iter().map(CompileItem::Parsed).collect();
    source_existence(Producer::Evaluated {
        items: &items,
        routes: &routes,
    })
}

fn read(files: &[(&str, &str)]) -> SourceExistence {
    read_with(files, None)
}

#[test]
fn probe_names() {
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
