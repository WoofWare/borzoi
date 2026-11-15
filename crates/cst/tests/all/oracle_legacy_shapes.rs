//! The legacy oracle's records, upgraded (`common::oracle::upgrade_legacy_record`),
//! read as the current oracle's do.
//!
//! Both oracles parse at 9.0, where the two compilers agree on every fixture
//! here: they differ in the ungated lexing and recovery the current compiler
//! changed, which these fixtures avoid, and in how they write the AST, which
//! is what the upgrade rewrites. So the FCS projection must read the two
//! records alike, fixture by fixture. Each rewrite the upgrade makes is
//! exercised by at least one fixture, and the interpolated strings check the
//! projection's inverse of the current compiler's alignment and printf split
//! against the legacy compiler, which never split them.

use std::io::Write;

use tempfile::NamedTempFile;

use crate::common::{Oracle, normalised_ast};

/// Implementation files, one per rewritten shape (and their combinations).
const IMPL: &[&str] = &[
    // `SynComponentInfo`: type, module and nested-module heads, dotted.
    "module M\ntype T = int\n",
    "namespace A.B\nmodule C =\n    type D<'a> = 'a list\n    module E = begin end\n",
    "module M\ntype R = { A: int; mutable B: string }\nand U = | X | Y of R\n",
    "module M\nexception E of int\ntype C() =\n    member _.M = 1\n",
    "module M\n[<AutoOpen>]\nmodule internal N =\n    let x = 1\n",
    "module M\ntype T with\n    member _.M = 1\n",
    // Record expressions, copy-and-update, and anonymous records.
    "module M\nlet r = { A = 1; B = \"x\" }\nlet s = { r with A = 2 }\n",
    "module M\nlet r = { A = 1\n          B = 2 }\nlet n = { r with A.B = 3 }\n",
    "module M\nlet a = {| X = 1; Y = 2 |}\nlet b = {| a with X = 3 |}\nlet c = struct {| Z = 0 |}\n",
    // Interpolated-string holes: plain, `.NET` format, alignment, both, printf.
    "module M\nlet s = $\"a{x}b{y:N2}c\"\n",
    "module M\nlet s = $\"a{x,5}b{y,-3:N2}c\"\n",
    "module M\nlet s = $\"a%d{x}b%5.2f{y}c%%{z}\"\n",
    "module M\nlet s = $\"%s{x}\"\nlet t = $\"\"\"%d{x} {y}\"\"\"\nlet u = $@\"{x,2}\"\n",
    "module M\nlet s = $\"{x, y, 5}{(x, 5)}\"\n",
];

/// Signature files.
const SIG: &[&str] = &[
    "namespace N\ntype T = { A: int }\nmodule M =\n    val x: int\n",
    "module M\ntype U =\n    | A\n    | B of int\nexception E of string\n",
];

fn assert_alike(source: &str, suffix: &str) {
    let mut tmp = NamedTempFile::with_suffix(suffix).expect("create tempfile");
    tmp.write_all(source.as_bytes()).expect("write source");
    let current = Oracle::Current.ast_at(tmp.path(), "9.0");
    let legacy = Oracle::Legacy.ast_at(tmp.path(), "9.0");
    assert_eq!(
        normalised_ast::normalise_fcs_dump(&legacy),
        normalised_ast::normalise_fcs_dump(&current),
        "the oracles' records project differently for {source:?}",
    );
}

#[test]
fn legacy_impl_records_upgrade_to_the_current_shapes() {
    for source in IMPL {
        assert_alike(source, ".fs");
    }
}

#[test]
fn legacy_sig_records_upgrade_to_the_current_shapes() {
    for source in SIG {
        assert_alike(source, ".fsi");
    }
}
