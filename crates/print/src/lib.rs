//! An owned F# syntax tree that a program builds, and a reference printer that
//! writes it as F# source.
//!
//! This is the output half of source generation. `borzoi-cst`'s tree is
//! lossless and comes only from parsing, so it is not something a generator can
//! build; [`tree`] is. [`print_impl_file`] is the *reference* printer: verbose,
//! fully parenthesised and one line per expression, so that it is easy to see
//! it is right, and every tree prints as source F# parses back to that tree.
//!
//! A tree's types say which F# language version it targets ([`version`]): an
//! `ImplFile<V7_0>` cannot hold a construct F# 7 lacks, and prints as source
//! that F# 7 and every later version parse back to that tree.
//!
//! The crate depends only on `borzoi-cst`, for its [`LanguageVersion`] and
//! feature table. Its correctness oracle lives in
//! `borzoi-cst`'s tests (`tests/all/print_roundtrip/`), which have the
//! FCS-graded parser differential to hand: for every generated tree, and every
//! tree read off a corpus file, the printed text must parse cleanly under both
//! FCS and `borzoi-cst` at the tree's version and at `preview`, the parses must
//! agree, and the parse must read back as the tree that was printed. Below a
//! gate's version, FCS must reject the construct the gate admits.
//!
//! What "parses back to that tree" covers is the parse, not type checking.
//! Where F#'s checker reads syntax more finely than the parse tree records,
//! the tree models the finer reading. An argument list is one: `M(a, b)`
//! passes two arguments where `M((a, b))` passes one tuple, and `M(x = 1)`
//! names an argument where `M((x = 1))` passes a `bool`, so the tree tells an
//! [`tree::Expr::App`] to one value from an [`tree::Expr::MethodApp`] to an
//! argument list, and the printer writes each in the parentheses that keep it
//! so.

pub mod names;
mod print;
pub mod tree;
pub mod vec;
pub mod version;

pub use print::print_impl_file;
pub use version::LanguageVersion;
