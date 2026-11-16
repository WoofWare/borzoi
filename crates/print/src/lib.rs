//! An owned F# syntax tree that a program builds, and a reference printer that
//! writes it as F# source.
//!
//! This is the output half of source generation. `borzoi-cst`'s tree is
//! lossless and comes only from parsing, so it is not something a generator can
//! build; [`tree`] is. [`print_impl_file`] is the *reference* printer: verbose,
//! fully parenthesised and one line per expression, so that it is easy to see
//! it is right, and every tree prints as source F# parses back to that tree.
//!
//! The crate has no dependencies. Its correctness oracle lives in
//! `borzoi-cst`'s tests (`tests/all/print_roundtrip/`), which have the
//! FCS-graded parser differential to hand: for every generated tree, and every
//! tree read off a corpus file, the printed text must parse cleanly under both
//! FCS and `borzoi-cst`, the two parses must agree, and the parse must read back
//! as the tree that was printed.
//!
//! What "parses back to that tree" covers is the parse, not type checking.
//! F#'s checker reads some syntax more finely than the parse tree records:
//! `M(x = 1)` passes a named argument where `M((x = 1))` passes a `bool`. The
//! printer parenthesises every expression, names included, so it always means
//! the plain reading (`(x) = (1)` is never a named argument), but a construct
//! whose meaning rests on such syntax cannot be built from this tree yet.

pub mod names;
mod print;
pub mod tree;
pub mod vec;

pub use print::print_impl_file;
