//! The crate's whole surface, held to an exact list.
//!
//! The crate exists to have no reading of an incomplete answer as a complete
//! one, and such a reading can be added under any name: an `is_found`, an
//! `ok`, a derived `Default`, a trait impl. A `compile_fail` doctest catches
//! only the name it spells. So this test reads `src/lib.rs` and lists every
//! item in it: each type with its derives, each inherent method with its
//! visibility, each trait impl by its header, and any other item by kind.
//! The list must equal [`SURFACE`] exactly. Adding an operation means adding
//! its line here, together with its laws in `tests/laws.rs`.

use quote::ToTokens;

/// Every item of `src/lib.rs`, one per line, sorted.
const SURFACE: &str = "\
enum Lookup<T,C> pub derive(Clone,Copy,Debug,Eq,Hash,PartialEq)
enum Reading<C> private derive()
enum Verdict<T,C> pub derive(Clone,Copy,Debug,Eq,Hash,PartialEq)
impl<T,C,I:Iterator<Item=Verdict<T,C>>>IteratorforUntilUnknown<I,C>
impl<T,C,V:FromIterator<T>>FromIterator<Verdict<T,C>>forVerdict<V,C>
inherent Lookup<T,C> fn and_then pub
inherent Lookup<T,C> fn as_ref pub
inherent Lookup<T,C> fn into_verdict pub
inherent Lookup<T,C> fn map pub
inherent Lookup<T,C> fn map_cause pub
inherent Lookup<T,C> fn or_shadowed pub
inherent Verdict<Option<T>,C> fn into_lookup pub
inherent Verdict<T,C> fn and_then pub
inherent Verdict<T,C> fn as_ref pub
inherent Verdict<T,C> fn map pub
inherent Verdict<T,C> fn map_cause pub
inherent Verdict<T,C> fn zip pub
struct UntilUnknown<I,C> private
";

fn tokens(t: &impl ToTokens) -> String {
    t.to_token_stream().to_string().replace(' ', "")
}

fn visibility(v: &syn::Visibility) -> &'static str {
    match v {
        syn::Visibility::Public(_) => "pub",
        syn::Visibility::Restricted(_) => "restricted",
        syn::Visibility::Inherited => "private",
    }
}

fn derives(attrs: &[syn::Attribute]) -> String {
    let mut names = Vec::new();
    for attr in attrs.iter().filter(|a| a.path().is_ident("derive")) {
        attr.parse_nested_meta(|meta| {
            names.push(tokens(&meta.path));
            Ok(())
        })
        .expect("a derive list");
    }
    names.sort();
    format!("derive({})", names.join(","))
}

fn surface(source: &str) -> Vec<String> {
    let file = syn::parse_file(source).expect("src/lib.rs parses");
    let mut lines = Vec::new();
    for item in &file.items {
        match item {
            syn::Item::Enum(e) => lines.push(format!(
                "enum {}{} {} {}",
                e.ident,
                tokens(&e.generics),
                visibility(&e.vis),
                derives(&e.attrs)
            )),
            syn::Item::Struct(s) => {
                let derived = derives(&s.attrs);
                let derived = if derived == "derive()" {
                    String::new()
                } else {
                    format!(" {derived}")
                };
                lines.push(format!(
                    "struct {}{} {}{derived}",
                    s.ident,
                    tokens(&s.generics),
                    visibility(&s.vis)
                ))
            }
            syn::Item::Impl(i) if i.trait_.is_none() => {
                let owner = tokens(&i.self_ty);
                for member in &i.items {
                    match member {
                        syn::ImplItem::Fn(f) => lines.push(format!(
                            "inherent {owner} fn {} {}",
                            f.sig.ident,
                            visibility(&f.vis)
                        )),
                        other => lines.push(format!("inherent {owner} {}", tokens(other))),
                    }
                }
            }
            syn::Item::Impl(i) => {
                let mut header = i.clone();
                header.items.clear();
                header.attrs.clear();
                lines.push(tokens(&header).trim_end_matches("{}").to_string());
            }
            other => lines.push(format!("other {}", tokens(other))),
        }
    }
    lines.sort();
    lines
}

#[test]
fn the_surface_is_exactly_the_listed_operations() {
    let source = include_str!("../src/lib.rs");
    let actual = surface(source);
    let expected: Vec<String> = SURFACE.lines().map(str::to_string).collect();
    assert_eq!(
        actual, expected,
        "the crate's surface moved; every operation needs its laws in tests/laws.rs \
         and its line in SURFACE, and no reading as Option/bool/Default may be added"
    );
}

#[test]
fn the_listing_sees_what_would_break_the_contract() {
    // Each of these, appended to the crate, must move the listing: the test
    // above cannot pass with any of them present.
    let base = surface(include_str!("../src/lib.rs"));
    for addition in [
        "impl<T, C> Lookup<T, C> { pub fn is_found(&self) -> bool { true } }",
        "impl<T, C> Verdict<T, C> { pub fn ok(self) -> Option<T> { None } }",
        "impl<T, C> Default for Lookup<T, C> { fn default() -> Self { Lookup::ProvedAbsent } }",
        "impl<T, C> From<Option<T>> for Lookup<T, C> { fn from(_: Option<T>) -> Self { Lookup::ProvedAbsent } }",
        "impl<T, C> IntoIterator for Verdict<T, C> { type Item = T; type IntoIter = core::option::IntoIter<T>; fn into_iter(self) -> Self::IntoIter { None.into_iter() } }",
        "macro_rules! more { () => {} }",
        "pub fn found<T, C>(_: Lookup<T, C>) -> bool { true }",
    ] {
        let source = format!("{}\n{addition}\n", include_str!("../src/lib.rs"));
        assert_ne!(surface(&source), base, "{addition}");
    }
    // And a derive added to an existing type.
    let derived = include_str!("../src/lib.rs").replacen(
        "#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]\npub enum Lookup",
        "#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]\npub enum Lookup",
        1,
    );
    assert_ne!(
        derived,
        include_str!("../src/lib.rs"),
        "the derive was added"
    );
    assert_ne!(surface(&derived), base);
}
