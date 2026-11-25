//! The crate's whole surface, held to an exact list.
//!
//! The crate exists to have no reading of an incomplete answer as a complete
//! one, and such a reading can be added under any name, or on any platform: an
//! `is_found`, an `ok`, a derived `Default`, one derived only under a
//! `cfg_attr`, a trait impl. A `compile_fail` doctest catches only the name it
//! spells, on the platform it runs on. So this test reads `src/lib.rs` and
//! lists every item in it:
//!
//! - each type, with every attribute on it but its docs, and each variant
//!   with its fields and attributes;
//! - each inherent method, with its visibility and attributes;
//! - each trait impl, by its header and attributes;
//! - the crate's inner attributes;
//! - any other item, by kind and text.
//!
//! A plain `derive` is listed by its sorted names, so reordering one moves
//! nothing; every other attribute (`cfg`, `cfg_attr`, `default`, …) is listed
//! as written, so adding one moves the listing. The list must equal
//! [`SURFACE`] exactly. Adding an operation means adding its line here,
//! together with its laws in `tests/laws.rs`.

use quote::ToTokens;

/// Every item of `src/lib.rs`, one per line, sorted.
const SURFACE: &str = "\
crate #![forbid(unsafe_code)]
crate #![no_std]
enum Lookup<T,C> pub derive(Clone,Copy,Debug,Eq,Hash,PartialEq)
enum Lookup<T,C> variant Found(T)
enum Lookup<T,C> variant ProvedAbsent
enum Lookup<T,C> variant Unknown(C)
enum Reading<C> private derive()
enum Reading<C> variant Ended
enum Reading<C> variant Unknown(C)
enum Reading<C> variant Values
enum Verdict<T,C> pub derive(Clone,Copy,Debug,Eq,Hash,PartialEq)
enum Verdict<T,C> variant Certain(T)
enum Verdict<T,C> variant Unknown(C)
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
struct UntilUnknown<I,C> private derive()
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

/// The attributes, docs aside: a plain `derive` by its sorted names, every
/// other attribute as written, in order.
fn attributes(attrs: &[syn::Attribute]) -> String {
    let mut derived = Vec::new();
    let mut others = Vec::new();
    for attr in attrs {
        if attr.path().is_ident("doc") {
            continue;
        }
        if attr.path().is_ident("derive") {
            attr.parse_nested_meta(|meta| {
                derived.push(tokens(&meta.path));
                Ok(())
            })
            .expect("a derive list");
        } else {
            others.push(tokens(attr));
        }
    }
    derived.sort();
    let mut listed = format!("derive({})", derived.join(","));
    for other in others {
        listed.push(' ');
        listed.push_str(&other);
    }
    listed
}

/// The attributes other than docs, as written, prefixed by a space; empty
/// when there are none.
fn other_attributes(attrs: &[syn::Attribute]) -> String {
    attrs
        .iter()
        .filter(|a| !a.path().is_ident("doc"))
        .map(|a| format!(" {}", tokens(a)))
        .collect()
}

fn surface(source: &str) -> Vec<String> {
    let file = syn::parse_file(source).expect("the source parses");
    let mut lines: Vec<String> = file
        .attrs
        .iter()
        .filter(|a| !a.path().is_ident("doc"))
        .map(|a| format!("crate {}", tokens(a)))
        .collect();
    for item in &file.items {
        match item {
            syn::Item::Enum(e) => {
                let owner = format!("{}{}", e.ident, tokens(&e.generics));
                lines.push(format!(
                    "enum {owner} {} {}",
                    visibility(&e.vis),
                    attributes(&e.attrs)
                ));
                for variant in &e.variants {
                    lines.push(format!(
                        "enum {owner} variant {}{}{}",
                        variant.ident,
                        tokens(&variant.fields),
                        other_attributes(&variant.attrs)
                    ));
                }
            }
            syn::Item::Struct(s) => lines.push(format!(
                "struct {}{} {} {}",
                s.ident,
                tokens(&s.generics),
                visibility(&s.vis),
                attributes(&s.attrs)
            )),
            syn::Item::Impl(i) if i.trait_.is_none() => {
                let owner = format!("{}{}", tokens(&i.self_ty), other_attributes(&i.attrs));
                for member in &i.items {
                    match member {
                        syn::ImplItem::Fn(f) => lines.push(format!(
                            "inherent {owner} fn {} {}{}",
                            f.sig.ident,
                            visibility(&f.vis),
                            other_attributes(&f.attrs)
                        )),
                        other => lines.push(format!("inherent {owner} {}", tokens(other))),
                    }
                }
            }
            syn::Item::Impl(i) => {
                let mut header = i.clone();
                header.items.clear();
                header.attrs.retain(|a| !a.path().is_ident("doc"));
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
    let actual = surface(include_str!("../src/lib.rs"));
    let expected: Vec<String> = SURFACE.lines().map(str::to_string).collect();
    assert_eq!(
        actual, expected,
        "the crate's surface moved; every operation needs its laws in tests/laws.rs \
         and its line in SURFACE, and no reading as Option/bool/Default may be added"
    );
}

/// A small crate in the shape of `src/lib.rs`, for testing the listing apart
/// from how `src/lib.rs` happens to be spelt.
const FIXTURE: &str = "
#![no_std]
/// Docs.
#[derive(Debug, Clone, Copy)]
pub enum E<T> {
    /// Docs.
    A(T),
    B,
}
impl<T> E<T> {
    /// Docs.
    pub fn m(&self) {}
}
impl<T> core::iter::FromIterator<T> for E<T> {
    fn from_iter<I: IntoIterator<Item = T>>(_: I) -> Self { E::B }
}
";

#[test]
fn the_listing_moves_with_every_change_to_the_surface() {
    let base = surface(FIXTURE);
    let moved = [
        // A reading under a new name, an impl, or anything else.
        format!("{FIXTURE}\nimpl<T> E<T> {{ pub fn is_found(&self) -> bool {{ true }} }}"),
        format!("{FIXTURE}\nimpl<T> Default for E<T> {{ fn default() -> Self {{ E::B }} }}"),
        format!(
            "{FIXTURE}\nimpl<T> From<Option<T>> for E<T> {{ fn from(_: Option<T>) -> Self {{ E::B }} }}"
        ),
        format!("{FIXTURE}\nmacro_rules! more {{ () => {{}} }}"),
        format!("{FIXTURE}\npub fn found<T>(_: E<T>) -> bool {{ true }}"),
        format!("{FIXTURE}\nuse core::convert::From;"),
        // A derive, plain or conditional, and what a derived `Default` needs.
        FIXTURE.replace(
            "#[derive(Debug, Clone, Copy)]",
            "#[derive(Debug, Clone, Copy, Default)]",
        ),
        FIXTURE.replace(
            "#[derive(Debug, Clone, Copy)]",
            "#[cfg_attr(target_os = \"macos\", derive(Default))]\n#[derive(Debug, Clone, Copy)]",
        ),
        FIXTURE.replace("    B,", "    #[default]\n    B,"),
        FIXTURE.replace("    B,", "    #[cfg_attr(unix, default)]\n    B,"),
        // A new variant, or a changed one.
        FIXTURE.replace("    B,", "    B,\n    C,"),
        FIXTURE.replace("    A(T),", "    A(T, T),"),
        // A method made conditional, or visible, or added in a conditional impl.
        FIXTURE.replace(
            "    /// Docs.\n    pub fn m",
            "    #[cfg(unix)]\n    pub fn m",
        ),
        FIXTURE.replace("pub fn m(&self)", "fn m(&self)"),
        FIXTURE.replace("impl<T> E<T> {", "#[cfg(unix)]\nimpl<T> E<T> {"),
        // An impl made conditional.
        FIXTURE.replace(
            "impl<T> core::iter::FromIterator",
            "#[cfg(unix)]\nimpl<T> core::iter::FromIterator",
        ),
        // A crate attribute.
        FIXTURE.replace(
            "#![no_std]",
            "#![no_std]\n#![cfg_attr(unix, allow(unused))]",
        ),
    ];
    for changed in &moved {
        assert_ne!(changed.as_str(), FIXTURE, "the change applied");
        assert_ne!(surface(changed), base, "{changed}");
    }
    // What does not change the surface does not move the listing.
    let unmoved = [
        FIXTURE.replace(
            "#[derive(Debug, Clone, Copy)]",
            "#[derive(Copy, Debug, Clone)]",
        ),
        FIXTURE.replace("/// Docs.\n#[derive", "/// Other docs.\n#[derive"),
        FIXTURE.replace("{ E::B }", "{\n        E::B\n    }"),
    ];
    for unchanged in &unmoved {
        assert_ne!(unchanged.as_str(), FIXTURE, "the change applied");
        assert_eq!(surface(unchanged), base, "{unchanged}");
    }
}
