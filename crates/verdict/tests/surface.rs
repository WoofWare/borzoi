//! The crate's whole surface, held to an exact list.
//!
//! The crate exists to have no reading of an incomplete answer as a complete
//! one, and such a reading can be added under any name, on any platform, or
//! by loosening a signature: an `is_found`, an `ok`, a derived `Default`, one
//! derived only under a `cfg_attr`, a trait impl, an `FnOnce` bound made
//! `Fn`. A `compile_fail` doctest catches only what it spells, on the platform
//! it runs on. So this test reads `src/lib.rs` and lists all of it but what
//! cannot change the surface: doc comments, and the statements of function
//! bodies. What a body holds that can reach the surface is listed: each item
//! declared in it (an impl there adds methods callable from outside), listed
//! as a top-level one is, and each macro it invokes, with its arguments, which
//! may expand to one or hold one. The walk visits every expression, type and
//! pattern of the body, so a block declaring items is found wherever it sits;
//! only a macro's arguments are opaque to it, and those are listed whole.
//! Nothing else is modelled or left out, so no dimension of the surface can be
//! missed.
//!
//! Each item is a line: a type with its attributes, variants and fields, a
//! free item as written, the crate's own attributes. An impl is a line for its
//! header and a line for each member under it, so a moved signature shows as
//! one line. A plain `derive` is listed with its names sorted, so reordering
//! one moves nothing. The list must equal [`SURFACE`] exactly. Adding an
//! operation means adding its line here, together with its laws in
//! `tests/laws.rs`.

use quote::ToTokens;

/// Every line of `src/lib.rs`'s listing, sorted.
const SURFACE: &str = r#"
# ! [forbid (unsafe_code)]
# ! [no_std]
# [derive (Clone , Copy , Debug , Eq , Hash , PartialEq)] pub enum Lookup < T , C > { Found (T) , ProvedAbsent , Unknown (C) , }
# [derive (Clone , Copy , Debug , Eq , Hash , PartialEq)] pub enum Verdict < T , C > { Certain (T) , Unknown (C) , }
enum Reading < C > { Values , Ended , Unknown (C) , }
impl < T , C , I : Iterator < Item = Verdict < T , C > > > Iterator for UntilUnknown < I , C > { }
impl < T , C , I : Iterator < Item = Verdict < T , C > > > Iterator for UntilUnknown < I , C > { } => fn next (& mut self) -> Option < T > { }
impl < T , C , I : Iterator < Item = Verdict < T , C > > > Iterator for UntilUnknown < I , C > { } => fn next => macro matches ! (self . state , Reading :: Values)
impl < T , C , I : Iterator < Item = Verdict < T , C > > > Iterator for UntilUnknown < I , C > { } => fn size_hint (& self) -> (usize , Option < usize >) { }
impl < T , C , I : Iterator < Item = Verdict < T , C > > > Iterator for UntilUnknown < I , C > { } => type Item = T ;
impl < T , C , V : FromIterator < T > > FromIterator < Verdict < T , C > > for Verdict < V , C > { }
impl < T , C , V : FromIterator < T > > FromIterator < Verdict < T , C > > for Verdict < V , C > { } => fn from_iter < I : IntoIterator < Item = Verdict < T , C > > > (iter : I) -> Self { }
impl < T , C > Lookup < T , C > { }
impl < T , C > Lookup < T , C > { } => pub fn and_then < U > (self , f : impl FnOnce (T) -> Lookup < U , C >) -> Lookup < U , C > { }
impl < T , C > Lookup < T , C > { } => pub fn as_ref (& self) -> Lookup < & T , & C > { }
impl < T , C > Lookup < T , C > { } => pub fn into_verdict (self) -> Verdict < Option < T > , C > { }
impl < T , C > Lookup < T , C > { } => pub fn map < U > (self , f : impl FnOnce (T) -> U) -> Lookup < U , C > { }
impl < T , C > Lookup < T , C > { } => pub fn map_cause < D > (self , f : impl FnOnce (C) -> D) -> Lookup < T , D > { }
impl < T , C > Lookup < T , C > { } => pub fn or_shadowed (self , outer : impl FnOnce () -> Lookup < T , C >) -> Lookup < T , C > { }
impl < T , C > Verdict < Option < T > , C > { }
impl < T , C > Verdict < Option < T > , C > { } => pub fn into_lookup (self) -> Lookup < T , C > { }
impl < T , C > Verdict < T , C > { }
impl < T , C > Verdict < T , C > { } => pub fn and_then < U > (self , f : impl FnOnce (T) -> Verdict < U , C >) -> Verdict < U , C > { }
impl < T , C > Verdict < T , C > { } => pub fn as_ref (& self) -> Verdict < & T , & C > { }
impl < T , C > Verdict < T , C > { } => pub fn map < U > (self , f : impl FnOnce (T) -> U) -> Verdict < U , C > { }
impl < T , C > Verdict < T , C > { } => pub fn map_cause < D > (self , f : impl FnOnce (C) -> D) -> Verdict < T , D > { }
impl < T , C > Verdict < T , C > { } => pub fn zip < U > (self , other : Verdict < U , C >) -> Verdict < (T , U) , C > { }
struct UntilUnknown < I , C > { source : I , state : Reading < C > , }
"#;

/// Drops what cannot change the surface (doc comments) and sorts the names
/// of each plain `derive`.
fn normalise_attributes(attrs: &mut Vec<syn::Attribute>) {
    attrs.retain(|a| !a.path().is_ident("doc"));
    for attr in attrs.iter_mut() {
        if !attr.path().is_ident("derive") {
            continue;
        }
        let mut names = Vec::new();
        attr.parse_nested_meta(|meta| {
            names.push(meta.path.to_token_stream().to_string());
            Ok(())
        })
        .expect("a derive list");
        names.sort();
        let sorted = format!("#[derive({})]", names.join(", "));
        let mut parsed = syn::parse::Parser::parse_str(syn::Attribute::parse_outer, &sorted)
            .expect("a derive attribute");
        *attr = parsed.pop().expect("one attribute");
    }
}

/// The item without its docs (its own, its variants', its fields' and its
/// members') or its function bodies, which cannot change the surface.
fn normalise_item(item: &mut syn::Item) {
    if let Some(attrs) = item_attributes(item) {
        normalise_attributes(attrs);
    }
    let fields = |fields: &mut syn::Fields| {
        for field in fields.iter_mut() {
            normalise_attributes(&mut field.attrs);
        }
    };
    match item {
        syn::Item::Fn(f) => f.block.stmts.clear(),
        syn::Item::Enum(e) => {
            for variant in &mut e.variants {
                normalise_attributes(&mut variant.attrs);
                fields(&mut variant.fields);
            }
        }
        syn::Item::Struct(s) => fields(&mut s.fields),
        syn::Item::Impl(i) => {
            for member in &mut i.items {
                match member {
                    syn::ImplItem::Const(c) => normalise_attributes(&mut c.attrs),
                    syn::ImplItem::Fn(f) => {
                        normalise_attributes(&mut f.attrs);
                        f.block.stmts.clear();
                    }
                    syn::ImplItem::Type(t) => normalise_attributes(&mut t.attrs),
                    syn::ImplItem::Macro(m) => normalise_attributes(&mut m.attrs),
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

/// The attributes of an item, for the kinds that carry them.
fn item_attributes(item: &mut syn::Item) -> Option<&mut Vec<syn::Attribute>> {
    Some(match item {
        syn::Item::Const(i) => &mut i.attrs,
        syn::Item::Enum(i) => &mut i.attrs,
        syn::Item::ExternCrate(i) => &mut i.attrs,
        syn::Item::Fn(i) => &mut i.attrs,
        syn::Item::ForeignMod(i) => &mut i.attrs,
        syn::Item::Impl(i) => &mut i.attrs,
        syn::Item::Macro(i) => &mut i.attrs,
        syn::Item::Mod(i) => &mut i.attrs,
        syn::Item::Static(i) => &mut i.attrs,
        syn::Item::Struct(i) => &mut i.attrs,
        syn::Item::Trait(i) => &mut i.attrs,
        syn::Item::TraitAlias(i) => &mut i.attrs,
        syn::Item::Type(i) => &mut i.attrs,
        syn::Item::Union(i) => &mut i.attrs,
        syn::Item::Use(i) => &mut i.attrs,
        _ => return None,
    })
}

/// What a function body holds that can reach the surface: the items declared
/// in it (an impl there adds methods callable from outside), and the macros it
/// invokes, whole (a macro may expand to items, and its arguments, which the
/// walk cannot see into, may declare them).
#[derive(Default)]
struct BodyContents {
    items: Vec<syn::Item>,
    macros: std::collections::BTreeSet<String>,
}

impl<'ast> syn::visit::Visit<'ast> for BodyContents {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        // Listed in full by the caller, so not descended into here.
        self.items.push(item.clone());
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        // The whole invocation: its arguments are opaque to the walk, and may
        // hold a block declaring items.
        self.macros.insert(mac.to_token_stream().to_string());
    }
}

fn body_contents(block: &syn::Block) -> BodyContents {
    let mut contents = BodyContents::default();
    syn::visit::Visit::visit_block(&mut contents, block);
    contents
}

/// Lists what a function body holds that can reach the surface, under
/// `context`: each nested item, listed as a top-level one is, and each
/// macro the body invokes.
fn list_body(context: &str, block: &syn::Block, lines: &mut Vec<String>) {
    let contents = body_contents(block);
    for mac in &contents.macros {
        lines.push(format!("{context} => macro {mac}"));
    }
    let mut nested = Vec::new();
    list_items(contents.items, &mut nested);
    for line in nested {
        lines.push(format!("{context} => nested {line}"));
    }
}

/// Lists `items` into `lines`: each item but its docs and function bodies, an
/// impl as its header and a line per member, and what each body holds that can
/// reach the surface.
fn list_items(items: Vec<syn::Item>, lines: &mut Vec<String>) {
    for mut item in items {
        match &item {
            syn::Item::Fn(f) => list_body(&format!("fn {}", f.sig.ident), &f.block, lines),
            syn::Item::Impl(i) => {
                let mut header = i.clone();
                header.items.clear();
                let mut normalised_header = syn::Item::Impl(header);
                normalise_item(&mut normalised_header);
                let header = normalised_header.to_token_stream().to_string();
                for member in &i.items {
                    if let syn::ImplItem::Fn(f) = member {
                        list_body(&format!("{header} => fn {}", f.sig.ident), &f.block, lines);
                    }
                }
            }
            _ => {}
        }
        normalise_item(&mut item);
        match item {
            syn::Item::Impl(i) => {
                let mut header = i.clone();
                header.items.clear();
                let header = header.to_token_stream().to_string();
                for member in &i.items {
                    lines.push(format!("{header} => {}", member.to_token_stream()));
                }
                lines.push(header);
            }
            other => lines.push(other.to_token_stream().to_string()),
        }
    }
}

fn surface(source: &str) -> Vec<String> {
    let mut file = syn::parse_file(source).expect("the source parses");
    normalise_attributes(&mut file.attrs);
    let mut lines: Vec<String> = file
        .attrs
        .iter()
        .map(|a| a.to_token_stream().to_string())
        .collect();
    list_items(file.items, &mut lines);
    lines.sort();
    lines
}

#[test]
fn the_surface_is_exactly_the_listed_operations() {
    let actual = surface(include_str!("../src/lib.rs"));
    let expected: Vec<String> = SURFACE
        .lines()
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();
    let missing: Vec<&String> = expected.iter().filter(|l| !actual.contains(l)).collect();
    let extra: Vec<&String> = actual.iter().filter(|l| !expected.contains(l)).collect();
    assert!(
        missing.is_empty() && extra.is_empty() && actual == expected,
        "the crate's surface moved; every operation needs its laws in tests/laws.rs \
         and its line in SURFACE, and no reading as Option/bool/Default may be added\n\
         listed but absent: {missing:#?}\npresent but unlisted: {extra:#?}"
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
struct S<C> {
    /// Docs.
    c: C,
}
impl<T> E<T> {
    /// Docs.
    pub fn m(&self, f: impl FnOnce() -> T) -> Option<T> {
        debug_assert!(true);
        Some(f())
    }
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
        // A new variant, a changed one, a changed field.
        FIXTURE.replace("    B,", "    B,\n    C,"),
        FIXTURE.replace("    A(T),", "    A(T, T),"),
        FIXTURE.replace("    c: C,", "    c: Option<C>,"),
        // A signature: a bound loosened, a parameter, a return type, a
        // generic bound on the impl, a where clause, visibility.
        FIXTURE.replace("impl FnOnce() -> T", "impl Fn() -> T"),
        FIXTURE.replace("f: impl FnOnce() -> T", "f: impl FnOnce() -> T, g: bool"),
        FIXTURE.replace("-> Option<T> {", "-> bool {"),
        FIXTURE.replace("impl<T> E<T> {", "impl<T: Copy> E<T> {"),
        FIXTURE.replace("impl<T> E<T> {", "impl<T> E<T> where T: Copy {"),
        FIXTURE.replace("pub fn m(", "fn m("),
        FIXTURE.replace("Item = T>>(_: I)", "Item = T> + Clone>(_: I)"),
        // A method made conditional, or added in a conditional impl.
        FIXTURE.replace(
            "    /// Docs.\n    pub fn m",
            "    #[cfg(unix)]\n    pub fn m",
        ),
        FIXTURE.replace("impl<T> E<T> {", "#[cfg(unix)]\nimpl<T> E<T> {"),
        FIXTURE.replace(
            "impl<T> core::iter::FromIterator",
            "#[cfg(unix)]\nimpl<T> core::iter::FromIterator",
        ),
        // An item declared in a function body: an impl there adds methods
        // callable from outside the crate. And a macro a body invokes, which
        // may expand to one.
        FIXTURE.replace(
            "Some(f())",
            "mod hidden { impl<T> super::E<T> { pub fn did_find(&self) -> bool { true } } }\n        Some(f())",
        ),
        FIXTURE.replace(
            "{ E::B }",
            "{ impl<T> E<T> { pub fn found(&self) -> bool { true } } E::B }",
        ),
        FIXTURE.replace("Some(f())", "{ let _ = { fn inner() {} }; Some(f()) }"),
        FIXTURE.replace("Some(f())", "include!(\"more.rs\"); Some(f())"),
        FIXTURE.replace("Some(f())", "Some(core::convert::identity(stamp!(f())))"),
        // A macro's arguments, which the walk cannot see into: a block in them
        // may declare an impl.
        FIXTURE.replace(
            "debug_assert!(true)",
            "debug_assert!({ mod m { impl<T> super::super::E<T> { pub fn w(&self) -> bool { true } } } true })",
        ),
        FIXTURE.replace("debug_assert!(true)", "debug_assert!(false)"),

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
    // What does not change the surface does not move the listing: derive
    // order, docs, formatting and function bodies.
    let unmoved = [
        FIXTURE.replace(
            "#[derive(Debug, Clone, Copy)]",
            "#[derive(Copy, Debug, Clone)]",
        ),
        FIXTURE.replace("/// Docs.\n#[derive", "/// Other docs.\n#[derive"),
        FIXTURE.replace("    /// Docs.\n    c: C,", "    c: C,"),
        FIXTURE.replace("{ E::B }", "{\n        E::B\n    }"),
        FIXTURE.replace("Some(f())", "let x = f();\n        Some(x)"),
    ];
    for unchanged in &unmoved {
        assert_ne!(unchanged.as_str(), FIXTURE, "the change applied");
        assert_eq!(surface(unchanged), base, "{unchanged}");
    }
}
