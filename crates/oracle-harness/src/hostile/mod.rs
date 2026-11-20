//! Hostile values: the strange inputs every generator should search.
//!
//! A review finding that needs a contrived input (a file named
//! `-o:Evil.dll`, a FIFO where a DLL is expected, a property whose value
//! holds `%0A--out:`) names a *value* no generator produced. Fixing the one
//! site it names leaves the neighbouring site for the next review. This
//! module holds those values once, by the **kind** of input they are
//! ([`Kind`]), so a generator that consumes a kind draws every family of them
//! ([`Dimension`]), and a new finding is answered by a new dimension that
//! every such generator then searches.
//!
//! # The parts
//!
//! - **Alphabets.** One typed table per kind ([`name`], [`spelling`],
//!   [`value`], [`mod@env`], [`cwd`], [`wire`], [`xml`], [`source`]) and the
//!   file-system states ([`fs`]). Every entry is a value, the dimension it belongs to and
//!   the reason it is hostile, so a failure explains itself.
//! - **Drawing.** An alphabet is small enough to enumerate
//!   ([`Alphabet::entries`]), which is how a harness covers every dimension
//!   on every run. Beyond that, a generator mixes hostile values into its own
//!   at [`RATE`]: [`Alphabet::sample`] for a generator with its own random
//!   numbers, [`Alphabet::strategy`] for proptest. What is drawn is a
//!   [`Drawn`]: the value and the dimensions mixed into it.
//! - **The census** ([`census`]). A harness records each drawn value where it
//!   *reaches the subject*, with what the subject did. A dimension the
//!   harness declares and never reaches fails its test: a hostile value
//!   filtered out on the way would otherwise pass without checking anything.
//!   What each dimension met is pinned per harness as an exact manifest.
//! - **Coverage** ([`coverage`]). Every generative differential and
//!   perturbation sweep in the workspace is in one table, declaring the kinds
//!   it draws or the reason none applies. A generator in neither state fails.
//! - **The seed corpus** ([`seed`]). The review findings the library was
//!   built from, each mapped to the dimension that generates it and to what
//!   became of it.
//!
//! # Adding a dimension
//!
//! Add the variant to the `dimensions!` table below with its reason, and at
//! least one entry to its kind's alphabet (the alphabets' tests fail on a
//! dimension with none). Every harness that declares the kind then fails
//! until it reaches the new dimension or excludes it with a reason, and its
//! census manifest records which.

pub mod census;
pub mod coverage;
pub mod cwd;
pub mod env;
pub mod fs;
pub mod name;
pub mod seed;
pub mod source;
pub mod spelling;
pub mod value;
pub mod wire;
pub mod xml;

use std::collections::BTreeSet;
use std::fmt;

use proptest::strategy::{BoxedStrategy, Strategy};

/// One in this many is hostile, where a generator mixes hostile values into
/// its own. The rest are the generator's own values, so the space it already
/// modelled still dominates its run.
///
/// The unit is the *case*. A generator that builds a case from one draw can
/// draw at the rate ([`Alphabet::sample`], [`Alphabet::strategy`]). One that
/// builds a case from many draws decides once per case whether it mixes
/// ([`mixes`]) and, in a case that does, takes hostile entries where it
/// likes ([`Alphabet::pick`]): ten draws each hostile at this rate would
/// leave hardly a case plain.
pub const RATE: u64 = 4;

/// Whether a case mixes hostile values in: so for one `entropy` in [`RATE`].
pub fn mixes(entropy: u64) -> bool {
    entropy.is_multiple_of(RATE)
}

/// The kind of input a generator hands its subject. A generator declares the
/// kinds it consumes; each kind has one alphabet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// The name of a file or directory: one path component.
    FileName,
    /// How a path to a file is spelt: its separators, its `.` and `..`, its
    /// root.
    PathSpelling,
    /// What sits at a path: a regular file, a FIFO, a dangling link.
    FsState,
    /// A file changing between two requests in a way a stamp does not show.
    FsChange,
    /// A file changing while one request reads it.
    FsRace,
    /// The value of an MSBuild property or of item metadata.
    PropertyValue,
    /// How a value is written in an XML document.
    XmlSpelling,
    /// An environment variable: its name and its value.
    Environment,
    /// The directory a tool is started from.
    WorkingDirectory,
    /// A request on the wire to one of our own oracles.
    Wire,
    /// The text of an F# source file, as a tool around the compiler reads it.
    SourceText,
}

impl Kind {
    /// Every kind.
    pub const ALL: &'static [Kind] = &[
        Kind::FileName,
        Kind::PathSpelling,
        Kind::FsState,
        Kind::FsChange,
        Kind::FsRace,
        Kind::PropertyValue,
        Kind::XmlSpelling,
        Kind::Environment,
        Kind::WorkingDirectory,
        Kind::Wire,
        Kind::SourceText,
    ];

    /// The kind's name in a dimension's key and in the coverage table.
    pub fn id(self) -> &'static str {
        match self {
            Kind::FileName => "name",
            Kind::PathSpelling => "spelling",
            Kind::FsState => "fs",
            Kind::FsChange => "change",
            Kind::FsRace => "race",
            Kind::PropertyValue => "value",
            Kind::XmlSpelling => "xml",
            Kind::Environment => "env",
            Kind::WorkingDirectory => "cwd",
            Kind::Wire => "wire",
            Kind::SourceText => "source",
        }
    }

    /// The kind named `id`.
    pub fn from_id(id: &str) -> Option<Kind> {
        Kind::ALL.iter().copied().find(|k| k.id() == id)
    }

    /// The dimensions of this kind.
    pub fn dimensions(self) -> impl Iterator<Item = Dimension> {
        Dimension::ALL
            .iter()
            .copied()
            .filter(move |d| d.kind() == self)
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}

/// Declares [`Dimension`]: each variant with its kind, its name within the
/// kind, and the reason values of the family are hostile.
macro_rules! dimensions {
    ($( $kind:ident { $( $(#[$meta:meta])* $variant:ident = $id:literal: $why:literal, )+ } )+) => {
        /// One family of hostile values within a [`Kind`]: what a census
        /// counts, and what a review finding is answered with.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum Dimension {
            $( $( $(#[$meta])* #[doc = $why] $variant, )+ )+
        }

        impl Dimension {
            /// Every dimension, grouped by kind.
            pub const ALL: &'static [Dimension] = &[ $( $( Dimension::$variant, )+ )+ ];

            /// The kind of input the dimension belongs to.
            pub fn kind(self) -> Kind {
                match self { $( $( Dimension::$variant => Kind::$kind, )+ )+ }
            }

            /// The dimension's name within its kind.
            pub fn id(self) -> &'static str {
                match self { $( $( Dimension::$variant => $id, )+ )+ }
            }

            /// Why values of the family are hostile.
            pub fn why(self) -> &'static str {
                match self { $( $( Dimension::$variant => $why, )+ )+ }
            }
        }
    };
}

dimensions! {
    FileName {
        SwitchShaped = "switch-shaped":
            "A name with a leading `-` or `@` is read as an option or a response file by a tool handed it as an argument.",
        EarlyColon = "early-colon":
            "A `:` after one or two characters reads as an option's separator (`r:`), a drive letter or a URI scheme.",
        Backslash = "backslash":
            "A `\\` is a name character on Unix and a separator to MSBuild, which rewrites some to `/`.",
        PercentEscape = "percent-escape":
            "MSBuild decodes `%XX` in an item spec or a value, so the text names another file, or splits, after decoding.",
        ListSeparator = "list-separator":
            "A `;` splits an MSBuild list and a `,` a command line's property list.",
        Quote = "quote":
            "A quote opens a quoted string to a command line, a response file or a condition.",
        GlobChar = "glob-char":
            "A `*`, `?` or `[` makes an item spec a pattern.",
        Expansion = "expansion":
            "`$(`, `@(` and `%(` start an MSBuild expansion.",
        XmlMarkup = "xml-markup":
            "A `&`, `<` or a character reference must be escaped where the name is written in XML, and is text once read back.",
        LineBreak = "line-break":
            "A line break in a name splits a response file's line, a log line or a wire request.",
        ControlChar = "control-char":
            "A control character other than a line break: a tab, an escape, a NUL (which no file name holds and which ends a C string).",
        EdgeDotOrSpace = "edge-dot-or-space":
            "A leading or trailing dot or space is trimmed by some readers and kept by the file system.",
        DotName = "dot-name":
            "A name that is all dots, or begins with one: `.` and `..` are directories, and a leading dot hides a file from a default glob.",
        Invisible = "invisible":
            "A character with no glyph (a soft hyphen, a zero-width space, a direction override) that a culture-aware comparison ignores.",
        CaseFold = "case-fold":
            "A name differing from another only by case, or by a letter whose case mapping is not one to one.",
        Normalisation = "normalisation":
            "One text in two Unicode normal forms: equal to some file systems and comparisons, distinct bytes to others.",
        Confusable = "confusable":
            "A character that looks like another: a Cyrillic letter, a full-width or division slash, a full-width colon.",
        Utf16Width = "utf16-width":
            "A character outside the Basic Multilingual Plane is one character to us and two UTF-16 units to .NET.",
        NonUtf8 = "non-utf8":
            "Bytes that are not UTF-8: a path a string cannot hold and JSON cannot carry.",
        Long = "long":
            "A name at or past the file system's length limit.",
        KindByExtension = "kind-by-extension":
            "A tool that classifies its arguments by extension reads a `.dll`, `.resx` or `.rsp` as something other than a source.",
    }
    PathSpelling {
        CurDir = "curdir":
            "`./x` and `x/.` are `x` to the file system and other text to a comparison of spellings.",
        DotDot = "dotdot":
            "`d/../x` is `x` lexically, and physically only if `d` is a directory that is no link.",
        DotDotThroughLink = "dotdot-through-link":
            "`link/../x` names one file lexically and another through the file system.",
        DotDotThroughMissing = "dotdot-through-missing":
            "`missing/../x` is `x` lexically and no file to the file system.",
        Doubled = "doubled-separator":
            "A doubled separator is one separator to the file system.",
        TrailingSeparator = "trailing-separator":
            "A trailing separator asks for a directory.",
        BackslashSeparator = "backslash-separator":
            "A `\\` separator is a name character on Unix, which MSBuild rewrites only where the rewritten path exists.",
        EscapedSeparator = "escaped-separator":
            "`%2F` and `%5C` become separators only after MSBuild decodes them.",
        ParentEscape = "parent-escape":
            "A leading `..` names a file outside the directory the path is relative to.",
        Rooted = "rooted":
            "A leading `/` makes a relative name absolute, outside the directory it was meant to be relative to.",
        Root = "root":
            "The root path has no parent and no file name.",
        WindowsRoot = "windows-root":
            "A drive letter, a UNC prefix or a verbatim prefix is a root on Windows and a relative name on Unix.",
        CaseVariant = "case-variant":
            "A spelling in another case names the same file only on a case-insensitive file system.",
        ThroughLink = "through-link":
            "A path through a link to a directory has another physical spelling.",
        Relative = "relative":
            "A relative path means a file only against a working directory.",
        LongPath = "long-path":
            "A path longer than the operating system's limit for one call.",
    }
    FsState {
        Regular = "regular":
            "A regular file with content: the state every reader models, which a census must show it commits on.",
        Empty = "empty":
            "A regular file of no bytes.",
        Fifo = "fifo":
            "A FIFO: an open for reading waits for a writer, for ever.",
        Socket = "socket":
            "A socket: an open fails, with an error unlike a missing file's.",
        CharDevice = "char-device":
            "A character device: a read never ends, or returns nothing, and its length is zero.",
        Symlink = "symlink":
            "A link to a regular file in the tree: its own metadata is not its target's.",
        DanglingSymlink = "dangling-symlink":
            "A link to nothing: the directory lists it and an open fails.",
        SymlinkLoop = "symlink-loop":
            "A link to itself: resolving it fails, with an error unlike a missing file's.",
        SymlinkOutOfTree = "symlink-out-of-tree":
            "A link to a file outside the tree the reader was given.",
        Directory = "directory":
            "A directory where a file is expected.",
        Unreadable = "unreadable":
            "A file its owner may not read: it exists and an open fails.",
        ReadOnly = "read-only":
            "A file its owner may not write.",
        Missing = "missing":
            "No file at all.",
    }
    FsChange {
        SameStampRewrite = "same-stamp-rewrite":
            "A file rewritten in place with other bytes of the same length, its modification time put back.",
        SameStampResize = "same-stamp-resize":
            "A file rewritten in place with bytes of another length, its modification time put back.",
        SameStampReplace = "same-stamp-replace":
            "A file replaced by a rename of another, with the old modification time: a new inode under the old name.",
        Appears = "appears":
            "A file that was absent at one request and present at the next.",
        Disappears = "disappears":
            "A file that was present at one request and absent at the next.",
    }
    FsRace {
        DeletedAfterListing = "deleted-after-listing":
            "A file deleted between a directory listing that named it and the open.",
        RewrittenDuringRequest = "rewritten-during-request":
            "A file rewritten while one request reads it, so two reads within the request differ.",
        ReplacedAfterHash = "replaced-after-hash":
            "A file replaced between the read that identified it and the read that used it.",
        AppearsDuringRequest = "appears-during-request":
            "A file recorded absent that appears before the request ends.",
    }
    PropertyValue {
        Option = "option":
            "A value shaped as a compiler option, in each spelling fsc reads one.",
        PaddedOption = "padded-option":
            "An option behind a space or a word, where a command line is split at spaces.",
        OptionAfterLineBreak = "option-after-line-break":
            "An option behind a line break, written or escaped, where a response file is split at lines.",
        ResponseFile = "response-file":
            "A value with a leading `@` names a response file to a command line.",
        QuotedArgument = "quoted-argument":
            "Quotes that group, split or hide part of an argument.",
        SelfSetProperty = "self-set-property":
            "A reference to a property the build process sets for itself, which an evaluation outside a build never sees.",
        ReadsTheBuild = "reads-the-build":
            "A value that reads the build's own command line, working directory or file system.",
        Padded = "padded":
            "Leading or trailing whitespace, which some readers trim and others compare.",
        PathSeparator = "path-separator":
            "A separator in a value that is used as one path component.",
        Blank = "blank":
            "An empty value, or one of whitespace alone: set, and yet nothing.",
        OverwrittenLater = "overwritten-later":
            "A hostile value a later write replaces: what read it in between has already used it.",
        LongValue = "long-value":
            "A value of tens of thousands of characters.",
        NumberSpelling = "number-spelling":
            "A spelling at the edge of what .NET reads as a number: NaN, an infinity, hex, a sign, a trailing NUL.",
        VersionSpelling = "version-spelling":
            "A spelling at the edge of what .NET or MSBuild reads as a version: a `-0` component, five components, a `v`, a suffix.",
        BooleanSpelling = "boolean-spelling":
            "A spelling at the edge of MSBuild's boolean vocabulary: a negation, another case, padding.",
        ItemSeparator = "item-separator":
            "A `;` that splits the value into items, or into the pieces an indexer counts.",
        ItemExpression = "item-expression":
            "Text that forms an item list, transform or metadata reference where it is spliced, which MSBuild expands in an item's condition.",
        CaseFolding = "case-folding":
            "A letter whose case folds outside ASCII, which ordinal-ignore-case comparison folds and ASCII folding does not.",
    }
    XmlSpelling {
        CharRef = "char-ref":
            "A character written as a decimal or hexadecimal reference.",
        Cdata = "cdata":
            "Text in a CDATA section, where markup characters are themselves.",
        CommentSplit = "comment-split":
            "Text with a comment inside it, which MSBuild reads as one text.",
        LiteralWhitespace = "literal-whitespace":
            "A tab or line break written as itself, which an XML reader may normalise and MSBuild does not.",
    }
    Environment {
        PropertyName = "property-name":
            "A variable named as a property MSBuild reads: every variable is a property.",
        ToolchainVariable = "toolchain-variable":
            "A variable the .NET host, MSBuild or NuGet reads to choose what it runs or where it looks.",
        CompilerSelector = "compiler-selector":
            "A variable naming the compiler or its host.",
        BuildSetVariable = "build-set-variable":
            "A variable the build process sets in its own environment before evaluating.",
        Locale = "locale":
            "A variable choosing the culture, and with it case mapping and comparison.",
        EmptyValue = "empty-value":
            "A variable that is set and empty.",
        HostileValue = "hostile-value":
            "A variable whose value holds a line break, a control character or a list separator.",
        CaseVariantName = "case-variant-name":
            "Two variables whose names differ by case: two variables to Unix and one property to MSBuild.",
        NotAPropertyName = "not-a-property-name":
            "A variable whose name no property can have.",
    }
    WorkingDirectory {
        ProjectDirectory = "project-directory":
            "The project's own directory, holding its `obj/`.",
        ProjectDirectoryUnrestored = "project-directory-unrestored":
            "The project's own directory before any restore, with no `obj/`.",
        UnrelatedEmpty = "unrelated-empty":
            "An empty directory unrelated to the project.",
        HoldsProjectSegments = "holds-project-segments":
            "An unrelated directory holding the path segments the project names (`obj/`, `bin/`).",
        RootDirectory = "root-directory":
            "The root directory.",
    }
    Wire {
        BlankLine = "blank-line":
            "A blank line where a request is expected.",
        MultiLine = "multi-line":
            "One request over several lines: a line-based oracle reads several requests.",
        TrailingUnicodeWhitespace = "trailing-unicode-whitespace":
            "Whitespace one side's JSON reader trims and the other's does not.",
        WrongType = "wrong-type":
            "A field of the wrong JSON type.",
        UnknownField = "unknown-field":
            "A field the oracle does not know.",
        DuplicateKey = "duplicate-key":
            "One key twice in an object: readers differ on which wins.",
        MissingField = "missing-field":
            "A required field left out.",
        NotAnObject = "not-an-object":
            "Well-formed JSON that is no request: an array, a string, `null`.",
        NotJson = "not-json":
            "Text that is not JSON.",
    }
    SourceText {
        LineDirective = "line-directive":
            "A `#line` directive: positions after it are reported in another file or on another line.",
        DirectiveLookalike = "directive-lookalike":
            "Text a scan takes for a directive or a comment and the lexer does not: in a comment, in a string, in an operator.",
        ScriptDirective = "script-directive":
            "A `#r` or `#load` directive, which means one thing in a script and another in a compiled source.",
        ToolDefine = "tool-define":
            "A conditional on a symbol only some tools define (`EDITING`, `COMPILED`, `INTERACTIVE`).",
        LongRun = "long-run":
            "A very long run of one character, on which a careless scan is quadratic.",
        ByteOrderMark = "byte-order-mark":
            "A byte order mark before the first token.",
        LineEnds = "line-ends":
            "Line ends other than a line feed, which move positions and line counts.",
        NotText = "not-text":
            "Bytes in the file that are not text: invalid UTF-8, a NUL.",
    }
}

impl Dimension {
    /// `<kind>.<id>`: the dimension's key in a census manifest and in the seed
    /// table.
    pub fn key(self) -> String {
        format!("{}.{}", self.kind().id(), self.id())
    }

    /// The dimension with [`Self::key`] `key`.
    pub fn from_key(key: &str) -> Option<Dimension> {
        Dimension::ALL.iter().copied().find(|d| d.key() == key)
    }
}

impl fmt::Display for Dimension {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.kind().id(), self.id())
    }
}

/// One hostile value: what it is, the family it belongs to, and why this one
/// is in the alphabet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry<V> {
    /// The family.
    pub dimension: Dimension,
    /// The value.
    pub value: V,
    /// Why this value: what reads it wrongly, or the finding it came from.
    pub why: &'static str,
}

/// A value a generator drew, and the hostile dimensions mixed into it: none
/// for a value of the generator's own.
///
/// The dimensions travel with the value so that the harness can record them
/// where the value reaches its subject ([`census::Census::reached`]) and not
/// where it was drawn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Drawn<V> {
    /// The value.
    pub value: V,
    /// The dimensions mixed into it.
    pub hostile: BTreeSet<Dimension>,
}

impl<V> Drawn<V> {
    /// A value of the generator's own.
    pub fn plain(value: V) -> Self {
        Drawn {
            value,
            hostile: BTreeSet::new(),
        }
    }

    /// `entry`'s value, of its dimension.
    pub fn of(entry: &Entry<V>) -> Self
    where
        V: Clone,
    {
        Drawn {
            value: entry.value.clone(),
            hostile: BTreeSet::from([entry.dimension]),
        }
    }

    /// The value changed, of the same dimensions.
    pub fn map<W>(self, f: impl FnOnce(V) -> W) -> Drawn<W> {
        Drawn {
            value: f(self.value),
            hostile: self.hostile,
        }
    }

    /// Two drawn values as one, of both's dimensions: for a case built from
    /// several draws.
    pub fn zip<W>(self, other: Drawn<W>) -> Drawn<(V, W)> {
        let mut hostile = self.hostile;
        hostile.extend(other.hostile);
        Drawn {
            value: (self.value, other.value),
            hostile,
        }
    }
}

/// The hostile values of one kind.
#[derive(Debug, Clone)]
pub struct Alphabet<V> {
    kind: Kind,
    entries: Vec<Entry<V>>,
}

impl<V: Clone + fmt::Debug + PartialEq> Alphabet<V> {
    /// An alphabet of `kind` holding `entries`.
    ///
    /// # Panics
    ///
    /// If an entry is of another kind, if two entries of one dimension hold
    /// one value, or if a dimension of the kind has no entry: an alphabet
    /// that cannot produce a dimension would let every census of it fail for
    /// a reason no harness can fix.
    pub fn new(kind: Kind, entries: Vec<Entry<V>>) -> Self {
        for (i, e) in entries.iter().enumerate() {
            assert_eq!(
                e.dimension.kind(),
                kind,
                "{:?} is in the {kind} alphabet and of dimension {}",
                e.value,
                e.dimension
            );
            assert!(
                !entries[..i]
                    .iter()
                    .any(|o| o.dimension == e.dimension && o.value == e.value),
                "{:?} is in the {kind} alphabet twice under {}",
                e.value,
                e.dimension
            );
        }
        let alphabet = Alphabet { kind, entries };
        let empty: Vec<_> = kind
            .dimensions()
            .filter(|d| alphabet.of(*d).next().is_none())
            .collect();
        assert!(
            empty.is_empty(),
            "the {kind} alphabet has no entry for {empty:?}"
        );
        alphabet
    }

    /// The kind.
    pub fn kind(&self) -> Kind {
        self.kind
    }

    /// Every entry, for a harness that enumerates the alphabet.
    pub fn entries(&self) -> &[Entry<V>] {
        &self.entries
    }

    /// The entries of `dimension`.
    pub fn of(&self, dimension: Dimension) -> impl Iterator<Item = &Entry<V>> {
        self.entries
            .iter()
            .filter(move |e| e.dimension == dimension)
    }

    /// The alphabet without the entries `keep` rejects, for a place that
    /// cannot carry some values at all. A dimension left with no entry is one
    /// the harness must exclude from its census with the reason.
    pub fn filtered(&self, mut keep: impl FnMut(&Entry<V>) -> bool) -> Vec<Entry<V>> {
        self.entries.iter().filter(|e| keep(e)).cloned().collect()
    }

    /// A draw for a generator with random numbers of its own: a hostile entry
    /// for one `entropy` in [`RATE`], chosen by the rest of it, and `None`
    /// (draw a value of your own) otherwise.
    pub fn sample(&self, entropy: u64) -> Option<&Entry<V>> {
        sample(&self.entries, entropy)
    }

    /// An entry chosen by `entropy`, for a case that [`mixes`]. The number
    /// may be the one `mixes` took: the choice is by what is left of it once
    /// the part `mixes` read is taken off, as [`Alphabet::sample`] chooses.
    pub fn pick(&self, entropy: u64) -> &Entry<V> {
        &self.entries[((entropy / RATE) % self.entries.len() as u64) as usize]
    }

    /// A proptest strategy: `plain`'s values, with a hostile entry mixed in
    /// at [`RATE`].
    pub fn strategy(&self, plain: impl Strategy<Value = V> + 'static) -> BoxedStrategy<Drawn<V>>
    where
        V: 'static,
    {
        strategy(self.entries.clone(), plain)
    }
}

/// [`Alphabet::sample`] over any list of entries (an alphabet filtered for a
/// place, say).
pub fn sample<V>(entries: &[Entry<V>], entropy: u64) -> Option<&Entry<V>> {
    if entries.is_empty() || !entropy.is_multiple_of(RATE) {
        return None;
    }
    let index = (entropy / RATE) % entries.len() as u64;
    Some(&entries[index as usize])
}

/// [`Alphabet::strategy`] over any list of entries.
///
/// # Panics
///
/// If `entries` is empty: a strategy that never draws a hostile value is not
/// what the caller asked for.
pub fn strategy<V: Clone + fmt::Debug + 'static>(
    entries: Vec<Entry<V>>,
    plain: impl Strategy<Value = V> + 'static,
) -> BoxedStrategy<Drawn<V>> {
    assert!(
        !entries.is_empty(),
        "a hostile strategy needs at least one entry"
    );
    let hostile = proptest::sample::select(entries).prop_map(|e| Drawn::of(&e));
    proptest::prop_oneof![
        (RATE - 1) as u32 => plain.prop_map(Drawn::plain),
        1 => hostile,
    ]
    .boxed()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimension_keys_are_distinct_and_round_trip() {
        let mut seen = BTreeSet::new();
        for d in Dimension::ALL {
            assert!(seen.insert(d.key()), "{} names two dimensions", d.key());
            assert_eq!(Dimension::from_key(&d.key()), Some(*d));
            assert!(
                d.id()
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-'),
                "{d}'s name must be lower-case words joined by hyphens: it is a manifest key"
            );
        }
    }

    #[test]
    fn every_kind_has_a_dimension_and_a_distinct_name() {
        let mut seen = BTreeSet::new();
        for k in Kind::ALL {
            assert!(seen.insert(k.id()));
            assert_eq!(Kind::from_id(k.id()), Some(*k));
            assert!(k.dimensions().next().is_some(), "{k} has no dimension");
        }
        assert!(Dimension::ALL.iter().all(|d| Kind::ALL.contains(&d.kind())));
    }

    #[test]
    fn sampling_is_hostile_at_the_documented_rate_and_reaches_every_entry() {
        let entries: Vec<Entry<u32>> = (0..7)
            .map(|value| Entry {
                dimension: Dimension::Regular,
                value,
                why: "",
            })
            .collect();
        let draws: Vec<_> = (0..RATE * 7 * 3).map(|e| sample(&entries, e)).collect();
        let hostile: Vec<u32> = draws.iter().flatten().map(|e| e.value).collect();
        assert_eq!(hostile.len() as u64, 7 * 3);
        assert_eq!(
            hostile.iter().copied().collect::<BTreeSet<_>>().len(),
            7,
            "every entry is drawn"
        );
        assert!(sample::<u32>(&[], 0).is_none());
        assert_eq!((0..RATE * 100).filter(|e| mixes(*e)).count(), 100);
    }

    /// A case that mixes takes its entries by `pick`, and may hand it the
    /// number `mixes` took or another: either way every entry is picked,
    /// whatever the alphabet's length shares with [`RATE`].
    #[test]
    fn a_case_that_mixes_picks_every_entry() {
        for alphabet in [
            fs::alphabet().entries().len(),
            xml::alphabet().entries().len(),
        ] {
            assert!(alphabet > 1);
        }
        let xml = xml::alphabet();
        let states = fs::alphabet();
        let numbers = 0..RATE * 64;
        let same: BTreeSet<_> = numbers
            .clone()
            .filter(|e| mixes(*e))
            .map(|e| (xml.pick(e).value, states.pick(e).value))
            .map(|(how, state)| (format!("{how:?}"), format!("{state:?}")))
            .collect();
        let other: BTreeSet<_> = numbers
            .map(|e| format!("{:?}", xml.pick(e).value))
            .collect();
        let hows: BTreeSet<_> = same.iter().map(|(how, _)| how.clone()).collect();
        let picked_states: BTreeSet<_> = same.iter().map(|(_, state)| state.clone()).collect();
        assert_eq!(hows.len(), xml.entries().len(), "{hows:?}");
        assert_eq!(
            picked_states.len(),
            states.entries().len(),
            "{picked_states:?}"
        );
        assert_eq!(other.len(), xml.entries().len(), "{other:?}");
    }

    #[test]
    #[should_panic(expected = "has no entry for")]
    fn an_alphabet_missing_a_dimension_is_refused() {
        Alphabet::new(
            Kind::FsChange,
            vec![Entry {
                dimension: Dimension::Appears,
                value: 0u8,
                why: "",
            }],
        );
    }

    #[test]
    #[should_panic(expected = "of dimension")]
    fn an_alphabet_holding_another_kind_is_refused() {
        Alphabet::new(
            Kind::FsChange,
            vec![Entry {
                dimension: Dimension::Fifo,
                value: 0u8,
                why: "",
            }],
        );
    }

    #[test]
    fn drawn_values_carry_their_dimensions_through_map_and_zip() {
        let a = Drawn::of(&Entry {
            dimension: Dimension::Fifo,
            value: 1u8,
            why: "",
        });
        let b = Drawn::of(&Entry {
            dimension: Dimension::Backslash,
            value: "x",
            why: "",
        });
        let both = a.map(|v| v + 1).zip(b).zip(Drawn::plain(()));
        assert_eq!(both.value, ((2, "x"), ()));
        assert_eq!(
            both.hostile,
            BTreeSet::from([Dimension::Fifo, Dimension::Backslash])
        );
    }
}
