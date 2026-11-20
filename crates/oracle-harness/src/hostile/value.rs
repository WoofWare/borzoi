//! Hostile values of an MSBuild property or of item metadata
//! ([`Kind::PropertyValue`]).
//!
//! A value is a template over the *plain* value the harness would have
//! written (`true` for a boolean property, `Demo` for a name), so a hostile
//! value still begins as the property's grammar expects and a reader that
//! checks only a prefix is caught.
//!
//! A value used as a file name or a path is also drawn from the name
//! alphabet ([`super::name::as_text`]); a harness that sets such a property
//! declares both kinds.

use std::sync::OnceLock;

use super::{Alphabet, Dimension, Entry, Kind};

/// The text of a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Text {
    /// This text, each `{}` standing for the plain value.
    Template(&'static str),
    /// The plain value, then this text this many times.
    Repeat(&'static str, usize),
}

/// When the value is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Write {
    /// It is the property's last write.
    Final,
    /// A later write puts the plain value back: whatever read the property
    /// in between has used the hostile one.
    ThenPlain,
}

/// A hostile value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    /// The text.
    pub text: Text,
    /// When it is written.
    pub write: Write,
}

impl Value {
    /// The value's text, for a property whose plain value is `plain`.
    pub fn render(&self, plain: &str) -> String {
        match self.text {
            Text::Template(template) => template.replace("{}", plain),
            Text::Repeat(unit, n) => {
                let mut out = String::with_capacity(plain.len() + unit.len() * n);
                out.push_str(plain);
                for _ in 0..n {
                    out.push_str(unit);
                }
                out
            }
        }
    }
}

const fn last(template: &'static str) -> Value {
    Value {
        text: Text::Template(template),
        write: Write::Final,
    }
}

const fn reset(template: &'static str) -> Value {
    Value {
        text: Text::Template(template),
        write: Write::ThenPlain,
    }
}

const TABLE: &[(Dimension, Value, &str)] = &[
    // Options, in each spelling fsc reads one.
    (
        Dimension::Option,
        last("--out:obj/Evil.dll"),
        "fsc's long output switch",
    ),
    (
        Dimension::Option,
        last("-o:Evil.dll"),
        "fsc's short output switch",
    ),
    (
        Dimension::Option,
        last("/o:obj/Evil.dll"),
        "the short switch behind a slash",
    ),
    (
        Dimension::Option,
        last("/out:obj/Evil.dll"),
        "the long switch behind a slash",
    ),
    (
        Dimension::Option,
        last("--out"),
        "the output switch with no value, which a parser that splits at the colon misreads",
    ),
    (
        Dimension::Option,
        last("-o:"),
        "the output switch with an empty value",
    ),
    (
        Dimension::Option,
        last("--o:Evil.dll"),
        "a switch fsc does not know, which a lenient reader records as a source",
    ),
    (
        Dimension::Option,
        last("-O"),
        "the optimisation switch, which a reader that lowers case takes for the output switch",
    ),
    (
        Dimension::Option,
        last("-a"),
        "fsc's shorthand for a library target",
    ),
    (
        Dimension::Option,
        last("--target:module"),
        "a netmodule target, whose output no assembly reader reads",
    ),
    (
        Dimension::Option,
        last("--refout:obj/Evil.dll"),
        "a second output, written beside the first",
    ),
    (
        Dimension::Option,
        last("--langversion:?"),
        "the switch that makes fsc print its versions and exit, which breaks a resident oracle's protocol",
    ),
    (
        Dimension::Option,
        last("--platform:anycpu32bitpreferred"),
        "a platform fsc rejects for a library",
    ),
    // An option behind padding.
    (
        Dimension::PaddedOption,
        last(" --out:obj/Evil.dll"),
        "an option behind a space",
    ),
    (
        Dimension::PaddedOption,
        last("{} --out:obj/Evil.dll"),
        "an option behind the plain value and a space",
    ),
    (
        Dimension::PaddedOption,
        last("{}\t-o:Evil.dll"),
        "an option behind a tab",
    ),
    // An option behind a line break.
    (
        Dimension::OptionAfterLineBreak,
        last("{}\n--out:obj/Evil.dll"),
        "an option on the response file's next line",
    ),
    (
        Dimension::OptionAfterLineBreak,
        last("{}\r-o:Evil.dll"),
        "an option behind a bare carriage return, which fsc's response-file reader splits at",
    ),
    (
        Dimension::OptionAfterLineBreak,
        last("{}\r\n/out:obj/Evil.dll"),
        "an option behind a carriage return and line feed",
    ),
    (
        Dimension::OptionAfterLineBreak,
        last("{}%0A--out%3Aobj/Evil.dll"),
        "the line break and the colon escaped, to be decoded on the way to the compiler",
    ),
    (
        Dimension::OptionAfterLineBreak,
        last("{}\u{85}--out:obj/Evil.dll"),
        "an option behind NEL, a line break to .NET's line reader",
    ),
    (
        Dimension::OptionAfterLineBreak,
        last("{}\u{2028}--out:obj/Evil.dll"),
        "an option behind the line separator",
    ),
    // Response files.
    (
        Dimension::ResponseFile,
        last("@evil.rsp"),
        "a response file",
    ),
    (
        Dimension::ResponseFile,
        last("{} @evil.rsp"),
        "a response file behind the plain value: one framework's build silently dropped its compile",
    ),
    (
        Dimension::ResponseFile,
        last("@"),
        "a response file with no name",
    ),
    // Quotes.
    (
        Dimension::QuotedArgument,
        last("--o\"\"ut:Evil.dll"),
        "quotes inside a switch's name, which the command line removes",
    ),
    (
        Dimension::QuotedArgument,
        last("--doc:\"API out docs.xml\""),
        "a quoted argument holding a space and the word `out`, which splitting at spaces breaks",
    ),
    (
        Dimension::QuotedArgument,
        last("\"--out:Evil.dll\""),
        "a whole option inside quotes",
    ),
    (
        Dimension::QuotedArgument,
        last("--doc:\"a\n--out:Evil.dll\""),
        "a line break inside a quoted argument",
    ),
    (
        Dimension::QuotedArgument,
        last("\"{}"),
        "a quote that never closes",
    ),
    // Properties the build sets for itself.
    (
        Dimension::SelfSetProperty,
        last("{}$(_MSBUILDTLENABLED)"),
        "set by MSBuild's command line to 0 or 1, and unset to an evaluation outside a build",
    ),
    (
        Dimension::SelfSetProperty,
        last("{}$(MSBuildLoadMicrosoftTargetsReadOnly)"),
        "set by MSBuild's command line",
    ),
    (
        Dimension::SelfSetProperty,
        last("{}$(MSBUILDUSESERVER)"),
        "set by the dotnet CLI when unset",
    ),
    (
        Dimension::SelfSetProperty,
        last("{}$(MSBuildBinaryLoggerEnabled)"),
        "set when a binary log is asked for: a build that reads it detects its own instrumentation",
    ),
    (
        Dimension::SelfSetProperty,
        last("{}$(MSBUILDLOGTASKINPUTS)"),
        "a variable an oracle sets to read task inputs, which the project can read back",
    ),
    (
        Dimension::SelfSetProperty,
        last("{}$(MSBuildIsRestoring)"),
        "a global of the restore's evaluation alone",
    ),
    (
        Dimension::SelfSetProperty,
        last("{}$(DOTNET_HOST_PATH)"),
        "set by the dotnet CLI to the muxer that runs the build",
    ),
    // Values that read the build itself.
    (
        Dimension::ReadsTheBuild,
        last("{}$([System.Environment]::CommandLine.Length)"),
        "the build's own command line: loggers and switches an oracle adds are visible in it",
    ),
    (
        Dimension::ReadsTheBuild,
        last("{}$([System.IO.Directory]::GetCurrentDirectory().Length)"),
        "the working directory, which a served evaluation does not know",
    ),
    (
        Dimension::ReadsTheBuild,
        last("{}$(MSBuildStartupDirectory.Length)"),
        "the directory MSBuild was started from",
    ),
    (
        Dimension::ReadsTheBuild,
        last("{}$([System.IO.File]::Exists('obj/project.assets.json'))"),
        "a file the restore writes, probed against the working directory: one value before a restore and another after",
    ),
    (
        Dimension::ReadsTheBuild,
        last("{}$([System.DateTime]::Now.Ticks)"),
        "the time: no two evaluations agree",
    ),
    (
        Dimension::ReadsTheBuild,
        last("{}$([System.Environment]::ProcessId)"),
        "the process: an oracle in another process cannot agree",
    ),
    // Padding.
    (Dimension::Padded, last(" {} "), "padded on both sides"),
    (Dimension::Padded, last("{} "), "a trailing space"),
    (Dimension::Padded, last("\t{}"), "a leading tab"),
    (Dimension::Padded, last("{}\n"), "a trailing line feed"),
    (
        Dimension::Padded,
        last("\n    {}\n  "),
        "the value on a line of its own, as an indented element is written",
    ),
    // Separators in what is used as one path component.
    (
        Dimension::PathSeparator,
        last("{}/x"),
        "a separator inside a name: the output lands in another directory",
    ),
    (
        Dimension::PathSeparator,
        last("tmp/{}"),
        "a directory prefix with no trailing separator of its own",
    ),
    (
        Dimension::PathSeparator,
        last("{}/"),
        "a trailing separator",
    ),
    (
        Dimension::PathSeparator,
        last("/{}"),
        "a leading separator: rooted",
    ),
    (
        Dimension::PathSeparator,
        last("{}\\x"),
        "a backslash, which MSBuild may rewrite to a separator",
    ),
    (
        Dimension::PathSeparator,
        last("../{}"),
        "the parent directory",
    ),
    // Blank values.
    (Dimension::Blank, last(""), "set, and empty"),
    (Dimension::Blank, last(" "), "one space"),
    (Dimension::Blank, last("\t\n"), "whitespace alone"),
    // Hostile, then put back.
    (
        Dimension::OverwrittenLater,
        reset("--out:obj/Evil.dll"),
        "an option the SDK captures into another property before the project resets it",
    ),
    (
        Dimension::OverwrittenLater,
        reset("{}%0A--out:obj/Evil.dll"),
        "an escaped line break and an option, reset later",
    ),
    (
        Dimension::OverwrittenLater,
        reset("{}$(_MSBUILDTLENABLED)"),
        "a self-set property read into a value that is reset later",
    ),
    // Spellings .NET's number parse reads at its edge.
    (
        Dimension::NumberSpelling,
        last("NaN"),
        "a number every comparison is false on",
    ),
    (
        Dimension::NumberSpelling,
        last("-Infinity"),
        "an infinity, which MSBuild refuses as a number",
    ),
    (
        Dimension::NumberSpelling,
        last("0x{}"),
        "hex, read as a 32-bit signed number",
    ),
    (
        Dimension::NumberSpelling,
        last("{}%00"),
        "a trailing NUL, escaped, which .NET reads as part of the number",
    ),
    (Dimension::NumberSpelling, last("+{}"), "a leading sign"),
    (Dimension::NumberSpelling, last("-0"), "negative zero"),
    (
        Dimension::NumberSpelling,
        last("1e3"),
        "an exponent, which MSBuild does not read",
    ),
    // Spellings at the edge of a version.
    (
        Dimension::VersionSpelling,
        last("{}.-0"),
        "a `-0` component, which .NET's version parse takes",
    ),
    (
        Dimension::VersionSpelling,
        last("1.2.3.4.5"),
        "five components",
    ),
    (
        Dimension::VersionSpelling,
        last("v{}.2"),
        "a leading `v`, which MSBuild's version functions strip",
    ),
    (
        Dimension::VersionSpelling,
        last("{}.0-beta"),
        "a prerelease suffix, which MSBuild's version functions drop",
    ),
    (
        Dimension::VersionSpelling,
        last("2147483648.0"),
        "a component past `int`",
    ),
    (
        Dimension::VersionSpelling,
        last(" {} . 2 "),
        "padded components",
    ),
    // Spellings at the edge of MSBuild's boolean vocabulary.
    (
        Dimension::BooleanSpelling,
        last("!false"),
        "a negated boolean",
    ),
    (
        Dimension::BooleanSpelling,
        last("ON"),
        "a boolean in another case",
    ),
    (
        Dimension::BooleanSpelling,
        last(" true"),
        "a padded boolean, which MSBuild does not trim",
    ),
    (
        Dimension::BooleanSpelling,
        last("yeſ"),
        "a boolean only ordinal-ignore-case folds",
    ),
    (
        Dimension::BooleanSpelling,
        last("false%00"),
        "a boolean padded with an escaped NUL, which a property function hands on as a NUL and `Boolean.TryParse` trims as padding",
    ),
    // List separators.
    (Dimension::ItemSeparator, last("{};{}"), "two items"),
    (Dimension::ItemSeparator, last(";"), "a separator alone"),
    (
        Dimension::ItemSeparator,
        last("{};;"),
        "empty items after the value",
    ),
    // Text that forms an item or metadata expression.
    (
        Dimension::ItemExpression,
        last("@"),
        "the start of an item list, completed by what follows",
    ),
    (
        Dimension::ItemExpression,
        last("(I->NoSuchFunction())"),
        "the rest of an item transform, after an `@` spliced before it",
    ),
    (Dimension::ItemExpression, last("@(I)"), "a whole item list"),
    (
        Dimension::ItemExpression,
        last("%(M)"),
        "a whole metadata reference",
    ),
    // Case folding outside ASCII.
    (
        Dimension::CaseFolding,
        last("É"),
        "an accented capital, which folds to its small letter",
    ),
    (
        Dimension::CaseFolding,
        last("{}ſ"),
        "a long s, which folds to `S`",
    ),
    // Long values.
    (
        Dimension::LongValue,
        Value {
            text: Text::Repeat("x", 65_536),
            write: Write::Final,
        },
        "a value of 64 KiB",
    ),
    (
        Dimension::LongValue,
        Value {
            text: Text::Repeat(";x", 20_000),
            write: Write::Final,
        },
        "a list of twenty thousand elements",
    ),
];

/// The alphabet of hostile property values.
pub fn alphabet() -> &'static Alphabet<Value> {
    static ALPHABET: OnceLock<Alphabet<Value>> = OnceLock::new();
    ALPHABET.get_or_init(|| {
        Alphabet::new(
            Kind::PropertyValue,
            TABLE
                .iter()
                .map(|(dimension, value, why)| Entry {
                    dimension: *dimension,
                    value: *value,
                    why,
                })
                .collect(),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_alphabet_covers_every_value_dimension() {
        assert_eq!(alphabet().kind(), Kind::PropertyValue);
    }

    #[test]
    fn a_value_renders_around_the_plain_one() {
        assert_eq!(
            last("{} --out:obj/Evil.dll").render("true"),
            "true --out:obj/Evil.dll"
        );
        let long = alphabet()
            .of(Dimension::LongValue)
            .map(|e| e.value.render("Demo"))
            .collect::<Vec<_>>();
        assert!(
            long.iter()
                .all(|v| v.starts_with("Demo") && v.len() > 40_000)
        );
    }

    #[test]
    fn only_the_overwritten_dimension_is_reset() {
        for e in alphabet().entries() {
            assert_eq!(
                e.value.write == Write::ThenPlain,
                e.dimension == Dimension::OverwrittenLater,
                "{}",
                e.why
            );
            // No rendered value is the plain one: each is hostile in itself.
            if e.dimension != Dimension::Blank {
                assert_ne!(e.value.render("Demo"), "Demo", "{}", e.why);
            }
        }
    }
}
