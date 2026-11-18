//! The F# compiler's arguments as a typed value: the response file the
//! `Fsc` task hands fsc ([`crate::msbuild_oracle::fsc_args`] reads it off a
//! real build), parsed once, at the boundary, the way fsc reads it
//! (`CompilerOptions.fs`: `ResponseFile.parseFile`, `parseOption`;
//! `CompilerConfig.fs`: `DecideNames`).
//!
//! fsc reads the file a line at a time (`\r\n`, `\r` or `\n`), drops blank
//! lines and lines starting `#`, trims the rest, and takes a line for an
//! option when fsc's own rule does (a leading `-`, or a leading `/` it takes
//! for a switch), else for a source; a line shaped as an option that names
//! none it reports as an error, and so does the parse. An option whose value
//! fsc keeps as one (`-o:`, `--langversion:`, `--target:`) is honoured
//! last-wins; one it accumulates (`-r:`, `--define:`) keeps every occurrence,
//! in order. [`FscArguments::options`] holds every option line unvalidated:
//! one fsc does not know fails the compile, which [`crate::msbuild_oracle`]
//! reports as a build that did not succeed.
//! `fsc_args_oracle_calibration` (in `borzoi-msbuild`) holds this reading to
//! the files real compiling builds write.

/// One option line, as fsc splits it: its name (the token after the leading
/// `-`, `--` or `/`, up to the first `:`) and everything after that `:`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FscOption {
    pub name: String,
    pub argument: String,
}

/// What fsc is handed, by role. Every option line also stays in
/// [`Self::options`], in order, so a consumer needing one this type does not
/// name reads it there rather than re-reading the text.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FscArguments {
    /// The file fsc compiles to: the last `-o:`/`--out:`.
    pub output: Option<String>,
    /// `-r:`/`--reference:`, in order.
    pub references: Vec<String>,
    /// `-d:`/`--define:`, in order.
    pub defines: Vec<String>,
    /// The last `--langversion:`.
    pub lang_version: Option<String>,
    /// The target the last `--target:` or `-a` (`--target:library`) sets
    /// (`library`, `exe`, …).
    pub target: Option<String>,
    /// The lines fsc takes for sources, in order, their quotes trimmed as fsc
    /// trims them.
    pub sources: Vec<String>,
    /// Every option line, in order.
    pub options: Vec<FscOption>,
}

/// Why a response file cannot be read here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FscArgsError {
    /// A line names another response file (`@file`), whose contents fsc reads
    /// in its place.
    ResponseFile(String),
    /// A line fsc takes for an option but recognises as none (`--o:x`,
    /// `-out:x`), which it reports as an error rather than reading as a
    /// source.
    UnrecognisedOption(String),
}

impl FscArguments {
    /// Parse the response file text `file`.
    pub fn parse(file: &str) -> Result<FscArguments, FscArgsError> {
        let mut args = FscArguments::default();
        for raw in file.split("\r\n").flat_map(|l| l.split(['\r', '\n'])) {
            if raw.trim().is_empty() || raw.starts_with('#') {
                continue;
            }
            let line = raw.trim();
            if line.starts_with('@') {
                return Err(FscArgsError::ResponseFile(line.to_string()));
            }
            let Some(option) = parse_option(line) else {
                if line.starts_with('-') || is_slash_option(line) {
                    return Err(FscArgsError::UnrecognisedOption(line.to_string()));
                }
                // fsc trims a source's quotes after classifying the line
                // (`FileSystemUtils.trimQuotes`).
                args.sources.push(line.trim_matches([' ', '"']).to_string());
                continue;
            };
            let value = (!option.argument.is_empty()).then(|| option.argument.clone());
            match option.name.as_str() {
                "o" | "out" => args.output = value.or(args.output),
                "r" | "reference" => args.references.extend(value),
                "d" | "define" => args.defines.extend(value),
                "langversion" => args.lang_version = value.or(args.lang_version),
                "target" => args.target = value.or(args.target),
                "a" if option.argument.is_empty() => args.target = Some("library".to_string()),
                _ => {}
            }
            args.options.push(option);
        }
        Ok(args)
    }

    /// The parsed arguments of the `Fsc` task's argument list `args`, which
    /// it writes to the response file one per line.
    pub fn parse_arguments(args: &[String]) -> Result<FscArguments, FscArgsError> {
        FscArguments::parse(&args.join("\n"))
    }

    /// The assembly name FCS gives the output ([`assembly_name_of`]).
    pub fn assembly_name(&self) -> Option<String> {
        self.output.as_deref().map(assembly_name_of)
    }
}

/// The assembly name FCS gives an output file: its name up to its last dot
/// (`DecideNames`: `Path.GetFileNameWithoutExtension` of `Path.GetFileName`),
/// separators being `/` only, as on the hosts the differentials run on.
pub fn assembly_name_of(path: &str) -> String {
    let file = path.rsplit('/').next().unwrap_or(path);
    match file.rfind('.') {
        Some(dot) => file[..dot].to_string(),
        None => file.to_string(),
    }
}

/// fsc's `isSlashOpt`: a leading `/` with no other `/` after it, which fsc
/// reads as a switch.
fn is_slash_option(line: &str) -> bool {
    line.starts_with('/') && !line[1..].contains('/')
}

/// fsc's `parseOption`: the option `line` carries, or `None` when it carries
/// none: a source, or a line fsc rejects as an unrecognised option.
fn parse_option(line: &str) -> Option<FscOption> {
    let chars: Vec<char> = line.chars().collect();
    let argument = line.split(':').skip(1).collect::<Vec<_>>().join(":");
    let is_slash_opt = is_slash_option(line);
    let opt: String = if chars.is_empty() || (chars[0] != '-' && chars[0] != '/') {
        String::new()
    } else if line != "--" {
        if chars.len() == 2 || is_slash_opt || (chars.len() >= 3 && chars[2] == ':') {
            chars[1..].iter().collect()
        } else if line.starts_with("--") {
            if chars.len() >= 4 && chars[3] == ':' {
                String::new()
            } else if chars.len() > 3 {
                chars[2..].iter().collect()
            } else {
                String::new()
            }
        } else {
            String::new()
        }
    } else {
        line.to_string()
    };
    let name = opt.split(':').next().unwrap_or("").to_string();
    (!name.is_empty()).then_some(FscOption { name, argument })
}

#[cfg(test)]
mod tests {
    use super::{FscArgsError, FscArguments};

    fn name(lines: &[&str]) -> Result<Option<String>, FscArgsError> {
        Ok(FscArguments::parse(&lines.join("\n"))?.assembly_name())
    }

    #[test]
    fn output_follows_fsc() {
        assert_eq!(name(&["-o:obj/A.dll", "x.fs"]), Ok(Some("A".into())));
        assert_eq!(
            name(&["-o:obj/A.dll", "--out:B.x.dll"]),
            Ok(Some("B.x".into()))
        );
        assert_eq!(name(&["-o:obj/A.dll", "/out:B.dll"]), Ok(Some("B".into())));
        assert_eq!(
            name(&["-o:obj/A.dll", "/out:d/B.dll"]),
            Ok(Some("A".into()))
        );
        assert_eq!(name(&["-o:obj/A.dll", "/o:d/B.dll"]), Ok(Some("B".into())));
        assert!(name(&["-o:obj/A.dll", "--o:B.dll"]).is_err());
        assert_eq!(name(&["-o:obj/A.dll", "--OUT:B.dll"]), Ok(Some("A".into())));
        assert_eq!(
            name(&["-o:obj/A.dll", "#--out:B.dll"]),
            Ok(Some("A".into()))
        );
        assert_eq!(
            name(&["-o:obj/A.dll", " --out:B.dll"]),
            Ok(Some("B".into()))
        );
        assert_eq!(
            name(&["-o:obj/A.dll", "--warnon:1\n--out:B.dll"]),
            Ok(Some("B".into()))
        );
        assert_eq!(name(&["-o:obj/A.dll", "-o"]), Ok(Some("A".into())));
        assert_eq!(name(&["-o:obj/.dll"]), Ok(Some("".into())));
        assert_eq!(name(&["-o:obj/A..dll"]), Ok(Some("A.".into())));
        assert!(name(&["-o:obj/A.dll", "@x.rsp"]).is_err());
        assert!(name(&["-o:obj/A.dll", "-out:B.dll"]).is_err());
        assert_eq!(name(&["-o:obj/A.dll", "/abs/x.fs"]), Ok(Some("A".into())));
    }

    #[test]
    fn the_short_library_switch_sets_the_target() {
        let args = FscArguments::parse("--target:exe\n-a\nA.fs").unwrap();
        assert_eq!(args.target.as_deref(), Some("library"));
        let args = FscArguments::parse("-a\n--target:exe\nA.fs").unwrap();
        assert_eq!(args.target.as_deref(), Some("exe"));
    }

    #[test]
    fn roles_are_read_in_order() {
        let args = FscArguments::parse(
            "-o:obj/A.dll\n-r:/p/FSharp.Core.dll\n--define:DEBUG\n-r:/p/System.Runtime.dll\n\
             --langversion:preview\n--target:library\n--define:NET\nA.fs\nB.fs",
        )
        .unwrap();
        assert_eq!(
            args.references,
            ["/p/FSharp.Core.dll", "/p/System.Runtime.dll"]
        );
        assert_eq!(args.defines, ["DEBUG", "NET"]);
        assert_eq!(args.lang_version.as_deref(), Some("preview"));
        assert_eq!(args.target.as_deref(), Some("library"));
        assert_eq!(args.sources, ["A.fs", "B.fs"]);
        let quoted = FscArguments::parse("-o:A.dll\n\"B.fs\"").unwrap();
        assert_eq!(quoted.sources, ["B.fs"]);
        assert_eq!(args.options.len(), 7);
    }
}
