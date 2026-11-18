//! fsc's reading of the arguments the `Fsc` task passes it, for the
//! differentials that hold a name to the one fsc compiles to. Mirrors fsc's
//! own code (`CompilerOptions.fs`, `CompilerConfig.fs`);
//! `fsc_args_oracle_calibration` holds it to the files real compiling builds
//! write.

/// The file fsc compiles to, from the arguments the `Fsc` task passed it,
/// which it writes to a response file one per line: [`fsc_output_path_in`]
/// that file.
pub fn fsc_output_path(args: &[String]) -> Result<Option<String>, String> {
    fsc_output_path_in(&args.join("\n"))
}

/// The file fsc compiles to, from the response file it reads: fsc reads it a
/// line at a time (`\r\n`, `\r` or `\n`), drops blank lines and lines
/// starting `#`, trims the rest, and parses each as an option or a source
/// (`ResponseFile.parseFile`, `parseOption`). `-o:F` and `--out:F` (and
/// `/out:F`, `/o:F` where fsc takes a leading `/` for a switch) set the
/// output, and the last one read wins. `Ok(None)` when no line sets it.
/// `Err` when the reading is not certain: a line naming another response
/// file.
pub fn fsc_output_path_in(file: &str) -> Result<Option<String>, String> {
    let mut output = None;
    for raw in file.split("\r\n").flat_map(|l| l.split(['\r', '\n'])) {
        if raw.trim().is_empty() || raw.starts_with('#') {
            continue;
        }
        let line = raw.trim();
        if line.starts_with('@') {
            return Err(format!("a response file: {line:?}"));
        }
        let (token, argument) = parse_option(line);
        if (token == "o" || token == "out") && !argument.is_empty() {
            output = Some(argument);
        }
    }
    Ok(output)
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

/// [`assembly_name_of`] the file [`fsc_output_path`] reads.
pub fn fsc_output_name(args: &[String]) -> Result<Option<String>, String> {
    Ok(fsc_output_path(args)?.map(|path| assembly_name_of(&path)))
}

/// [`assembly_name_of`] the file [`fsc_output_path_in`] reads.
pub fn fsc_output_name_in(file: &str) -> Result<Option<String>, String> {
    Ok(fsc_output_path_in(file)?.map(|path| assembly_name_of(&path)))
}

/// fsc's `parseOption`: the option name a line carries (empty when it is not
/// an option) and everything after its first `:`.
fn parse_option(option: &str) -> (String, String) {
    let parts: Vec<&str> = option.split(':').collect();
    let argument = parts[1..].join(":");
    let chars: Vec<char> = option.chars().collect();
    let is_slash_opt =
        chars.first() == Some(&'/') && (chars.len() == 1 || !option[1..].contains('/'));
    let opt: String = if option.is_empty() || (chars[0] != '-' && chars[0] != '/') {
        String::new()
    } else if option != "--" {
        if chars.len() == 2 || is_slash_opt || (chars.len() >= 3 && chars[2] == ':') {
            chars[1..].iter().collect()
        } else if option.starts_with("--") {
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
        option.to_string()
    };
    let token = opt.split(':').next().unwrap_or("").to_string();
    (token, argument)
}
