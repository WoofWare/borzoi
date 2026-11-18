//! fsc's reading of the arguments the `Fsc` task passes it
//! ([`borzoi_oracle_harness::fsc_args`]), as the name differentials use it.

pub use borzoi_oracle_harness::fsc_args::assembly_name_of;
use borzoi_oracle_harness::fsc_args::{FscArgsError, FscArguments};

fn why(error: FscArgsError) -> String {
    match error {
        FscArgsError::ResponseFile(line) => format!("a response file: {line:?}"),
    }
}

/// The file fsc compiles to, from the `Fsc` task's argument list.
pub fn fsc_output_path(args: &[String]) -> Result<Option<String>, String> {
    Ok(FscArguments::parse_arguments(args).map_err(why)?.output)
}

/// The file fsc compiles to, from the response file it reads.
pub fn fsc_output_path_in(file: &str) -> Result<Option<String>, String> {
    Ok(FscArguments::parse(file).map_err(why)?.output)
}

/// [`assembly_name_of`] the file [`fsc_output_path_in`] reads.
pub fn fsc_output_name_in(file: &str) -> Result<Option<String>, String> {
    Ok(fsc_output_path_in(file)?.map(|path| assembly_name_of(&path)))
}
