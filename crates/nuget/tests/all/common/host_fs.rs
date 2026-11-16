//! The test binary's whole-file reads, of fixtures and of what the oracle and
//! `dotnet restore` wrote, none of which is a FIFO. The crate's `clippy.toml`
//! bans the `std` calls that open a file (the library reads only through its
//! `regular_file` module), and allowing that lint wholesale in a test module
//! would also allow the child-process spawns it bans, so tests reach them
//! here.

#![allow(clippy::disallowed_methods)]

use std::path::Path;

pub fn read(path: impl AsRef<Path>) -> std::io::Result<Vec<u8>> {
    std::fs::read(path)
}

pub fn read_to_string(path: impl AsRef<Path>) -> std::io::Result<String> {
    std::fs::read_to_string(path)
}
