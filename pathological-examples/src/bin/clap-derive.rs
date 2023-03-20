// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Parser;
use pathological::AbsoluteSystemPathBuf;

/// This example shows how a `AbsoluteSystemPath` can be used with `clap`'s derive-based argument parsing.
///
/// Using a `AbsoluteSystemPath` in argument parsing in this manner means that non-UTF-8 paths can be rejected
/// at the boundaries of your program.
///
/// To run this example, run `cargo run --package pathological-examples --bin clap-derive`.
#[derive(Parser)]
#[clap(rename_all = "kebab-case")]
struct Opt {
    /// Input file
    input: AbsoluteSystemPathBuf,

    /// Output file
    output: Option<AbsoluteSystemPathBuf>,
}

pub fn main() {
    // Parse the arguments.
    let opt = Opt::parse();

    // Print the input and output files.
    println!("input file: {}", opt.input);
    match &opt.output {
        Some(output) => println!("output file: {}", output),
        None => println!("no output file"),
    }
}
