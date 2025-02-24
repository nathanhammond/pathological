// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use anyhow::Result;
use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;

/// This example demonstrates how to use a `AbsoluteSystemPath` in a `serde` struct.
///
/// With the `serde1` feature, `pathological` paths can be used as targets for `serde` serialization and
/// deserialization. (Note that serde itself [does not support] parsing non-UTF-8 `PathBuf`s, so
/// there is no loss of generality in switching to `AbsoluteSystemPathBuf` instances.)
///
/// To run this example, run `cargo run --package pathological-examples --bin serde`.
///
/// [does not support]: https://docs.rs/crate/serde/1.0.123/source/src/de/impls.rs
#[derive(Serialize, Deserialize)]
struct MyStruct {
    input: AbsoluteSystemPathBuf,
    output: AbsoluteSystemPathBuf,
}

/// A borrowed version of `MyStruct`, to demonstrate zero-copy deserialization to `AbsoluteSystemPath`s.
#[derive(Serialize, Deserialize)]
struct MyStructBorrowed<'a> {
    #[serde(borrow)]
    input: &'a AbsoluteSystemPath,
    // Note: This always deserializes to an owned string because of
    // https://github.com/serde-rs/serde/issues/1852. In the future we may add a `pathological-utils`
    // library with a `CowAbsoluteSystemPath<'a>` wrapper which can deserialize to the borrowed implementation
    // if possible.
    #[serde(borrow)]
    output: Cow<'a, AbsoluteSystemPath>,
}

static JSON_STR: &str = "{ \"input\": \"/foo/bar\", \"output\": \"/baz\\\\/quux\" }";
pub fn main() -> Result<()> {
    println!("*** json string: {}", JSON_STR);

    println!("*** Trying deserialize...");

    // Deserialize to MyStruct.
    let deserialized: MyStruct = serde_json::from_str(JSON_STR)?;
    assert_eq!(deserialized.input, "/foo/bar");
    assert_eq!(deserialized.output, "/baz\\/quux");

    println!("*** Trying serialize...");
    let serialized = serde_json::to_string_pretty(&deserialized)?;
    println!("serialize output: {}", serialized);

    println!("*** Trying zero-copy deserialize...");

    // Zero-copy deserialize to MyStructBorrowed.
    let zero_copy: MyStructBorrowed<'_> = serde_json::from_str(JSON_STR)?;
    assert_eq!(zero_copy.input, "/foo/bar");
    assert_eq!(zero_copy.output.as_str(), "/baz\\/quux");

    println!("*** Trying zero-copy serialize...");
    let serialized = serde_json::to_string_pretty(&zero_copy)?;
    println!("serialize output: {}", serialized);

    Ok(())
}
