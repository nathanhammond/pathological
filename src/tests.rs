// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

// Test that all required impls exist.

use crate::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
use std::{
    borrow::Cow,
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
};

macro_rules! all_into {
    ($t:ty, $x:ident) => {
        test_into::<$t, AbsoluteSystemPathBuf>($x.clone());
        test_into::<$t, Box<AbsoluteSystemPath>>($x.clone());
        test_into::<$t, Arc<AbsoluteSystemPath>>($x.clone());
        test_into::<$t, Rc<AbsoluteSystemPath>>($x.clone());
        test_into::<$t, Cow<'_, AbsoluteSystemPath>>($x.clone());
        test_into::<$t, PathBuf>($x.clone());
        test_into::<$t, Box<Path>>($x.clone());
        test_into::<$t, Arc<Path>>($x.clone());
        test_into::<$t, Rc<Path>>($x.clone());
        test_into::<$t, Cow<'_, Path>>($x.clone());
    };
}

#[test]
fn test_borrowed_into() {
    let utf8_path = AbsoluteSystemPath::new("test/path");
    all_into!(&AbsoluteSystemPath, utf8_path);
}

#[test]
fn test_owned_into() {
    let utf8_path_buf = AbsoluteSystemPathBuf::from("test/path");
    all_into!(AbsoluteSystemPathBuf, utf8_path_buf);
}

fn test_into<T, U>(orig: T)
where
    T: Into<U>,
{
    let _ = orig.into();
}

#[cfg(path_buf_deref_mut)]
#[test]
fn test_deref_mut() {
    // This test is mostly for miri.
    let mut path_buf = AbsoluteSystemPathBuf::from("foobar");
    let _: &mut AbsoluteSystemPath = &mut path_buf;
}
