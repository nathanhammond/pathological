// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    path::Path,
};

static PATH_CORPUS: &[&str] = &[
    "",
    "foo",
    "foo/bar",
    "foo//bar",
    "foo/bar/baz",
    "foo/bar/./baz",
    "foo/bar/../baz",
    "../foo/bar/./../baz",
    "/foo",
    "/foo/bar",
    "/",
    "///",
    // ---
    // Windows-only paths
    // ---
    #[cfg(windows)]
    "foo\\bar",
    #[cfg(windows)]
    "\\foo\\bar",
    #[cfg(windows)]
    "C:\\foo",
    #[cfg(windows)]
    "C:foo\\bar",
    #[cfg(windows)]
    "C:\\foo\\..\\.\\bar",
    #[cfg(windows)]
    "\\\\server\\foo\\bar",
    #[cfg(windows)]
    "\\\\.\\C:\\foo\\bar.txt",
];

#[test]
fn test_borrow_eq_ord() {
    // AbsoluteSystemPathBuf implements Borrow<AbsoluteSystemPath> so equality and ordering comparisons should
    // match.
    for (idx, &path1) in PATH_CORPUS.iter().enumerate() {
        for &path2 in &PATH_CORPUS[idx..] {
            let borrowed1 = AbsoluteSystemPath::new(path1);
            let borrowed2 = AbsoluteSystemPath::new(path2);
            let owned1 = AbsoluteSystemPathBuf::from(path1);
            let owned2 = AbsoluteSystemPathBuf::from(path2);

            assert_eq!(
                borrowed1 == borrowed2,
                owned1 == owned2,
                "Eq impls match: {} == {}",
                borrowed1,
                borrowed2
            );
            assert_eq!(
                borrowed1.cmp(borrowed2),
                owned1.cmp(&owned2),
                "Ord impls match: {} and {}",
                borrowed1,
                borrowed2
            );

            // Also check against std paths.
            let std1 = Path::new(path1);
            let std2 = Path::new(path2);
            assert_eq!(
                borrowed1, std1,
                "Eq between Path and AbsoluteSystemPath: {}",
                borrowed1
            );
            assert_eq!(
                borrowed1 == borrowed2,
                std1 == std2,
                "Eq impl matches Path: {} == {}",
                borrowed1,
                borrowed2
            );
            assert_eq!(
                borrowed1.cmp(borrowed2),
                std1.cmp(std2),
                "Ord impl matches Path: {} and {}",
                borrowed1,
                borrowed2
            );
        }
    }
}

#[test]
fn test_borrow_hash() {
    // AbsoluteSystemPathBuf implements Borrow<AbsoluteSystemPath> so hash comparisons should match.
    fn hash_output(x: impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        x.hash(&mut hasher);
        hasher.finish()
    }

    for &path in PATH_CORPUS {
        let borrowed = AbsoluteSystemPath::new(path);
        let owned = AbsoluteSystemPathBuf::from(path);

        assert_eq!(
            hash_output(owned),
            hash_output(borrowed),
            "consistent Hash: {}",
            borrowed
        );
    }
}
