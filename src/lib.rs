// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![warn(missing_docs)]
#![cfg_attr(doc_cfg, feature(doc_cfg, doc_auto_cfg))]

//! UTF-8 encoded paths.
//!
//! `pathological` is an extension of the `std::path` module that adds new [`AbsoluteSystemPathBuf`] and [`AbsoluteSystemPath`]
//! types. These are like the standard library's [`PathBuf`] and [`Path`] types, except they are
//! guaranteed to only contain UTF-8 encoded data. Therefore, they expose the ability to get their
//! contents as strings, they implement `Display`, etc.
//!
//! The `std::path` types are not guaranteed to be valid UTF-8. This is the right decision for the standard library,
//! since it must be as general as possible. However, on all platforms, non-Unicode paths are vanishingly uncommon for a
//! number of reasons:
//! * Unicode won. There are still some legacy codebases that store paths in encodings like Shift-JIS, but most
//!   have been converted to Unicode at this point.
//! * Unicode is the common subset of supported paths across Windows and Unix platforms. (On Windows, Rust stores paths
//!   as [an extension to UTF-8](https://simonsapin.github.io/wtf-8/), and converts them to UTF-16 at Win32
//!   API boundaries.)
//! * There are already many systems, such as Cargo, that only support UTF-8 paths. If your own tool interacts with any such
//!   system, you can assume that paths are valid UTF-8 without creating any additional burdens on consumers.
//! * The ["makefile problem"](https://www.mercurial-scm.org/wiki/EncodingStrategy#The_.22makefile_problem.22)
//!   (which also applies to `Cargo.toml`, and any other metadata file that lists the names of other files) has *no general,
//!   cross-platform solution* in systems that support non-UTF-8 paths. However, restricting paths to UTF-8 eliminates
//!   this problem.
//!
//! Therefore, many programs that want to manipulate paths *do* assume they contain UTF-8 data, and convert them to `str`s
//! as  necessary. However, because this invariant is not encoded in the `Path` type, conversions such as
//! `path.to_str().unwrap()` need to be repeated again and again, creating a frustrating experience.
//!
//! Instead, `pathological` allows you to check that your paths are UTF-8 *once*, and then manipulate them
//! as valid UTF-8 from there on, avoiding repeated lossy and confusing conversions.

use std::{
    borrow::{Borrow, Cow},
    cmp::Ordering,
    convert::{Infallible, TryFrom, TryInto},
    error,
    ffi::{OsStr, OsString},
    fmt, fs,
    hash::{Hash, Hasher},
    io,
    iter::FusedIterator,
    ops::Deref,
    path::*,
    rc::Rc,
    str::FromStr,
    sync::Arc,
};

#[cfg(feature = "proptest1")]
mod proptest_impls;
#[cfg(feature = "serde1")]
mod serde_impls;
#[cfg(test)]
mod tests;

/// An owned, mutable UTF-8 path (akin to [`String`]).
///
/// This type provides methods like [`push`] and [`set_extension`] that mutate
/// the path in place. It also implements [`Deref`] to [`AbsoluteSystemPath`], meaning that
/// all methods on [`AbsoluteSystemPath`] slices are available on `AbsoluteSystemPathBuf` values as well.
///
/// [`push`]: AbsoluteSystemPathBuf::push
/// [`set_extension`]: AbsoluteSystemPathBuf::set_extension
///
/// # Examples
///
/// You can use [`push`] to build up a `AbsoluteSystemPathBuf` from
/// components:
///
/// ```
/// use pathological::AbsoluteSystemPathBuf;
///
/// let mut path = AbsoluteSystemPathBuf::new();
///
/// path.push(r"C:\");
/// path.push("windows");
/// path.push("system32");
///
/// path.set_extension("dll");
/// ```
///
/// However, [`push`] is best used for dynamic situations. This is a better way
/// to do this when you know all of the components ahead of time:
///
/// ```
/// use pathological::AbsoluteSystemPathBuf;
///
/// let path: AbsoluteSystemPathBuf = [r"C:\", "windows", "system32.dll"].iter().collect();
/// ```
///
/// We can still do better than this! Since these are all strings, we can use
/// `From::from`:
///
/// ```
/// use pathological::AbsoluteSystemPathBuf;
///
/// let path = AbsoluteSystemPathBuf::from(r"C:\windows\system32.dll");
/// ```
///
/// Which method works best depends on what kind of situation you're in.
// NB: Internal PathBuf must only contain utf8 data
#[derive(Clone, Default)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde1", serde(transparent))]
#[repr(transparent)]
pub struct AbsoluteSystemPathBuf(PathBuf);

impl AbsoluteSystemPathBuf {
    /// Allocates an empty `AbsoluteSystemPathBuf`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    ///
    /// let path = AbsoluteSystemPathBuf::new();
    /// ```
    #[must_use]
    pub fn new() -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(PathBuf::new())
    }

    /// Creates a new `AbsoluteSystemPathBuf` from a `PathBuf` containing valid UTF-8 characters.
    ///
    /// Errors with the original `PathBuf` if it is not valid UTF-8.
    ///
    /// For a version that returns a type that implements [`std::error::Error`], use the
    /// `TryFrom<PathBuf>` impl.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    /// use std::ffi::OsStr;
    /// # #[cfg(unix)]
    /// use std::os::unix::ffi::OsStrExt;
    /// use std::path::PathBuf;
    ///
    /// let unicode_path = PathBuf::from("/valid/unicode");
    /// AbsoluteSystemPathBuf::from_path_buf(unicode_path).expect("valid Unicode path succeeded");
    ///
    /// // Paths on Unix can be non-UTF-8.
    /// # #[cfg(unix)]
    /// let non_unicode_str = OsStr::from_bytes(b"\xFF\xFF\xFF");
    /// # #[cfg(unix)]
    /// let non_unicode_path = PathBuf::from(non_unicode_str);
    /// # #[cfg(unix)]
    /// AbsoluteSystemPathBuf::from_path_buf(non_unicode_path).expect_err("non-Unicode path failed");
    /// ```
    pub fn from_path_buf(path: PathBuf) -> Result<AbsoluteSystemPathBuf, PathBuf> {
        if path.is_absolute() {
            Ok(AbsoluteSystemPathBuf(path))
        } else {
            Err(path)
        }
    }

    /// Converts a `AbsoluteSystemPathBuf` to a [`PathBuf`].
    ///
    /// This is equivalent to the `From<AbsoluteSystemPathBuf> for PathBuf` impl, but may aid in type
    /// inference.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    /// use std::path::PathBuf;
    /// use std::ffi::OsStr;
    ///
    /// let utf8_path_buf = AbsoluteSystemPathBuf::from("/foo.txt");
    /// let std_path_buf = utf8_path_buf.into_std_path_buf();
    /// assert_eq!(std_path_buf.to_str(), Some("/foo.txt"));
    ///
    /// // Convert back to a AbsoluteSystemPathBuf.
    /// let new_utf8_path_buf = AbsoluteSystemPathBuf::from_path_buf(std_path_buf).unwrap();
    /// assert_eq!(new_utf8_path_buf, OsStr::new("/foo.txt"));
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_std_path_buf(self) -> PathBuf {
        self.into()
    }

    /// Creates a new `AbsoluteSystemPathBuf` with a given capacity used to create the internal [`PathBuf`].
    /// See [`with_capacity`] defined on [`PathBuf`].
    ///
    /// *Requires Rust 1.44 or newer.*
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    ///
    /// let mut path = AbsoluteSystemPathBuf::with_capacity(10);
    /// let capacity = path.capacity();
    ///
    /// // This push is done without reallocating
    /// path.push(r"C:\");
    ///
    /// assert_eq!(capacity, path.capacity());
    /// ```
    ///
    /// [`with_capacity`]: PathBuf::with_capacity
    #[cfg(path_buf_capacity)]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(PathBuf::with_capacity(capacity))
    }

    /// Coerces to a [`AbsoluteSystemPath`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let p = AbsoluteSystemPathBuf::from("/test");
    /// assert_eq!(AbsoluteSystemPath::new("/test"), p.as_path());
    /// ```
    #[must_use]
    pub fn as_path(&self) -> &AbsoluteSystemPath {
        // SAFETY: every AbsoluteSystemPathBuf constructor ensures that self is valid UTF-8
        unsafe { AbsoluteSystemPath::coerce_absolute_system_path(&self.0) }
    }

    /// Extends `self` with `path`.
    ///
    /// If `path` is absolute, it replaces the current path.
    ///
    /// On Windows:
    ///
    /// * if `path` has a root but no prefix (e.g., `\windows`), it
    ///   replaces everything except for the prefix (if any) of `self`.
    /// * if `path` has a prefix but no root, it replaces `self`.
    ///
    /// # Examples
    ///
    /// Pushing a relative path extends the existing path:
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    ///
    /// let mut path = AbsoluteSystemPathBuf::from("/tmp");
    /// path.push("file.bk");
    /// assert_eq!(path, AbsoluteSystemPathBuf::from("/tmp/file.bk"));
    /// ```
    ///
    /// Pushing an absolute path replaces the existing path:
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    ///
    /// let mut path = AbsoluteSystemPathBuf::from("/tmp");
    /// path.push("/etc");
    /// assert_eq!(path, AbsoluteSystemPathBuf::from("/etc"));
    /// ```
    pub fn push(&mut self, path: impl AsRef<AbsoluteSystemPath>) {
        self.0.push(&path.as_ref().0)
    }

    /// Truncates `self` to [`self.parent`].
    ///
    /// Returns `false` and does nothing if [`self.parent`] is [`None`].
    /// Otherwise, returns `true`.
    ///
    /// [`self.parent`]: AbsoluteSystemPath::parent
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let mut p = AbsoluteSystemPathBuf::from("/spirited/away.rs");
    ///
    /// p.pop();
    /// assert_eq!(AbsoluteSystemPath::new("/spirited"), p);
    /// p.pop();
    /// assert_eq!(AbsoluteSystemPath::new("/"), p);
    /// ```
    pub fn pop(&mut self) -> bool {
        self.0.pop()
    }

    /// Updates [`self.file_name`] to `file_name`.
    ///
    /// If [`self.file_name`] was [`None`], this is equivalent to pushing
    /// `file_name`.
    ///
    /// Otherwise it is equivalent to calling [`pop`] and then pushing
    /// `file_name`. The new path will be a sibling of the original path.
    /// (That is, it will have the same parent.)
    ///
    /// [`self.file_name`]: AbsoluteSystemPath::file_name
    /// [`pop`]: AbsoluteSystemPathBuf::pop
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    ///
    /// let mut buf = AbsoluteSystemPathBuf::from("/");
    /// assert_eq!(buf.file_name(), None);
    /// buf.set_file_name("bar");
    /// assert_eq!(buf, AbsoluteSystemPathBuf::from("/bar"));
    /// assert!(buf.file_name().is_some());
    /// buf.set_file_name("baz.txt");
    /// assert_eq!(buf, AbsoluteSystemPathBuf::from("/baz.txt"));
    /// ```
    pub fn set_file_name(&mut self, file_name: impl AsRef<str>) {
        self.0.set_file_name(file_name.as_ref())
    }

    /// Updates [`self.extension`] to `extension`.
    ///
    /// Returns `false` and does nothing if [`self.file_name`] is [`None`],
    /// returns `true` and updates the extension otherwise.
    ///
    /// If [`self.extension`] is [`None`], the extension is added; otherwise
    /// it is replaced.
    ///
    /// [`self.file_name`]: AbsoluteSystemPath::file_name
    /// [`self.extension`]: AbsoluteSystemPath::extension
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let mut p = AbsoluteSystemPathBuf::from("/feel/the");
    ///
    /// p.set_extension("force");
    /// assert_eq!(AbsoluteSystemPath::new("/feel/the.force"), p.as_path());
    ///
    /// p.set_extension("dark_side");
    /// assert_eq!(AbsoluteSystemPath::new("/feel/the.dark_side"), p.as_path());
    /// ```
    pub fn set_extension(&mut self, extension: impl AsRef<str>) -> bool {
        self.0.set_extension(extension.as_ref())
    }

    /// Consumes the `AbsoluteSystemPathBuf`, yielding its internal [`String`] storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    ///
    /// let p = AbsoluteSystemPathBuf::from("/the/head");
    /// let s = p.into_string();
    /// assert_eq!(s, "/the/head");
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_string(self) -> String {
        self.into_os_string().into_string().unwrap()
    }

    /// Consumes the `AbsoluteSystemPathBuf`, yielding its internal [`OsString`] storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPathBuf;
    /// use std::ffi::OsStr;
    ///
    /// let p = AbsoluteSystemPathBuf::from("/the/head");
    /// let s = p.into_os_string();
    /// assert_eq!(s, OsStr::new("/the/head"));
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_os_string(self) -> OsString {
        self.0.into_os_string()
    }

    /// Converts this `AbsoluteSystemPathBuf` into a [boxed](Box) [`AbsoluteSystemPath`].
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_boxed_path(self) -> Box<AbsoluteSystemPath> {
        let ptr = Box::into_raw(self.0.into_boxed_path()) as *mut AbsoluteSystemPath;
        // SAFETY:
        // * self is valid UTF-8
        // * ptr was constructed by consuming self so it represents an owned path
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from *mut Path to
        //   *mut AbsoluteSystemPath is valid
        unsafe { Box::from_raw(ptr) }
    }

    /// Invokes [`capacity`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.44 or newer.*
    ///
    /// [`capacity`]: PathBuf::capacity
    #[cfg(path_buf_capacity)]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Invokes [`clear`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.44 or newer.*
    ///
    /// [`clear`]: PathBuf::clear
    #[cfg(path_buf_capacity)]
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Invokes [`reserve`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.44 or newer.*
    ///
    /// [`reserve`]: PathBuf::reserve
    #[cfg(path_buf_capacity)]
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    /// Invokes [`try_reserve`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.63 or newer.*
    ///
    /// [`try_reserve`]: PathBuf::try_reserve
    #[cfg(try_reserve_2)]
    #[inline]
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    /// Invokes [`reserve_exact`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.44 or newer.*
    ///
    /// [`reserve_exact`]: PathBuf::reserve_exact
    #[cfg(path_buf_capacity)]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.0.reserve_exact(additional)
    }

    /// Invokes [`try_reserve_exact`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.63 or newer.*
    ///
    /// [`try_reserve_exact`]: PathBuf::try_reserve_exact
    #[cfg(try_reserve_2)]
    #[inline]
    pub fn try_reserve_exact(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve_exact(additional)
    }

    /// Invokes [`shrink_to_fit`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.44 or newer.*
    ///
    /// [`shrink_to_fit`]: PathBuf::shrink_to_fit
    #[cfg(path_buf_capacity)]
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }

    /// Invokes [`shrink_to`] on the underlying instance of [`PathBuf`].
    ///
    /// *Requires Rust 1.56 or newer.*
    ///
    /// [`shrink_to`]: PathBuf::shrink_to
    #[cfg(shrink_to)]
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity)
    }
}

impl Deref for AbsoluteSystemPathBuf {
    type Target = AbsoluteSystemPath;

    fn deref(&self) -> &AbsoluteSystemPath {
        self.as_path()
    }
}

/// *Requires Rust 1.68 or newer.*
#[cfg(path_buf_deref_mut)]
impl std::ops::DerefMut for AbsoluteSystemPathBuf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { AbsoluteSystemPath::coerce_absolute_system_path_mut(&mut self.0) }
    }
}

impl fmt::Debug for AbsoluteSystemPathBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl fmt::Display for AbsoluteSystemPathBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0.display(), f)
    }
}

impl<P: AsRef<AbsoluteSystemPath>> Extend<P> for AbsoluteSystemPathBuf {
    fn extend<I: IntoIterator<Item = P>>(&mut self, iter: I) {
        for path in iter {
            self.push(path);
        }
    }
}

/// A slice of a UTF-8 path (akin to [`str`]).
///
/// This type supports a number of operations for inspecting a path, including
/// breaking the path into its components (separated by `/` on Unix and by either
/// `/` or `\` on Windows), extracting the file name, determining whether the path
/// is absolute, and so on.
///
/// This is an *unsized* type, meaning that it must always be used behind a
/// pointer like `&` or [`Box`]. For an owned version of this type,
/// see [`AbsoluteSystemPathBuf`].
///
/// # Examples
///
/// ```
/// use std::ffi::OsStr;
/// use pathological::AbsoluteSystemPath;
///
/// // Note: this example does work on Windows
/// let path = AbsoluteSystemPath::new("./foo/bar.txt");
///
/// let parent = path.parent();
/// assert_eq!(parent, Some(AbsoluteSystemPath::new("./foo")));
///
/// let file_stem = path.file_stem();
/// assert_eq!(file_stem, Some(OsStr::new("bar")));
///
/// let extension = path.extension();
/// assert_eq!(extension, Some(OsStr::new("txt")));
/// ```
#[repr(transparent)]
pub struct AbsoluteSystemPath(Path);

impl AbsoluteSystemPath {
    /// Directly wraps a string slice as a `AbsoluteSystemPath` slice.
    ///
    /// This is a cost-free conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// AbsoluteSystemPath::new("foo.txt");
    /// ```
    ///
    /// You can create `AbsoluteSystemPath`s from `String`s, or even other `AbsoluteSystemPath`s:
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let string = String::from("foo.txt");
    /// let from_string = AbsoluteSystemPath::new(&string);
    /// let from_path = AbsoluteSystemPath::new(&from_string);
    /// assert_eq!(from_string, from_path);
    /// ```
    pub fn new(s: &(impl AsRef<OsStr> + ?Sized)) -> &AbsoluteSystemPath {
        let path = Path::new(s.as_ref());
        // SAFETY: s is a str which means it is always valid UTF-8
        unsafe { AbsoluteSystemPath::coerce_absolute_system_path(path) }
    }

    /// Converts a [`Path`] to a `AbsoluteSystemPath`.
    ///
    /// Returns `None` if the path is not valid UTF-8.
    ///
    /// For a version that returns a type that implements [`std::error::Error`], use the
    /// `TryFrom<&Path>` impl.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    /// use std::ffi::OsStr;
    /// # #[cfg(unix)]
    /// use std::os::unix::ffi::OsStrExt;
    /// use std::path::Path;
    ///
    /// let unicode_path = Path::new("/valid/unicode");
    /// AbsoluteSystemPath::from_path(unicode_path).expect("valid Unicode path succeeded");
    ///
    /// // Paths on Unix can be non-UTF-8.
    /// # #[cfg(unix)]
    /// let non_unicode_str = OsStr::from_bytes(b"\xFF\xFF\xFF");
    /// # #[cfg(unix)]
    /// let non_unicode_path = Path::new(non_unicode_str);
    /// # #[cfg(unix)]
    /// assert!(AbsoluteSystemPath::from_path(non_unicode_path).is_none(), "non-Unicode path failed");
    /// ```
    pub fn from_path(path: &Path) -> Option<&AbsoluteSystemPath> {
        if path.is_absolute() {
            Some(AbsoluteSystemPath::new(path.as_os_str()))
        } else {
            None
        }
    }

    /// Converts a `AbsoluteSystemPath` to a [`Path`].
    ///
    /// This is equivalent to the `AsRef<&Path> for &AbsoluteSystemPath` impl, but may aid in type inference.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    /// use std::path::Path;
    /// use std::ffi::OsStr;
    ///
    /// let utf8_path = AbsoluteSystemPath::new("/foo.txt");
    /// let std_path: &Path = utf8_path.as_std_path();
    /// assert_eq!(std_path.to_str(), Some("/foo.txt"));
    ///
    /// // Convert back to a AbsoluteSystemPath.
    /// let new_utf8_path = AbsoluteSystemPath::from_path(std_path).unwrap();
    /// assert_eq!(new_utf8_path, OsStr::new("/foo.txt"));
    /// ```
    pub fn as_std_path(&self) -> &Path {
        self.as_ref()
    }

    /// Yields the underlying [`OsStr`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let os_str = AbsoluteSystemPath::new("foo.txt").as_os_str();
    /// assert_eq!(os_str, std::ffi::OsStr::new("foo.txt"));
    /// ```
    #[must_use]
    pub fn as_os_str(&self) -> &OsStr {
        self.0.as_os_str()
    }

    /// Converts a `AbsoluteSystemPath` to an owned [`AbsoluteSystemPathBuf`].
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let path_buf = AbsoluteSystemPath::new("foo.txt").to_path_buf();
    /// assert_eq!(path_buf, AbsoluteSystemPathBuf::from("foo.txt"));
    /// ```
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    pub fn to_path_buf(&self) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(self.0.to_path_buf())
    }

    /// Returns `true` if the `AbsoluteSystemPath` is absolute, i.e., if it is independent of
    /// the current directory.
    ///
    /// * On Unix, a path is absolute if it starts with the root, so
    /// `is_absolute` and [`has_root`] are equivalent.
    ///
    /// * On Windows, a path is absolute if it has a prefix and starts with the
    /// root: `c:\windows` is absolute, while `c:temp` and `\temp` are not.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// assert!(!AbsoluteSystemPath::new("foo.txt").is_absolute());
    /// ```
    ///
    /// [`has_root`]: AbsoluteSystemPath::has_root
    #[must_use]
    pub fn is_absolute(&self) -> bool {
        self.0.is_absolute()
    }

    /// Returns `true` if the `AbsoluteSystemPath` is relative, i.e., not absolute.
    ///
    /// See [`is_absolute`]'s documentation for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// assert!(AbsoluteSystemPath::new("foo.txt").is_relative());
    /// ```
    ///
    /// [`is_absolute`]: AbsoluteSystemPath::is_absolute
    #[must_use]
    pub fn is_relative(&self) -> bool {
        self.0.is_relative()
    }

    /// Returns `true` if the `AbsoluteSystemPath` has a root.
    ///
    /// * On Unix, a path has a root if it begins with `/`.
    ///
    /// * On Windows, a path has a root if it:
    ///     * has no prefix and begins with a separator, e.g., `\windows`
    ///     * has a prefix followed by a separator, e.g., `c:\windows` but not `c:windows`
    ///     * has any non-disk prefix, e.g., `\\server\share`
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// assert!(AbsoluteSystemPath::new("/etc/passwd").has_root());
    /// ```
    #[must_use]
    pub fn has_root(&self) -> bool {
        self.0.has_root()
    }

    /// Returns the `Path` without its final component, if there is one.
    ///
    /// Returns [`None`] if the path terminates in a root or prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/foo/bar");
    /// let parent = path.parent().unwrap();
    /// assert_eq!(parent, AbsoluteSystemPath::new("/foo"));
    ///
    /// let grand_parent = parent.parent().unwrap();
    /// assert_eq!(grand_parent, AbsoluteSystemPath::new("/"));
    /// assert_eq!(grand_parent.parent(), None);
    /// ```
    #[must_use]
    pub fn parent(&self) -> Option<&AbsoluteSystemPath> {
        self.0.parent().map(|path| {
            // SAFETY: self is valid UTF-8, so parent is valid UTF-8 as well
            unsafe { AbsoluteSystemPath::coerce_absolute_system_path(path) }
        })
    }

    /// Produces an iterator over `AbsoluteSystemPath` and its ancestors.
    ///
    /// The iterator will yield the `AbsoluteSystemPath` that is returned if the [`parent`] method is used zero
    /// or more times. That means, the iterator will yield `&self`, `&self.parent().unwrap()`,
    /// `&self.parent().unwrap().parent().unwrap()` and so on. If the [`parent`] method returns
    /// [`None`], the iterator will do likewise. The iterator will always yield at least one value,
    /// namely `&self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let mut ancestors = AbsoluteSystemPath::new("/foo/bar").ancestors();
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("/foo/bar")));
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("/foo")));
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("/")));
    /// assert_eq!(ancestors.next(), None);
    ///
    /// let mut ancestors = AbsoluteSystemPath::new("../foo/bar").ancestors();
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("../foo/bar")));
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("../foo")));
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("..")));
    /// assert_eq!(ancestors.next(), Some(AbsoluteSystemPath::new("")));
    /// assert_eq!(ancestors.next(), None);
    /// ```
    ///
    /// [`parent`]: AbsoluteSystemPath::parent
    pub fn ancestors(&self) -> AbsoluteSystemPathAncestors<'_> {
        AbsoluteSystemPathAncestors(self.0.ancestors())
    }

    /// Returns the final component of the `AbsoluteSystemPath`, if there is one.
    ///
    /// If the path is a normal file, this is the file name. If it's the path of a directory, this
    /// is the directory name.
    ///
    /// Returns [`None`] if the path terminates in `..`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::OsStr;
    /// use pathological::AbsoluteSystemPath;
    ///
    /// assert_eq!(Some(OsStr::new("bin")), AbsoluteSystemPath::new("/usr/bin/").file_name());
    /// assert_eq!(Some(OsStr::new("foo.txt")), AbsoluteSystemPath::new("tmp/foo.txt").file_name());
    /// assert_eq!(Some(OsStr::new("foo.txt")), AbsoluteSystemPath::new("foo.txt/.").file_name());
    /// assert_eq!(Some(OsStr::new("foo.txt")), AbsoluteSystemPath::new("foo.txt/.//").file_name());
    /// assert_eq!(None, AbsoluteSystemPath::new("foo.txt/..").file_name());
    /// assert_eq!(None, AbsoluteSystemPath::new("/").file_name());
    /// ```
    #[must_use]
    pub fn file_name(&self) -> Option<&OsStr> {
        self.0.file_name()
    }

    /// Returns a path that, when joined onto `base`, yields `self`.
    ///
    /// # Errors
    ///
    /// If `base` is not a prefix of `self` (i.e., [`starts_with`]
    /// returns `false`), returns [`Err`].
    ///
    /// [`starts_with`]: AbsoluteSystemPath::starts_with
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let path = AbsoluteSystemPath::new("/test/haha/foo.txt");
    ///
    /// assert_eq!(path.strip_prefix("/"), Ok(AbsoluteSystemPath::new("test/haha/foo.txt")));
    /// assert_eq!(path.strip_prefix("/test"), Ok(AbsoluteSystemPath::new("haha/foo.txt")));
    /// assert_eq!(path.strip_prefix("/test/"), Ok(AbsoluteSystemPath::new("haha/foo.txt")));
    /// assert_eq!(path.strip_prefix("/test/haha/foo.txt"), Ok(AbsoluteSystemPath::new("")));
    /// assert_eq!(path.strip_prefix("/test/haha/foo.txt/"), Ok(AbsoluteSystemPath::new("")));
    ///
    /// assert!(path.strip_prefix("test").is_err());
    /// assert!(path.strip_prefix("/haha").is_err());
    ///
    /// let prefix = AbsoluteSystemPathBuf::from("/test/");
    /// assert_eq!(path.strip_prefix(prefix), Ok(AbsoluteSystemPath::new("haha/foo.txt")));
    /// ```
    pub fn strip_prefix(
        &self,
        base: impl AsRef<Path>,
    ) -> Result<&AbsoluteSystemPath, StripPrefixError> {
        self.0.strip_prefix(base).map(|path| {
            // SAFETY: self is valid UTF-8, and strip_prefix returns a part of self (or an empty
            // string), so it is valid UTF-8 as well.
            unsafe { AbsoluteSystemPath::coerce_absolute_system_path(path) }
        })
    }

    /// Determines whether `base` is a prefix of `self`.
    ///
    /// Only considers whole path components to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/etc/passwd");
    ///
    /// assert!(path.starts_with("/etc"));
    /// assert!(path.starts_with("/etc/"));
    /// assert!(path.starts_with("/etc/passwd"));
    /// assert!(path.starts_with("/etc/passwd/")); // extra slash is okay
    /// assert!(path.starts_with("/etc/passwd///")); // multiple extra slashes are okay
    ///
    /// assert!(!path.starts_with("/e"));
    /// assert!(!path.starts_with("/etc/passwd.txt"));
    ///
    /// assert!(!AbsoluteSystemPath::new("/etc/foo.rs").starts_with("/etc/foo"));
    /// ```
    #[must_use]
    pub fn starts_with(&self, base: impl AsRef<Path>) -> bool {
        self.0.starts_with(base)
    }

    /// Determines whether `child` is a suffix of `self`.
    ///
    /// Only considers whole path components to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/etc/resolv.conf");
    ///
    /// assert!(path.ends_with("resolv.conf"));
    /// assert!(path.ends_with("etc/resolv.conf"));
    /// assert!(path.ends_with("/etc/resolv.conf"));
    ///
    /// assert!(!path.ends_with("/resolv.conf"));
    /// assert!(!path.ends_with("conf")); // use .extension() instead
    /// ```
    #[must_use]
    pub fn ends_with(&self, base: impl AsRef<Path>) -> bool {
        self.0.ends_with(base)
    }

    /// Extracts the stem (non-extension) portion of [`self.file_name`].
    ///
    /// [`self.file_name`]: AbsoluteSystemPath::file_name
    ///
    /// The stem is:
    ///
    /// * [`None`], if there is no file name;
    /// * The entire file name if there is no embedded `.`;
    /// * The entire file name if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name before the final `.`
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// assert_eq!("foo", AbsoluteSystemPath::new("foo.rs").file_stem().unwrap());
    /// assert_eq!("foo.tar", AbsoluteSystemPath::new("foo.tar.gz").file_stem().unwrap());
    /// ```
    #[must_use]
    pub fn file_stem(&self) -> Option<&OsStr> {
        self.0.file_stem()
    }

    /// Extracts the extension of [`self.file_name`], if possible.
    ///
    /// The extension is:
    ///
    /// * [`None`], if there is no file name;
    /// * [`None`], if there is no embedded `.`;
    /// * [`None`], if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name after the final `.`
    ///
    /// [`self.file_name`]: AbsoluteSystemPath::file_name
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// assert_eq!("rs", AbsoluteSystemPath::new("foo.rs").extension().unwrap());
    /// assert_eq!("gz", AbsoluteSystemPath::new("foo.tar.gz").extension().unwrap());
    /// ```
    #[must_use]
    pub fn extension(&self) -> Option<&OsStr> {
        self.0.extension()
    }

    /// Creates an owned [`AbsoluteSystemPathBuf`] with `path` adjoined to `self`.
    ///
    /// See [`AbsoluteSystemPathBuf::push`] for more details on what it means to adjoin a path.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// assert_eq!(AbsoluteSystemPath::new("/etc").join("passwd"), AbsoluteSystemPathBuf::from("/etc/passwd"));
    /// ```
    #[must_use]
    pub fn join(&self, path: impl AsRef<AbsoluteSystemPath>) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(self.0.join(&path.as_ref().0))
    }

    /// Creates an owned [`PathBuf`] with `path` adjoined to `self`.
    ///
    /// See [`PathBuf::push`] for more details on what it means to adjoin a path.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    /// use std::path::PathBuf;
    ///
    /// assert_eq!(AbsoluteSystemPath::new("/etc").join_os("passwd"), PathBuf::from("/etc/passwd"));
    /// ```
    #[must_use]
    pub fn join_os(&self, path: impl AsRef<Path>) -> PathBuf {
        self.0.join(path)
    }

    /// Creates an owned [`AbsoluteSystemPathBuf`] like `self` but with the given file name.
    ///
    /// See [`AbsoluteSystemPathBuf::set_file_name`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let path = AbsoluteSystemPath::new("/tmp/foo.txt");
    /// assert_eq!(path.with_file_name("bar.txt"), AbsoluteSystemPathBuf::from("/tmp/bar.txt"));
    ///
    /// let path = AbsoluteSystemPath::new("/tmp");
    /// assert_eq!(path.with_file_name("var"), AbsoluteSystemPathBuf::from("/var"));
    /// ```
    #[must_use]
    pub fn with_file_name(&self, file_name: impl AsRef<str>) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(self.0.with_file_name(file_name.as_ref()))
    }

    /// Creates an owned [`AbsoluteSystemPathBuf`] like `self` but with the given extension.
    ///
    /// See [`AbsoluteSystemPathBuf::set_extension`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
    ///
    /// let path = AbsoluteSystemPath::new("foo.rs");
    /// assert_eq!(path.with_extension("txt"), AbsoluteSystemPathBuf::from("foo.txt"));
    ///
    /// let path = AbsoluteSystemPath::new("foo.tar.gz");
    /// assert_eq!(path.with_extension(""), AbsoluteSystemPathBuf::from("foo.tar"));
    /// assert_eq!(path.with_extension("xz"), AbsoluteSystemPathBuf::from("foo.tar.xz"));
    /// assert_eq!(path.with_extension("").with_extension("txt"), AbsoluteSystemPathBuf::from("foo.txt"));
    /// ```
    pub fn with_extension(&self, extension: impl AsRef<str>) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(self.0.with_extension(extension.as_ref()))
    }

    /// Produces an iterator over the [`AbsoluteSystemPathComponent`]s of the path.
    ///
    /// When parsing the path, there is a small amount of normalization:
    ///
    /// * Repeated separators are ignored, so `a/b` and `a//b` both have
    ///   `a` and `b` as components.
    ///
    /// * Occurrences of `.` are normalized away, except if they are at the
    ///   beginning of the path. For example, `a/./b`, `a/b/`, `a/b/.` and
    ///   `a/b` all have `a` and `b` as components, but `./a/b` starts with
    ///   an additional [`CurDir`] component.
    ///
    /// * A trailing slash is normalized away, `/a/b` and `/a/b/` are equivalent.
    ///
    /// Note that no other normalization takes place; in particular, `a/c`
    /// and `a/b/../c` are distinct, to account for the possibility that `b`
    /// is a symbolic link (so its parent isn't `a`).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::OsStr;
    /// use pathological::{AbsoluteSystemPathComponent, AbsoluteSystemPath};
    ///
    /// let mut components = AbsoluteSystemPath::new("/tmp/foo.txt").components();
    ///
    /// assert_eq!(components.next(), Some(AbsoluteSystemPathComponent::RootDir));
    /// assert_eq!(components.next(), Some(AbsoluteSystemPathComponent::Normal(OsStr::new("tmp"))));
    /// assert_eq!(components.next(), Some(AbsoluteSystemPathComponent::Normal(OsStr::new("foo.txt"))));
    /// assert_eq!(components.next(), None)
    /// ```
    ///
    /// [`CurDir`]: AbsoluteSystemPathComponent::CurDir
    pub fn components(&self) -> AbsoluteSystemPathComponents {
        AbsoluteSystemPathComponents(self.0.components())
    }

    /// Produces an iterator over the path's components viewed as [`str`]
    /// slices.
    ///
    /// For more information about the particulars of how the path is separated
    /// into components, see [`components`].
    ///
    /// [`components`]: AbsoluteSystemPath::components
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::OsStr;
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let mut it = AbsoluteSystemPath::new("/tmp/foo.txt").iter();
    /// assert_eq!(it.next(), Some(OsStr::new(&std::path::MAIN_SEPARATOR.to_string())));
    /// assert_eq!(it.next(), Some(OsStr::new("tmp")));
    /// assert_eq!(it.next(), Some(OsStr::new("foo.txt")));
    /// assert_eq!(it.next(), None)
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            inner: self.components(),
        }
    }

    /// Queries the file system to get information about a file, directory, etc.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file.
    ///
    /// This is an alias to [`fs::metadata`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/Minas/tirith");
    /// let metadata = path.metadata().expect("metadata call failed");
    /// println!("{:?}", metadata.file_type());
    /// ```
    pub fn metadata(&self) -> io::Result<fs::Metadata> {
        self.0.metadata()
    }

    /// Queries the metadata about a file without following symlinks.
    ///
    /// This is an alias to [`fs::symlink_metadata`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/Minas/tirith");
    /// let metadata = path.symlink_metadata().expect("symlink_metadata call failed");
    /// println!("{:?}", metadata.file_type());
    /// ```
    pub fn symlink_metadata(&self) -> io::Result<fs::Metadata> {
        self.0.symlink_metadata()
    }

    /// Returns the canonical, absolute form of the path with all intermediate
    /// components normalized and symbolic links resolved.
    ///
    /// This is an alias to [`fs::canonicalize`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    /// use std::path::PathBuf;
    ///
    /// let path = AbsoluteSystemPath::new("/foo/test/../test/bar.rs");
    /// assert_eq!(path.canonicalize().unwrap(), PathBuf::from("/foo/test/bar.rs"));
    /// ```
    pub fn canonicalize(&self) -> io::Result<AbsoluteSystemPathBuf> {
        self.0
            .canonicalize()
            .and_then(|path| path.try_into().map_err(FromPathBufError::into_io_error))
    }

    /// Reads a symbolic link, returning the file that the link points to.
    ///
    /// This returns a [`PathBuf`] because even if a symlink is valid Unicode, its target may not
    /// be. For a version that returns a [`AbsoluteSystemPathBuf`], see
    /// [`read_link_utf8`](Self::read_link_utf8).
    ///
    /// This is an alias to [`fs::read_link`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/laputa/sky_castle.rs");
    /// let path_link = path.read_link().expect("read_link call failed");
    /// ```
    pub fn read_link(&self) -> io::Result<PathBuf> {
        self.0.read_link()
    }

    /// Returns an iterator over the entries within a directory.
    ///
    /// The iterator will yield instances of [`io::Result`]`<`[`fs::DirEntry`]`>`. New
    /// errors may be encountered after an iterator is initially constructed.
    ///
    /// This is an alias to [`fs::read_dir`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("/laputa");
    /// for entry in path.read_dir().expect("read_dir call failed") {
    ///     if let Ok(entry) = entry {
    ///         println!("{:?}", entry.path());
    ///     }
    /// }
    /// ```
    pub fn read_dir(&self) -> io::Result<fs::ReadDir> {
        self.0.read_dir()
    }

    /// Returns `true` if the path points at an existing entity.
    ///
    /// Warning: this method may be error-prone, consider using [`try_exists()`] instead!
    /// It also has a risk of introducing time-of-check to time-of-use (TOCTOU) bugs.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file. In case of broken symbolic links this will return `false`.
    ///
    /// If you cannot access the directory containing the file, e.g., because of a
    /// permission error, this will return `false`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    /// assert!(!AbsoluteSystemPath::new("does_not_exist.txt").exists());
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`fs::metadata`].
    ///
    /// [`try_exists()`]: Self::try_exists
    #[must_use]
    pub fn exists(&self) -> bool {
        self.0.exists()
    }

    /// Returns `Ok(true)` if the path points at an existing entity.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file. In case of broken symbolic links this will return `Ok(false)`.
    ///
    /// As opposed to the [`exists()`] method, this one doesn't silently ignore errors
    /// unrelated to the path not existing. (E.g. it will return `Err(_)` in case of permission
    /// denied on some of the parent directories.)
    ///
    /// Note that while this avoids some pitfalls of the `exists()` method, it still can not
    /// prevent time-of-check to time-of-use (TOCTOU) bugs. You should only use it in scenarios
    /// where those bugs are not an issue.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    /// assert!(!AbsoluteSystemPath::new("does_not_exist.txt").try_exists().expect("Can't check existence of file does_not_exist.txt"));
    /// assert!(AbsoluteSystemPath::new("/root/secret_file.txt").try_exists().is_err());
    /// ```
    ///
    /// [`exists()`]: Self::exists
    #[inline]
    pub fn try_exists(&self) -> io::Result<bool> {
        // Note: this block is written this way rather than with a pattern guard to appease Rust
        // 1.34.
        match fs::metadata(self) {
            Ok(_) => Ok(true),
            Err(error) => {
                if error.kind() == io::ErrorKind::NotFound {
                    Ok(false)
                } else {
                    Err(error)
                }
            }
        }
    }

    /// Returns `true` if the path exists on disk and is pointing at a regular file.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file. In case of broken symbolic links this will return `false`.
    ///
    /// If you cannot access the directory containing the file, e.g., because of a
    /// permission error, this will return `false`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    /// assert_eq!(AbsoluteSystemPath::new("./is_a_directory/").is_file(), false);
    /// assert_eq!(AbsoluteSystemPath::new("a_file.txt").is_file(), true);
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`fs::metadata`] and handle its [`Result`]. Then call
    /// [`fs::Metadata::is_file`] if it was [`Ok`].
    ///
    /// When the goal is simply to read from (or write to) the source, the most
    /// reliable way to test the source can be read (or written to) is to open
    /// it. Only using `is_file` can break workflows like `diff <( prog_a )` on
    /// a Unix-like system for example. See [`fs::File::open`] or
    /// [`fs::OpenOptions::open`] for more information.
    #[must_use]
    pub fn is_file(&self) -> bool {
        self.0.is_file()
    }

    /// Returns `true` if the path exists on disk and is pointing at a directory.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file. In case of broken symbolic links this will return `false`.
    ///
    /// If you cannot access the directory containing the file, e.g., because of a
    /// permission error, this will return `false`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use pathological::AbsoluteSystemPath;
    /// assert_eq!(AbsoluteSystemPath::new("./is_a_directory/").is_dir(), true);
    /// assert_eq!(AbsoluteSystemPath::new("a_file.txt").is_dir(), false);
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`fs::metadata`] and handle its [`Result`]. Then call
    /// [`fs::Metadata::is_dir`] if it was [`Ok`].
    #[must_use]
    pub fn is_dir(&self) -> bool {
        self.0.is_dir()
    }

    /// Returns `true` if the path exists on disk and is pointing at a symbolic link.
    ///
    /// This function will not traverse symbolic links.
    /// In case of a broken symbolic link this will also return true.
    ///
    /// If you cannot access the directory containing the file, e.g., because of a
    /// permission error, this will return false.
    ///
    /// # Examples
    ///
    #[cfg_attr(unix, doc = "```no_run")]
    #[cfg_attr(not(unix), doc = "```ignore")]
    /// use pathological::AbsoluteSystemPath;
    /// use std::os::unix::fs::symlink;
    ///
    /// let link_path = AbsoluteSystemPath::new("link");
    /// symlink("/origin_does_not_exist/", link_path).unwrap();
    /// assert_eq!(link_path.is_symlink(), true);
    /// assert_eq!(link_path.exists(), false);
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`AbsoluteSystemPath::symlink_metadata`] and handle its [`Result`]. Then call
    /// [`fs::Metadata::is_symlink`] if it was [`Ok`].
    #[must_use]
    pub fn is_symlink(&self) -> bool {
        self.symlink_metadata()
            .map(|m| m.file_type().is_symlink())
            .unwrap_or(false)
    }

    /// Converts a `Box<AbsoluteSystemPath>` into a [`AbsoluteSystemPathBuf`] without copying or allocating.
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_path_buf(self: Box<AbsoluteSystemPath>) -> AbsoluteSystemPathBuf {
        let ptr = Box::into_raw(self) as *mut Path;
        // SAFETY:
        // * self is valid UTF-8
        // * ptr was constructed by consuming self so it represents an owned path.
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from a *mut AbsoluteSystemPath to a
        //   *mut Path is valid.
        let boxed_path = unsafe { Box::from_raw(ptr) };
        AbsoluteSystemPathBuf(boxed_path.into_path_buf())
    }

    // invariant: Path must be guaranteed to be utf-8 data
    unsafe fn coerce_absolute_system_path(path: &Path) -> &AbsoluteSystemPath {
        // SAFETY: AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from a
        // *const Path to a *const AbsoluteSystemPath is valid.
        &*(path as *const Path as *const AbsoluteSystemPath)
    }

    #[cfg(path_buf_deref_mut)]
    unsafe fn coerce_absolute_system_path_mut(path: &mut Path) -> &mut AbsoluteSystemPath {
        &mut *(path as *mut Path as *mut AbsoluteSystemPath)
    }
}

impl Clone for Box<AbsoluteSystemPath> {
    fn clone(&self) -> Self {
        let boxed: Box<Path> = self.0.into();
        let ptr = Box::into_raw(boxed) as *mut AbsoluteSystemPath;
        // SAFETY:
        // * self is valid UTF-8
        // * ptr was created by consuming a Box<Path> so it represents an rced pointer
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from *mut Path to
        //   *mut AbsoluteSystemPath is valid
        unsafe { Box::from_raw(ptr) }
    }
}

impl fmt::Display for AbsoluteSystemPath {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0.display(), f)
    }
}

impl fmt::Debug for AbsoluteSystemPath {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

/// An iterator over [`AbsoluteSystemPath`] and its ancestors.
///
/// This `struct` is created by the [`ancestors`] method on [`AbsoluteSystemPath`].
/// See its documentation for more.
///
/// # Examples
///
/// ```
/// use pathological::AbsoluteSystemPath;
///
/// let path = AbsoluteSystemPath::new("/foo/bar");
///
/// for ancestor in path.ancestors() {
///     println!("{}", ancestor);
/// }
/// ```
///
/// [`ancestors`]: AbsoluteSystemPath::ancestors
#[derive(Copy, Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[repr(transparent)]
pub struct AbsoluteSystemPathAncestors<'a>(Ancestors<'a>);

impl<'a> fmt::Debug for AbsoluteSystemPathAncestors<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<'a> Iterator for AbsoluteSystemPathAncestors<'a> {
    type Item = &'a AbsoluteSystemPath;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|path| {
            // SAFETY: AbsoluteSystemPathAncestors was constructed from a AbsoluteSystemPath, so it is guaranteed to
            // be valid UTF-8
            unsafe { AbsoluteSystemPath::coerce_absolute_system_path(path) }
        })
    }
}

impl<'a> FusedIterator for AbsoluteSystemPathAncestors<'a> {}

/// An iterator over the [`AbsoluteSystemPathComponent`]s of a [`AbsoluteSystemPath`].
///
/// This `struct` is created by the [`components`] method on [`AbsoluteSystemPath`].
/// See its documentation for more.
///
/// # Examples
///
/// ```
/// use pathological::AbsoluteSystemPath;
///
/// let path = AbsoluteSystemPath::new("/tmp/foo/bar.txt");
///
/// for component in path.components() {
///     println!("{:?}", component);
/// }
/// ```
///
/// [`components`]: AbsoluteSystemPath::components
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct AbsoluteSystemPathComponents<'a>(Components<'a>);

impl<'a> AbsoluteSystemPathComponents<'a> {
    /// Extracts a slice corresponding to the portion of the path remaining for iteration.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let mut components = AbsoluteSystemPath::new("/tmp/foo/bar.txt").components();
    /// components.next();
    /// components.next();
    ///
    /// assert_eq!(AbsoluteSystemPath::new("foo/bar.txt"), components.as_path());
    /// ```
    #[must_use]
    pub fn as_path(&self) -> &'a AbsoluteSystemPath {
        // SAFETY: AbsoluteSystemPathComponents was constructed from a AbsoluteSystemPath, so it is guaranteed to be valid
        // UTF-8
        unsafe { AbsoluteSystemPath::coerce_absolute_system_path(self.0.as_path()) }
    }
}

impl<'a> Iterator for AbsoluteSystemPathComponents<'a> {
    type Item = AbsoluteSystemPathComponent<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|component| {
            // SAFETY: AbsoluteSystemPathComponent was constructed from a AbsoluteSystemPath, so it is guaranteed to be
            // valid UTF-8
            unsafe { AbsoluteSystemPathComponent::new(component) }
        })
    }
}

impl<'a> FusedIterator for AbsoluteSystemPathComponents<'a> {}

impl<'a> DoubleEndedIterator for AbsoluteSystemPathComponents<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|component| {
            // SAFETY: AbsoluteSystemPathComponent was constructed from a AbsoluteSystemPath, so it is guaranteed to be
            // valid UTF-8
            unsafe { AbsoluteSystemPathComponent::new(component) }
        })
    }
}

impl<'a> fmt::Debug for AbsoluteSystemPathComponents<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl AsRef<AbsoluteSystemPath> for AbsoluteSystemPathComponents<'_> {
    fn as_ref(&self) -> &AbsoluteSystemPath {
        self.as_path()
    }
}

impl AsRef<Path> for AbsoluteSystemPathComponents<'_> {
    fn as_ref(&self) -> &Path {
        self.as_path().as_ref()
    }
}

impl AsRef<OsStr> for AbsoluteSystemPathComponents<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_path().as_os_str()
    }
}

/// An iterator over the [`AbsoluteSystemPathComponent`]s of a [`AbsoluteSystemPath`], as [`str`] slices.
///
/// This `struct` is created by the [`iter`] method on [`AbsoluteSystemPath`].
/// See its documentation for more.
///
/// [`iter`]: AbsoluteSystemPath::iter
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a> {
    inner: AbsoluteSystemPathComponents<'a>,
}

impl fmt::Debug for Iter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct DebugHelper<'a>(&'a AbsoluteSystemPath);

        impl fmt::Debug for DebugHelper<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_list().entries(self.0.iter()).finish()
            }
        }

        f.debug_tuple("Iter")
            .field(&DebugHelper(self.as_path()))
            .finish()
    }
}

impl<'a> Iter<'a> {
    /// Extracts a slice corresponding to the portion of the path remaining for iteration.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let mut iter = AbsoluteSystemPath::new("/tmp/foo/bar.txt").iter();
    /// iter.next();
    /// iter.next();
    ///
    /// assert_eq!(AbsoluteSystemPath::new("foo/bar.txt"), iter.as_path());
    /// ```
    #[must_use]
    pub fn as_path(&self) -> &'a AbsoluteSystemPath {
        self.inner.as_path()
    }
}

impl AsRef<AbsoluteSystemPath> for Iter<'_> {
    fn as_ref(&self) -> &AbsoluteSystemPath {
        self.as_path()
    }
}

impl AsRef<Path> for Iter<'_> {
    fn as_ref(&self) -> &Path {
        self.as_path().as_ref()
    }
}

impl AsRef<OsStr> for Iter<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_path().as_os_str()
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a OsStr;

    fn next(&mut self) -> Option<&'a OsStr> {
        self.inner.next().map(|component| component.as_os_str())
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<&'a OsStr> {
        self.inner
            .next_back()
            .map(|component| component.as_os_str())
    }
}

impl FusedIterator for Iter<'_> {}

/// A single component of a path.
///
/// A `AbsoluteSystemPathComponent` roughly corresponds to a substring between path separators
/// (`/` or `\`).
///
/// This `enum` is created by iterating over [`AbsoluteSystemPathComponents`], which in turn is
/// created by the [`components`](AbsoluteSystemPath::components) method on [`AbsoluteSystemPath`].
///
/// # Examples
///
/// ```rust
/// use pathological::{AbsoluteSystemPathComponent, AbsoluteSystemPath};
///
/// let path = AbsoluteSystemPath::new("/tmp/foo/bar.txt");
/// let components = path.components().collect::<Vec<_>>();
/// assert_eq!(&components, &[
///     AbsoluteSystemPathComponent::RootDir,
///     AbsoluteSystemPathComponent::Normal("tmp".as_ref()),
///     AbsoluteSystemPathComponent::Normal("foo".as_ref()),
///     AbsoluteSystemPathComponent::Normal("bar.txt".as_ref()),
/// ]);
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AbsoluteSystemPathComponent<'a> {
    /// A Windows path prefix, e.g., `C:` or `\\server\share`.
    ///
    /// There is a large variety of prefix types, see [`AbsoluteSystemPathPrefix`]'s documentation
    /// for more.
    ///
    /// Does not occur on Unix.
    Prefix(AbsoluteSystemPathPrefixComponent<'a>),

    /// The root directory component, appears after any prefix and before anything else.
    ///
    /// It represents a separator that designates that a path starts from root.
    RootDir,

    /// A reference to the current directory, i.e., `.`.
    CurDir,

    /// A reference to the parent directory, i.e., `..`.
    ParentDir,

    /// A normal component, e.g., `a` and `b` in `a/b`.
    ///
    /// This variant is the most common one, it represents references to files
    /// or directories.
    Normal(&'a OsStr),
}

impl<'a> AbsoluteSystemPathComponent<'a> {
    unsafe fn new(component: Component<'a>) -> AbsoluteSystemPathComponent<'a> {
        match component {
            Component::Prefix(prefix) => {
                AbsoluteSystemPathComponent::Prefix(AbsoluteSystemPathPrefixComponent(prefix))
            }
            Component::RootDir => AbsoluteSystemPathComponent::RootDir,
            Component::CurDir => AbsoluteSystemPathComponent::CurDir,
            Component::ParentDir => AbsoluteSystemPathComponent::ParentDir,
            Component::Normal(s) => AbsoluteSystemPathComponent::Normal(s),
        }
    }

    /// Extracts the underlying [`OsStr`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use pathological::AbsoluteSystemPath;
    ///
    /// let path = AbsoluteSystemPath::new("./tmp/foo/bar.txt");
    /// let components: Vec<_> = path.components().map(|comp| comp.as_os_str()).collect();
    /// assert_eq!(&components, &[".", "tmp", "foo", "bar.txt"]);
    /// ```
    #[must_use]
    pub fn as_os_str(&self) -> &'a OsStr {
        match *self {
            AbsoluteSystemPathComponent::Prefix(prefix) => prefix.as_os_str(),
            AbsoluteSystemPathComponent::RootDir => Component::RootDir.as_os_str(),
            AbsoluteSystemPathComponent::CurDir => Component::CurDir.as_os_str(),
            AbsoluteSystemPathComponent::ParentDir => Component::ParentDir.as_os_str(),
            AbsoluteSystemPathComponent::Normal(s) => OsStr::new(s),
        }
    }
}

impl<'a> fmt::Debug for AbsoluteSystemPathComponent<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_os_str(), f)
    }
}

impl AsRef<Path> for AbsoluteSystemPathComponent<'_> {
    fn as_ref(&self) -> &Path {
        self.as_os_str().as_ref()
    }
}

impl AsRef<OsStr> for AbsoluteSystemPathComponent<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

/// Windows path prefixes, e.g., `C:` or `\\server\share`.
///
/// Windows uses a variety of path prefix styles, including references to drive
/// volumes (like `C:`), network shared folders (like `\\server\share`), and
/// others. In addition, some path prefixes are "verbatim" (i.e., prefixed with
/// `\\?\`), in which case `/` is *not* treated as a separator and essentially
/// no normalization is performed.
///
/// # Examples
///
/// ```
/// use std::ffi::OsStr;
/// use pathological::{AbsoluteSystemPathComponent, AbsoluteSystemPath, AbsoluteSystemPathPrefix};
/// use pathological::AbsoluteSystemPathPrefix::*;
///
/// fn get_path_prefix(s: &str) -> AbsoluteSystemPathPrefix {
///     let path = AbsoluteSystemPath::new(s);
///     match path.components().next().unwrap() {
///         AbsoluteSystemPathComponent::Prefix(prefix_component) => prefix_component.kind(),
///         _ => panic!(),
///     }
/// }
///
/// # if cfg!(windows) {
/// assert_eq!(Verbatim(OsStr::new("pictures")), get_path_prefix(r"\\?\pictures\kittens"));
/// assert_eq!(VerbatimUNC(OsStr::new("server"), OsStr::new("share")), get_path_prefix(r"\\?\UNC\server\share"));
/// assert_eq!(VerbatimDisk(b'C'), get_path_prefix(r"\\?\c:\"));
/// assert_eq!(DeviceNS(OsStr::new("BrainInterface")), get_path_prefix(r"\\.\BrainInterface"));
/// assert_eq!(UNC(OsStr::new("server"), OsStr::new("share")), get_path_prefix(r"\\server\share"));
/// assert_eq!(Disk(b'C'), get_path_prefix(r"C:\Users\Rust\Pictures\Ferris"));
/// # }
/// ```
#[derive(Copy, Clone, Debug, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub enum AbsoluteSystemPathPrefix<'a> {
    /// Verbatim prefix, e.g., `\\?\cat_pics`.
    ///
    /// Verbatim prefixes consist of `\\?\` immediately followed by the given
    /// component.
    Verbatim(&'a OsStr),

    /// Verbatim prefix using Windows' _**U**niform **N**aming **C**onvention_,
    /// e.g., `\\?\UNC\server\share`.
    ///
    /// Verbatim UNC prefixes consist of `\\?\UNC\` immediately followed by the
    /// server's hostname and a share name.
    VerbatimUNC(&'a OsStr, &'a OsStr),

    /// Verbatim disk prefix, e.g., `\\?\C:`.
    ///
    /// Verbatim disk prefixes consist of `\\?\` immediately followed by the
    /// drive letter and `:`.
    VerbatimDisk(u8),

    /// Device namespace prefix, e.g., `\\.\COM42`.
    ///
    /// Device namespace prefixes consist of `\\.\` immediately followed by the
    /// device name.&'a (impl AsRef<OsStr>)
    DeviceNS(&'a OsStr),

    /// Prefix using Windows' _**U**niform **N**aming **C**onvention_, e.g.
    /// `\\server\share`.
    ///
    /// UNC prefixes consist of the server's hostname and a share name.
    UNC(&'a OsStr, &'a OsStr),

    /// Prefix `C:` for the given disk drive.
    Disk(u8),
}

impl<'a> AbsoluteSystemPathPrefix<'a> {
    /// Determines if the prefix is verbatim, i.e., begins with `\\?\`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::OsStr;
    /// use pathological::AbsoluteSystemPathPrefix::*;
    ///
    /// assert!(Verbatim(OsStr::new("pictures")).is_verbatim());
    /// assert!(VerbatimUNC(OsStr::new("server"), OsStr::new("share")).is_verbatim());
    /// assert!(VerbatimDisk(b'C').is_verbatim());
    /// assert!(!DeviceNS(OsStr::new("BrainInterface")).is_verbatim());
    /// assert!(!UNC(OsStr::new("server"), OsStr::new("share")).is_verbatim());
    /// assert!(!Disk(b'C').is_verbatim());
    /// ```
    #[must_use]
    pub fn is_verbatim(&self) -> bool {
        use AbsoluteSystemPathPrefix::*;
        match self {
            Verbatim(_) | VerbatimDisk(_) | VerbatimUNC(..) => true,
            _ => false,
        }
    }
}

/// A structure wrapping a Windows path prefix as well as its unparsed string
/// representation.
///
/// In addition to the parsed [`AbsoluteSystemPathPrefix`] information returned by [`kind`],
/// `AbsoluteSystemPathPrefixComponent` also holds the raw and unparsed [`str`] slice,
/// returned by [`as_str`].
///
/// Instances of this `struct` can be obtained by matching against the
/// [`Prefix` variant] on [`AbsoluteSystemPathComponent`].
///
/// Does not occur on Unix.
///
/// # Examples
///
/// ```
/// # if cfg!(windows) {
/// use pathological::{AbsoluteSystemPathComponent, AbsoluteSystemPath, AbsoluteSystemPathPrefix};
/// use std::ffi::OsStr;
///
/// let path = AbsoluteSystemPath::new(r"c:\you\later\");
/// match path.components().next().unwrap() {
///     AbsoluteSystemPathComponent::Prefix(prefix_component) => {
///         assert_eq!(AbsoluteSystemPathPrefix::Disk(b'C'), prefix_component.kind());
///         assert_eq!(OsStr::new("c:"), prefix_component.as_os_str());
///     }
///     _ => unreachable!(),
/// }
/// # }
/// ```
///
/// [`as_str`]: AbsoluteSystemPathPrefixComponent::as_str
/// [`kind`]: AbsoluteSystemPathPrefixComponent::kind
/// [`Prefix` variant]: AbsoluteSystemPathComponent::Prefix
#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AbsoluteSystemPathPrefixComponent<'a>(PrefixComponent<'a>);

impl<'a> AbsoluteSystemPathPrefixComponent<'a> {
    /// Returns the parsed prefix data.
    ///
    /// See [`AbsoluteSystemPathPrefix`]'s documentation for more information on the different
    /// kinds of prefixes.
    #[must_use]
    pub fn kind(&self) -> AbsoluteSystemPathPrefix<'a> {
        // SAFETY for all the below unsafe blocks: the path self was originally constructed from was
        // UTF-8 so any parts of it are valid UTF-8
        match self.0.kind() {
            Prefix::Verbatim(prefix) => AbsoluteSystemPathPrefix::Verbatim(prefix),
            Prefix::VerbatimUNC(server, share) => {
                let server = server;
                let share = share;
                AbsoluteSystemPathPrefix::VerbatimUNC(server, share)
            }
            Prefix::VerbatimDisk(drive) => AbsoluteSystemPathPrefix::VerbatimDisk(drive),
            Prefix::DeviceNS(prefix) => AbsoluteSystemPathPrefix::DeviceNS(prefix),
            Prefix::UNC(server, share) => {
                let server = server;
                let share = share;
                AbsoluteSystemPathPrefix::UNC(server, share)
            }
            Prefix::Disk(drive) => AbsoluteSystemPathPrefix::Disk(drive),
        }
    }

    /// Returns the raw [`OsStr`] slice for this prefix.
    #[must_use]
    pub fn as_os_str(&self) -> &'a OsStr {
        self.0.as_os_str()
    }
}

impl<'a> fmt::Debug for AbsoluteSystemPathPrefixComponent<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl From<String> for AbsoluteSystemPathBuf {
    fn from(string: String) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(string.into())
    }
}

impl From<OsString> for AbsoluteSystemPathBuf {
    fn from(string: OsString) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf(string.into())
    }
}

impl FromStr for AbsoluteSystemPathBuf {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(AbsoluteSystemPathBuf(s.into()))
    }
}

// ---
// From impls: borrowed -> borrowed
// ---

impl<'a> From<&'a str> for &'a AbsoluteSystemPath {
    fn from(s: &'a str) -> &'a AbsoluteSystemPath {
        AbsoluteSystemPath::new(s)
    }
}

// ---
// From impls: borrowed -> owned
// ---
impl<T: ?Sized + AsRef<OsStr>> From<&T> for AbsoluteSystemPathBuf {
    fn from(s: &T) -> AbsoluteSystemPathBuf {
        AbsoluteSystemPathBuf::from(s.as_ref().to_os_string())
    }
}

impl<T: ?Sized + AsRef<OsStr>> From<&T> for Box<AbsoluteSystemPath> {
    fn from(s: &T) -> Box<AbsoluteSystemPath> {
        AbsoluteSystemPathBuf::from(s).into_boxed_path()
    }
}

impl From<&'_ AbsoluteSystemPath> for Arc<AbsoluteSystemPath> {
    fn from(path: &AbsoluteSystemPath) -> Arc<AbsoluteSystemPath> {
        let arc: Arc<Path> = Arc::from(AsRef::<Path>::as_ref(path));
        let ptr = Arc::into_raw(arc) as *const AbsoluteSystemPath;
        // SAFETY:
        // * path is valid UTF-8
        // * ptr was created by consuming an Arc<Path> so it represents an arced pointer
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from *const Path to
        //   *const AbsoluteSystemPath is valid
        unsafe { Arc::from_raw(ptr) }
    }
}

impl From<&'_ AbsoluteSystemPath> for Rc<AbsoluteSystemPath> {
    fn from(path: &AbsoluteSystemPath) -> Rc<AbsoluteSystemPath> {
        let rc: Rc<Path> = Rc::from(AsRef::<Path>::as_ref(path));
        let ptr = Rc::into_raw(rc) as *const AbsoluteSystemPath;
        // SAFETY:
        // * path is valid UTF-8
        // * ptr was created by consuming an Rc<Path> so it represents an rced pointer
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from *const Path to
        //   *const AbsoluteSystemPath is valid
        unsafe { Rc::from_raw(ptr) }
    }
}

impl<'a> From<&'a AbsoluteSystemPath> for Cow<'a, AbsoluteSystemPath> {
    fn from(path: &'a AbsoluteSystemPath) -> Cow<'a, AbsoluteSystemPath> {
        Cow::Borrowed(path)
    }
}

impl From<&'_ AbsoluteSystemPath> for Box<Path> {
    fn from(path: &AbsoluteSystemPath) -> Box<Path> {
        AsRef::<Path>::as_ref(path).into()
    }
}

impl From<&'_ AbsoluteSystemPath> for Arc<Path> {
    fn from(path: &AbsoluteSystemPath) -> Arc<Path> {
        AsRef::<Path>::as_ref(path).into()
    }
}

impl From<&'_ AbsoluteSystemPath> for Rc<Path> {
    fn from(path: &AbsoluteSystemPath) -> Rc<Path> {
        AsRef::<Path>::as_ref(path).into()
    }
}

impl<'a> From<&'a AbsoluteSystemPath> for Cow<'a, Path> {
    fn from(path: &'a AbsoluteSystemPath) -> Cow<'a, Path> {
        Cow::Borrowed(path.as_ref())
    }
}

// ---
// From impls: owned -> owned
// ---

impl From<Box<AbsoluteSystemPath>> for AbsoluteSystemPathBuf {
    fn from(path: Box<AbsoluteSystemPath>) -> AbsoluteSystemPathBuf {
        path.into_path_buf()
    }
}

impl From<AbsoluteSystemPathBuf> for Box<AbsoluteSystemPath> {
    fn from(path: AbsoluteSystemPathBuf) -> Box<AbsoluteSystemPath> {
        path.into_boxed_path()
    }
}

impl<'a> From<Cow<'a, AbsoluteSystemPath>> for AbsoluteSystemPathBuf {
    fn from(path: Cow<'a, AbsoluteSystemPath>) -> AbsoluteSystemPathBuf {
        path.into_owned()
    }
}

impl From<AbsoluteSystemPathBuf> for String {
    fn from(path: AbsoluteSystemPathBuf) -> String {
        path.into_string()
    }
}

impl From<AbsoluteSystemPathBuf> for OsString {
    fn from(path: AbsoluteSystemPathBuf) -> OsString {
        path.into_os_string()
    }
}

impl<'a> From<AbsoluteSystemPathBuf> for Cow<'a, AbsoluteSystemPath> {
    fn from(path: AbsoluteSystemPathBuf) -> Cow<'a, AbsoluteSystemPath> {
        Cow::Owned(path)
    }
}

impl From<AbsoluteSystemPathBuf> for Arc<AbsoluteSystemPath> {
    fn from(path: AbsoluteSystemPathBuf) -> Arc<AbsoluteSystemPath> {
        let arc: Arc<Path> = Arc::from(path.0);
        let ptr = Arc::into_raw(arc) as *const AbsoluteSystemPath;
        // SAFETY:
        // * path is valid UTF-8
        // * ptr was created by consuming an Arc<Path> so it represents an arced pointer
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from *const Path to
        //   *const AbsoluteSystemPath is valid
        unsafe { Arc::from_raw(ptr) }
    }
}

impl From<AbsoluteSystemPathBuf> for Rc<AbsoluteSystemPath> {
    fn from(path: AbsoluteSystemPathBuf) -> Rc<AbsoluteSystemPath> {
        let rc: Rc<Path> = Rc::from(path.0);
        let ptr = Rc::into_raw(rc) as *const AbsoluteSystemPath;
        // SAFETY:
        // * path is valid UTF-8
        // * ptr was created by consuming an Rc<Path> so it represents an rced pointer
        // * AbsoluteSystemPath is marked as #[repr(transparent)] so the conversion from *const Path to
        //   *const AbsoluteSystemPath is valid
        unsafe { Rc::from_raw(ptr) }
    }
}

impl From<AbsoluteSystemPathBuf> for PathBuf {
    fn from(path: AbsoluteSystemPathBuf) -> PathBuf {
        path.0
    }
}

impl From<AbsoluteSystemPathBuf> for Box<Path> {
    fn from(path: AbsoluteSystemPathBuf) -> Box<Path> {
        PathBuf::from(path).into_boxed_path()
    }
}

impl From<AbsoluteSystemPathBuf> for Arc<Path> {
    fn from(path: AbsoluteSystemPathBuf) -> Arc<Path> {
        PathBuf::from(path).into()
    }
}

impl From<AbsoluteSystemPathBuf> for Rc<Path> {
    fn from(path: AbsoluteSystemPathBuf) -> Rc<Path> {
        PathBuf::from(path).into()
    }
}

impl<'a> From<AbsoluteSystemPathBuf> for Cow<'a, Path> {
    fn from(path: AbsoluteSystemPathBuf) -> Cow<'a, Path> {
        PathBuf::from(path).into()
    }
}

// ---
// TryFrom impls
// ---

impl TryFrom<PathBuf> for AbsoluteSystemPathBuf {
    type Error = FromPathBufError;

    fn try_from(path: PathBuf) -> Result<AbsoluteSystemPathBuf, Self::Error> {
        AbsoluteSystemPathBuf::from_path_buf(path).map_err(|path| FromPathBufError {
            path,
            error: FromPathError(()),
        })
    }
}

impl<'a> TryFrom<&'a Path> for &'a AbsoluteSystemPath {
    type Error = FromPathError;

    fn try_from(path: &'a Path) -> Result<&'a AbsoluteSystemPath, Self::Error> {
        AbsoluteSystemPath::from_path(path).ok_or(FromPathError(()))
    }
}

/// A possible error value while converting a [`PathBuf`] to a [`AbsoluteSystemPathBuf`].
///
/// Produced by the `TryFrom<PathBuf>` implementation for [`AbsoluteSystemPathBuf`].
///
/// # Examples
///
/// ```
/// use pathological::{AbsoluteSystemPathBuf, FromPathBufError};
/// use std::convert::{TryFrom, TryInto};
/// use std::ffi::OsStr;
/// # #[cfg(unix)]
/// use std::os::unix::ffi::OsStrExt;
/// use std::path::PathBuf;
///
/// let unicode_path = PathBuf::from("/valid/unicode");
/// let utf8_path_buf: AbsoluteSystemPathBuf = unicode_path.try_into().expect("valid Unicode path succeeded");
///
/// // Paths on Unix can be non-UTF-8.
/// # #[cfg(unix)]
/// let non_unicode_str = OsStr::from_bytes(b"\xFF\xFF\xFF");
/// # #[cfg(unix)]
/// let non_unicode_path = PathBuf::from(non_unicode_str);
/// # #[cfg(unix)]
/// let err: FromPathBufError = AbsoluteSystemPathBuf::try_from(non_unicode_path.clone())
///     .expect_err("non-Unicode path failed");
/// # #[cfg(unix)]
/// assert_eq!(err.as_path(), &non_unicode_path);
/// # #[cfg(unix)]
/// assert_eq!(err.into_path_buf(), non_unicode_path);
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FromPathBufError {
    path: PathBuf,
    error: FromPathError,
}

impl FromPathBufError {
    /// Returns the [`Path`] slice that was attempted to be converted to [`AbsoluteSystemPathBuf`].
    pub fn as_path(&self) -> &Path {
        &self.path
    }

    /// Returns the [`PathBuf`] that was attempted to be converted to [`AbsoluteSystemPathBuf`].
    pub fn into_path_buf(self) -> PathBuf {
        self.path
    }

    /// Fetches a [`FromPathError`] for more about the conversion failure.
    ///
    /// At the moment this struct does not contain any additional information, but is provided for
    /// completeness.
    pub fn from_path_error(&self) -> FromPathError {
        self.error
    }

    /// Converts self into a [`std::io::Error`] with kind
    /// [`InvalidData`](io::ErrorKind::InvalidData).
    ///
    /// Many users of `FromPathBufError` will want to convert it into an `io::Error`. This is a
    /// convenience method to do that.
    pub fn into_io_error(self) -> io::Error {
        // NOTE: we don't currently implement `From<FromPathBufError> for io::Error` because we want
        // to ensure the user actually desires that conversion.
        io::Error::new(io::ErrorKind::InvalidData, self)
    }
}

impl fmt::Display for FromPathBufError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PathBuf contains invalid UTF-8: {}", self.path.display())
    }
}

impl error::Error for FromPathBufError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.error)
    }
}

/// A possible error value while converting a [`Path`] to a [`AbsoluteSystemPath`].
///
/// Produced by the `TryFrom<&Path>` implementation for [`&AbsoluteSystemPath`](AbsoluteSystemPath).
///
///
/// # Examples
///
/// ```
/// use pathological::{AbsoluteSystemPath, FromPathError};
/// use std::convert::{TryFrom, TryInto};
/// use std::ffi::OsStr;
/// # #[cfg(unix)]
/// use std::os::unix::ffi::OsStrExt;
/// use std::path::Path;
///
/// let unicode_path = Path::new("/valid/unicode");
/// let utf8_path: &AbsoluteSystemPath = unicode_path.try_into().expect("valid Unicode path succeeded");
///
/// // Paths on Unix can be non-UTF-8.
/// # #[cfg(unix)]
/// let non_unicode_str = OsStr::from_bytes(b"\xFF\xFF\xFF");
/// # #[cfg(unix)]
/// let non_unicode_path = Path::new(non_unicode_str);
/// # #[cfg(unix)]
/// let err: FromPathError = <&AbsoluteSystemPath>::try_from(non_unicode_path)
///     .expect_err("non-Unicode path failed");
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct FromPathError(());

impl FromPathError {
    /// Converts self into a [`std::io::Error`] with kind
    /// [`InvalidData`](io::ErrorKind::InvalidData).
    ///
    /// Many users of `FromPathError` will want to convert it into an `io::Error`. This is a
    /// convenience method to do that.
    pub fn into_io_error(self) -> io::Error {
        // NOTE: we don't currently implement `From<FromPathBufError> for io::Error` because we want
        // to ensure the user actually desires that conversion.
        io::Error::new(io::ErrorKind::InvalidData, self)
    }
}

impl fmt::Display for FromPathError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Path contains invalid UTF-8")
    }
}

impl error::Error for FromPathError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

// ---
// AsRef impls
// ---

impl AsRef<AbsoluteSystemPath> for AbsoluteSystemPath {
    fn as_ref(&self) -> &AbsoluteSystemPath {
        self
    }
}

impl AsRef<AbsoluteSystemPath> for AbsoluteSystemPathBuf {
    fn as_ref(&self) -> &AbsoluteSystemPath {
        self.as_path()
    }
}

impl AsRef<AbsoluteSystemPath> for str {
    fn as_ref(&self) -> &AbsoluteSystemPath {
        AbsoluteSystemPath::new(self)
    }
}

impl AsRef<AbsoluteSystemPath> for String {
    fn as_ref(&self) -> &AbsoluteSystemPath {
        AbsoluteSystemPath::new(self)
    }
}

impl AsRef<Path> for AbsoluteSystemPath {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<Path> for AbsoluteSystemPathBuf {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<OsStr> for AbsoluteSystemPath {
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

impl AsRef<OsStr> for AbsoluteSystemPathBuf {
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

// ---
// Borrow and ToOwned
// ---

impl Borrow<AbsoluteSystemPath> for AbsoluteSystemPathBuf {
    fn borrow(&self) -> &AbsoluteSystemPath {
        self.as_path()
    }
}

impl ToOwned for AbsoluteSystemPath {
    type Owned = AbsoluteSystemPathBuf;

    fn to_owned(&self) -> AbsoluteSystemPathBuf {
        self.to_path_buf()
    }
}

impl<P: AsRef<AbsoluteSystemPath>> std::iter::FromIterator<P> for AbsoluteSystemPathBuf {
    fn from_iter<I: IntoIterator<Item = P>>(iter: I) -> AbsoluteSystemPathBuf {
        let mut buf = AbsoluteSystemPathBuf::new();
        buf.extend(iter);
        buf
    }
}

// ---
// [Partial]Eq, [Partial]Ord, Hash
// ---

impl PartialEq for AbsoluteSystemPathBuf {
    fn eq(&self, other: &AbsoluteSystemPathBuf) -> bool {
        self.components() == other.components()
    }
}

impl Eq for AbsoluteSystemPathBuf {}

impl Hash for AbsoluteSystemPathBuf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_path().hash(state)
    }
}

impl PartialOrd for AbsoluteSystemPathBuf {
    fn partial_cmp(&self, other: &AbsoluteSystemPathBuf) -> Option<Ordering> {
        self.components().partial_cmp(other.components())
    }
}

impl Ord for AbsoluteSystemPathBuf {
    fn cmp(&self, other: &AbsoluteSystemPathBuf) -> Ordering {
        self.components().cmp(other.components())
    }
}

impl PartialEq for AbsoluteSystemPath {
    fn eq(&self, other: &AbsoluteSystemPath) -> bool {
        self.components().eq(other.components())
    }
}

impl Eq for AbsoluteSystemPath {}

impl Hash for AbsoluteSystemPath {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for component in self.components() {
            component.hash(state)
        }
    }
}

impl PartialOrd for AbsoluteSystemPath {
    fn partial_cmp(&self, other: &AbsoluteSystemPath) -> Option<Ordering> {
        self.components().partial_cmp(other.components())
    }
}

impl Ord for AbsoluteSystemPath {
    fn cmp(&self, other: &AbsoluteSystemPath) -> Ordering {
        self.components().cmp(other.components())
    }
}

impl<'a> IntoIterator for &'a AbsoluteSystemPathBuf {
    type Item = &'a OsStr;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a AbsoluteSystemPath {
    type Item = &'a OsStr;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

macro_rules! impl_cmp {
    ($lhs:ty, $rhs: ty) => {
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                <AbsoluteSystemPath as PartialEq>::eq(self, other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                <AbsoluteSystemPath as PartialEq>::eq(self, other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                <AbsoluteSystemPath as PartialOrd>::partial_cmp(self, other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                <AbsoluteSystemPath as PartialOrd>::partial_cmp(self, other)
            }
        }
    };
}

impl_cmp!(AbsoluteSystemPathBuf, AbsoluteSystemPath);
impl_cmp!(AbsoluteSystemPathBuf, &'a AbsoluteSystemPath);
impl_cmp!(Cow<'a, AbsoluteSystemPath>, AbsoluteSystemPath);
impl_cmp!(Cow<'a, AbsoluteSystemPath>, &'b AbsoluteSystemPath);
impl_cmp!(Cow<'a, AbsoluteSystemPath>, AbsoluteSystemPathBuf);

macro_rules! impl_cmp_std_path {
    ($lhs:ty, $rhs: ty) => {
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                <Path as PartialEq>::eq(self.as_ref(), other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                <Path as PartialEq>::eq(self, other.as_ref())
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<std::cmp::Ordering> {
                <Path as PartialOrd>::partial_cmp(self.as_ref(), other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<std::cmp::Ordering> {
                <Path as PartialOrd>::partial_cmp(self, other.as_ref())
            }
        }
    };
}

impl_cmp_std_path!(AbsoluteSystemPathBuf, Path);
impl_cmp_std_path!(AbsoluteSystemPathBuf, &'a Path);
impl_cmp_std_path!(AbsoluteSystemPathBuf, Cow<'a, Path>);
impl_cmp_std_path!(AbsoluteSystemPathBuf, PathBuf);
impl_cmp_std_path!(AbsoluteSystemPath, Path);
impl_cmp_std_path!(AbsoluteSystemPath, &'a Path);
impl_cmp_std_path!(AbsoluteSystemPath, Cow<'a, Path>);
impl_cmp_std_path!(AbsoluteSystemPath, PathBuf);
impl_cmp_std_path!(&'a AbsoluteSystemPath, Path);
impl_cmp_std_path!(&'a AbsoluteSystemPath, Cow<'b, Path>);
impl_cmp_std_path!(&'a AbsoluteSystemPath, PathBuf);
// NOTE: impls for Cow<'a, AbsoluteSystemPath> cannot be defined because of the orphan rule (E0117)

macro_rules! impl_cmp_os_str {
    ($lhs:ty, $rhs: ty) => {
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                <Path as PartialEq>::eq(self.as_ref(), other.as_ref())
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                <Path as PartialEq>::eq(self.as_ref(), other.as_ref())
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<std::cmp::Ordering> {
                <Path as PartialOrd>::partial_cmp(self.as_ref(), other.as_ref())
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<std::cmp::Ordering> {
                <Path as PartialOrd>::partial_cmp(self.as_ref(), other.as_ref())
            }
        }
    };
}

impl_cmp_os_str!(AbsoluteSystemPathBuf, OsStr);
impl_cmp_os_str!(AbsoluteSystemPathBuf, &'a OsStr);
impl_cmp_os_str!(AbsoluteSystemPathBuf, Cow<'a, OsStr>);
impl_cmp_os_str!(AbsoluteSystemPathBuf, OsString);
impl_cmp_os_str!(AbsoluteSystemPath, OsStr);
impl_cmp_os_str!(AbsoluteSystemPath, &'a OsStr);
impl_cmp_os_str!(AbsoluteSystemPath, Cow<'a, OsStr>);
impl_cmp_os_str!(AbsoluteSystemPath, OsString);
impl_cmp_os_str!(&'a AbsoluteSystemPath, OsStr);
impl_cmp_os_str!(&'a AbsoluteSystemPath, Cow<'b, OsStr>);
impl_cmp_os_str!(&'a AbsoluteSystemPath, OsString);
// NOTE: impls for Cow<'a, AbsoluteSystemPath> cannot be defined because of the orphan rule (E0117)
