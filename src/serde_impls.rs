// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Serde implementations for `AbsoluteSystemPath`.
//!
//! The Serde implementations for `AbsoluteSystemPathBuf` are derived, but `AbsoluteSystemPath` is an unsized type which
//! the derive impls can't handle. Implement these by hand.

use crate::AbsoluteSystemPath;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

struct AbsoluteSystemPathVisitor;

impl<'a> de::Visitor<'a> for AbsoluteSystemPathVisitor {
    type Value = &'a AbsoluteSystemPath;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a borrowed path")
    }

    fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(v.as_ref())
    }

    fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        std::str::from_utf8(v)
            .map(AsRef::as_ref)
            .map_err(|_| de::Error::invalid_value(de::Unexpected::Bytes(v), &self))
    }
}

#[cfg(feature = "serde1")]
impl<'de: 'a, 'a> Deserialize<'de> for &'a AbsoluteSystemPath {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(AbsoluteSystemPathVisitor)
    }
}

#[cfg(feature = "serde1")]
impl Serialize for AbsoluteSystemPath {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_str().serialize(serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AbsoluteSystemPathBuf;
    use serde_bytes::ByteBuf;

    #[test]
    fn valid_utf8() {
        let valid_utf8 = &["", "bar", "💩"];
        for input in valid_utf8 {
            let encode = Encode {
                path: ByteBuf::from(*input),
            };
            let encoded = bincode::serialize(&encode).expect("encoded correctly");

            assert_valid_utf8::<DecodeOwned>(input, &encoded);
            assert_valid_utf8::<DecodeBorrowed>(input, &encoded);
        }
    }

    fn assert_valid_utf8<'de, T: TestTrait<'de>>(input: &str, encoded: &'de [u8]) {
        let output = bincode::deserialize::<T>(encoded).expect("valid UTF-8 should be fine");
        assert_eq!(
            output.path(),
            input,
            "for input, with {}, paths should match",
            T::description()
        );
    }

    #[test]
    fn invalid_utf8() {
        let invalid_utf8: &[(&[u8], _, _)] = &[
            (b"\xff", 0, 1),
            (b"foo\xfe", 3, 1),
            (b"a\xC3\xA9 \xED\xA0\xBD\xF0\x9F\x92\xA9", 4, 1),
        ];

        for (input, valid_up_to, error_len) in invalid_utf8 {
            let encode = Encode {
                path: ByteBuf::from(*input),
            };
            let encoded = bincode::serialize(&encode).expect("encoded correctly");

            assert_invalid_utf8::<DecodeOwned>(input, &encoded, *valid_up_to, *error_len);
            assert_invalid_utf8::<DecodeBorrowed>(input, &encoded, *valid_up_to, *error_len)
        }
    }

    fn assert_invalid_utf8<'de, T: TestTrait<'de>>(
        input: &[u8],
        encoded: &'de [u8],
        valid_up_to: usize,
        error_len: usize,
    ) {
        let error = bincode::deserialize::<T>(encoded).expect_err("invalid UTF-8 should error out");
        let utf8_error = match *error {
            bincode::ErrorKind::InvalidUtf8Encoding(utf8_error) => utf8_error,
            other => panic!(
                "for input {:?}, with {}, expected ErrorKind::InvalidUtf8Encoding, found: {}",
                input,
                T::description(),
                other
            ),
        };
        assert_eq!(
            utf8_error.valid_up_to(),
            valid_up_to,
            "for input {:?}, with {}, valid_up_to didn't match",
            input,
            T::description(),
        );
        assert_eq!(
            utf8_error.error_len(),
            Some(error_len),
            "for input {:?}, with {}, error_len didn't match",
            input,
            T::description(),
        );
    }

    #[derive(Serialize, Debug)]
    struct Encode {
        path: ByteBuf,
    }

    trait TestTrait<'de>: Deserialize<'de> + fmt::Debug {
        fn description() -> &'static str;
        fn path(&self) -> &AbsoluteSystemPath;
    }

    #[derive(Deserialize, Debug)]
    #[allow(unused)]
    struct DecodeOwned {
        path: AbsoluteSystemPathBuf,
    }

    impl<'de> TestTrait<'de> for DecodeOwned {
        fn description() -> &'static str {
            "DecodeOwned"
        }

        fn path(&self) -> &AbsoluteSystemPath {
            &self.path
        }
    }

    #[derive(Deserialize, Debug)]
    #[allow(unused)]
    struct DecodeBorrowed<'a> {
        #[serde(borrow)]
        path: &'a AbsoluteSystemPath,
    }

    impl<'de> TestTrait<'de> for DecodeBorrowed<'de> {
        fn description() -> &'static str {
            "DecodeBorrowed"
        }

        fn path(&self) -> &AbsoluteSystemPath {
            self.path
        }
    }
}
