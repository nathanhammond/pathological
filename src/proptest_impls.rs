// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [proptest::Arbitrary](Arbitrary) implementation for `AbsoluteSystemPathBuf` and `Box<AbsoluteSystemPath>`.  Note
//! that implementions for `Rc<AbsoluteSystemPath>` and `Arc<AbsoluteSystemPath>` are not currently possible due to
//! orphan rules - this crate doesn't define `Rc`/`Arc` nor `Arbitrary`, so it can't define those
//! implementations.

// NOTE: #[cfg(feature = "proptest1")] is specified here to work with `doc_cfg`.

use crate::{AbsoluteSystemPath, AbsoluteSystemPathBuf};
use proptest::{arbitrary::StrategyFor, prelude::*, strategy::MapInto};

/// The [`Arbitrary`] impl for `AbsoluteSystemPathBuf` returns a path with between 0 and 8 components,
/// joined by the [`MAIN_SEPARATOR`](std::path::MAIN_SEPARATOR) for the platform. (Each component is
/// randomly generated, and may itself contain one or more separators.)
///
/// On Unix, this generates an absolute path half of the time and a relative path the other half.
///
/// On Windows, this implementation doesn't currently generate
/// [`Utf8PrefixComponent`](crate::Utf8PrefixComponent) instances, though in the future it might.
#[cfg(feature = "proptest1")]
impl Arbitrary for AbsoluteSystemPathBuf {
    type Parameters = <String as Arbitrary>::Parameters;
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        (
            any::<bool>(),
            prop::collection::vec(any_with::<String>(args), 0..8),
        )
            .prop_map(|(is_relative, components)| {
                let initial_component =
                    is_relative.then(|| format!("{}", std::path::MAIN_SEPARATOR));
                initial_component
                    .into_iter()
                    .chain(components.into_iter())
                    .collect()
            })
            .boxed()
    }
}

/// The [`Arbitrary`] impl for `Box<AbsoluteSystemPath>` returns a path with between 0 and 8 components,
/// joined by the [`MAIN_SEPARATOR`](std::path::MAIN_SEPARATOR) for the platform. (Each component is
/// randomly generated, and may itself contain one or more separators.)
///
/// On Unix, this generates an absolute path half of the time and a relative path the other half.
///
/// On Windows, this implementation doesn't currently generate
/// [`Utf8PrefixComponent`](crate::Utf8PrefixComponent) instances, though in the future it might.
#[cfg(feature = "proptest1")]
impl Arbitrary for Box<AbsoluteSystemPath> {
    type Parameters = <AbsoluteSystemPathBuf as Arbitrary>::Parameters;
    type Strategy = MapInto<StrategyFor<AbsoluteSystemPathBuf>, Self>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        any_with::<AbsoluteSystemPathBuf>(args).prop_map_into()
    }
}
