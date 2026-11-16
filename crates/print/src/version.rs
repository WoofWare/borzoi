//! The F# language version a tree targets, as a type.
//!
//! Every tree type that can hold a version-gated construct takes a
//! [`Version`] parameter, `Expr<V8_0>` and so on. A gated construct carries a
//! field of the gate's type, [`Version`]'s associated type named after the
//! FCS `LanguageFeature` that introduced it: [`Available`] at the versions
//! with the feature and the uninhabited [`Unavailable`] below them. So an
//! `ImplFile<V7_0>` cannot hold `_.Length` at all; building one is a compile
//! error, not a refusal at print time.
//!
//! Each gate switches on at one version and stays on, so a tree that is valid
//! at its version is valid at every later one. Code that picks the version at
//! run time, from a project's `<LangVersion>`, is written generic over `V` and
//! instantiated by one `match` on [`LanguageVersion`]; code that uses a feature
//! where the version has it asks the gate for its witness,
//! [`Gate::WITNESS`].

use std::fmt::Debug;
use std::hash::Hash;

pub use borzoi_cst::language_version::{LanguageFeature, LanguageVersion};

/// A gated feature is present at this version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Available;

/// A gated feature is absent at this version. It has no values, so a construct
/// carrying it cannot be built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Unavailable {}

mod sealed {
    pub trait Sealed {}
}

/// Whether a feature is present: [`Available`] or [`Unavailable`].
pub trait Gate: sealed::Sealed + Debug + Clone + Copy + PartialEq + Eq + Hash + 'static {
    /// The gate's value where the feature is present.
    const WITNESS: Option<Self>;
}

impl sealed::Sealed for Available {}
impl Gate for Available {
    const WITNESS: Option<Self> = Some(Available);
}

impl sealed::Sealed for Unavailable {}
impl Gate for Unavailable {
    const WITNESS: Option<Self> = None;
}

/// An F# language version, as a type. Implemented only by the markers in this
/// module, one per [`LanguageVersion`].
pub trait Version: sealed::Sealed + Debug + Clone + Copy + PartialEq + Eq + Hash + 'static {
    /// The version this type stands for.
    const LANGUAGE: LanguageVersion;

    /// Each gate's feature and whether this version has it, as the associated
    /// types say; the crate's tests hold it to [`LanguageVersion::supports`].
    const GATES: &'static [(LanguageFeature, bool)];

    /// `_.Member`, a lambda reading a member of its argument (F# 8).
    type AccessorFunctionShorthand: Gate;
}

macro_rules! versions {
    ($(
        $(#[$doc:meta])*
        $name:ident: available [$($available:ident),*] unavailable [$($unavailable:ident),*];
    )*) => {$(
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum $name {}

        impl sealed::Sealed for $name {}

        impl Version for $name {
            const LANGUAGE: LanguageVersion = LanguageVersion::$name;
            const GATES: &'static [(LanguageFeature, bool)] = &[
                $((LanguageFeature::$available, true),)*
                $((LanguageFeature::$unavailable, false),)*
            ];
            $(type $available = Available;)*
            $(type $unavailable = Unavailable;)*
        }
    )*};
}

versions! {
    /// F# 4.6, the oldest version `borzoi-cst` parses.
    V4_6: available [] unavailable [AccessorFunctionShorthand];
    /// F# 4.7.
    V4_7: available [] unavailable [AccessorFunctionShorthand];
    /// F# 5.0.
    V5_0: available [] unavailable [AccessorFunctionShorthand];
    /// F# 6.0.
    V6_0: available [] unavailable [AccessorFunctionShorthand];
    /// F# 7.0.
    V7_0: available [] unavailable [AccessorFunctionShorthand];
    /// F# 8.0.
    V8_0: available [AccessorFunctionShorthand] unavailable [];
    /// F# 9.0.
    V9_0: available [AccessorFunctionShorthand] unavailable [];
    /// F# 10.0.
    V10_0: available [AccessorFunctionShorthand] unavailable [];
    /// F# 11.0, what a project without `<LangVersion>` gets
    /// ([`LanguageVersion::DEFAULT`]).
    V11_0: available [AccessorFunctionShorthand] unavailable [];
    /// `<LangVersion>preview</LangVersion>`.
    Preview: available [AccessorFunctionShorthand] unavailable [];
}

/// The version a project without `<LangVersion>` gets.
pub type DefaultVersion = V11_0;

#[cfg(test)]
mod tests {
    use super::*;

    fn gates_match_the_feature_table<V: Version>() {
        assert!(!V::GATES.is_empty(), "{:?} lists no gates", V::LANGUAGE);
        for &(feature, available) in V::GATES {
            assert_eq!(
                available,
                V::LANGUAGE.supports(feature),
                "{feature:?} at {:?}",
                V::LANGUAGE
            );
        }
    }

    #[test]
    fn every_versions_gates_match_the_feature_table() {
        gates_match_the_feature_table::<V4_6>();
        gates_match_the_feature_table::<V4_7>();
        gates_match_the_feature_table::<V5_0>();
        gates_match_the_feature_table::<V6_0>();
        gates_match_the_feature_table::<V7_0>();
        gates_match_the_feature_table::<V8_0>();
        gates_match_the_feature_table::<V9_0>();
        gates_match_the_feature_table::<V10_0>();
        gates_match_the_feature_table::<V11_0>();
        gates_match_the_feature_table::<Preview>();
    }

    #[test]
    fn every_version_has_a_marker() {
        let markers = [
            V4_6::LANGUAGE,
            V4_7::LANGUAGE,
            V5_0::LANGUAGE,
            V6_0::LANGUAGE,
            V7_0::LANGUAGE,
            V8_0::LANGUAGE,
            V9_0::LANGUAGE,
            V10_0::LANGUAGE,
            V11_0::LANGUAGE,
        ];
        assert_eq!(markers, LanguageVersion::NUMBERED);
        assert_eq!(Preview::LANGUAGE, LanguageVersion::Preview);
        assert_eq!(DefaultVersion::LANGUAGE, LanguageVersion::DEFAULT);
    }

    #[test]
    fn a_gates_witness_is_its_availability() {
        assert_eq!(
            <V8_0 as Version>::AccessorFunctionShorthand::WITNESS,
            Some(Available)
        );
        assert_eq!(<V7_0 as Version>::AccessorFunctionShorthand::WITNESS, None);
    }
}
