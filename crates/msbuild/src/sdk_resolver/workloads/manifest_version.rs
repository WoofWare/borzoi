//! The order in which `SdkDirectoryWorkloadManifestProvider.ResolveManifestDirectory`
//! picks a manifest's version directory: the provider's private
//! `VersionCompare`, folded over the candidates in enumeration order
//! (`Aggregate((d1, d2) => VersionCompare(d1, d2) > 0 ? d1 : d2)`).
//!
//! `VersionCompare(a, b)` is 0 when the names are equal (ordinal). Otherwise
//! it splits each name at its first `-` and compares the cores as
//! `System.Version` does (two to four components; a missing build or revision
//! is -1, below 0). Only when the cores are equal does it compare the rest
//! of each name, the `-` included, as the prerelease of a `ReleaseVersion`
//! (`1.1.1-…`, or none), so the first identifier always carries the `-` and
//! is never numeric: `1.0.0-10` sorts below `1.0.0-9`.
//!
//! `ReleaseVersion`'s precedence: a version without a prerelease is above one
//! with; identifiers compare left to right, two all-digit ones by length and
//! then digit by digit (so `01` is above `2`), an all-digit one below any
//! other, and any other two ordinally; a longer list is above its prefix.
//!
//! [`ManifestVersion::parse`] certifies a subset of what both parsers take:
//! a core of two to four components of one to nine ASCII digits, and a rest
//! of dot-separated identifiers of ASCII letters, digits and `-`, none empty.
//! Outside it the reference may throw (a `System.Version` it cannot parse, a
//! prerelease `ReleaseVersion` refuses), so the provider's comparison is not
//! certainly ours; a name it never compares (the only candidate) needs no
//! parse at all. `workload_locator_diff` grades both against the resolver.

use std::cmp::Ordering;

/// A manifest version directory's name, as `VersionCompare` reads it.
#[derive(Debug)]
pub(super) struct ManifestVersion<'a> {
    name: &'a str,
    /// `System.Version`'s four fields, a missing one -1.
    core: [i64; 4],
    /// The name from its first `-` on, the `-` included.
    prerelease: Option<&'a str>,
}

impl<'a> ManifestVersion<'a> {
    /// `name` as `VersionCompare` reads it, if it lies in the certified
    /// subset (see the module docs).
    pub(super) fn parse(name: &'a str) -> Option<Self> {
        let (core, prerelease) = match name.find('-') {
            Some(dash) => (&name[..dash], Some(&name[dash..])),
            None => (name, None),
        };
        let components: Vec<&str> = core.split('.').collect();
        if !(2..=4).contains(&components.len())
            || !components
                .iter()
                .all(|c| (1..=9).contains(&c.len()) && c.bytes().all(|b| b.is_ascii_digit()))
        {
            return None;
        }
        let mut fields = [-1i64; 4];
        for (field, component) in fields.iter_mut().zip(&components) {
            *field = component.parse().ok()?;
        }
        if let Some(prerelease) = prerelease
            && !prerelease.split('.').all(|identifier| {
                !identifier.is_empty()
                    && identifier
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'-')
            })
        {
            return None;
        }
        Some(ManifestVersion {
            name,
            core: fields,
            prerelease,
        })
    }

    /// `VersionCompare(self, other)`: `Equal` for two names it cannot tell
    /// apart as well as for one name.
    pub(super) fn compare(&self, other: &ManifestVersion<'_>) -> Ordering {
        if self.name == other.name {
            return Ordering::Equal;
        }
        self.core
            .cmp(&other.core)
            .then_with(|| compare_prereleases(self.prerelease, other.prerelease))
    }
}

/// `ReleaseVersion.CompareIdentifiers` of two prereleases.
fn compare_prereleases(a: Option<&str>, b: Option<&str>) -> Ordering {
    let (a, b) = match (a, b) {
        (None, None) => return Ordering::Equal,
        (None, Some(_)) => return Ordering::Greater,
        (Some(_), None) => return Ordering::Less,
        (Some(a), Some(b)) => (a, b),
    };
    let (a, b): (Vec<&str>, Vec<&str>) = (a.split('.').collect(), b.split('.').collect());
    for (x, y) in a.iter().zip(&b) {
        let numeric = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
        let order = match (numeric(x), numeric(y)) {
            // `CompareNumericIdentifier`: the longer is above; of two as
            // long, the first digit that differs decides.
            (true, true) => x.len().cmp(&y.len()).then_with(|| x.cmp(y)),
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => x.cmp(y),
        };
        if order != Ordering::Equal {
            return order;
        }
    }
    a.len().cmp(&b.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cmp(a: &str, b: &str) -> Ordering {
        ManifestVersion::parse(a)
            .unwrap()
            .compare(&ManifestVersion::parse(b).unwrap())
    }

    /// The orders the resolver was seen to pick (`workload_locator_diff`
    /// grades them all).
    #[test]
    fn versions_order_as_version_compare_orders_them() {
        assert_eq!(cmp("1.0.0", "1.0"), Ordering::Greater);
        assert_eq!(cmp("1.0.0", "1.0.0.0"), Ordering::Less);
        assert_eq!(cmp("1.0.0", "1.0.0-rc.1"), Ordering::Greater);
        assert_eq!(cmp("1.0.0-rc.1", "1.0.0-rc.01"), Ordering::Less);
        assert_eq!(cmp("1.0.0-rc.2", "1.0.0-rc.01"), Ordering::Less);
        assert_eq!(cmp("1.0.0-rc.10", "1.0.0-rc.01"), Ordering::Greater);
        assert_eq!(cmp("1.0.0-10", "1.0.0-9"), Ordering::Less);
        assert_eq!(cmp("1.0.0-rc.1", "1.0.0-rc.a"), Ordering::Less);
        assert_eq!(cmp("1.0.0-a", "1.0.0-A"), Ordering::Greater);
        assert_eq!(cmp("1.0.0-rc.1", "1.0.0-rc.1.2"), Ordering::Less);
        assert_eq!(cmp("1.0.0", "01.0.0"), Ordering::Equal);
        assert_eq!(cmp("1.0.0.0-rc.1", "1.0.0"), Ordering::Greater);
    }

    #[test]
    fn names_outside_the_certified_subset_are_refused() {
        for name in [
            "1",
            "1.0.0.0.0",
            "foo",
            "-1",
            "1.0.0+x",
            "1.0.0-rc+x",
            "1.0.0-rc..1",
            "1.0.0-rc_1",
            " 1.0.0",
            "1234567890.0.0",
            "1.0.0-é",
        ] {
            assert!(ManifestVersion::parse(name).is_none(), "{name}");
        }
    }
}
