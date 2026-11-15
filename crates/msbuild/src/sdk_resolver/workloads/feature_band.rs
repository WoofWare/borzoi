//! `SdkFeatureBand` (dotnet/sdk, `Microsoft.NET.Sdk.WorkloadManifestReader`):
//! the feature band a version string names, as the workload resolver computes,
//! spells and orders it.
//!
//! The resolver builds a `ReleaseVersion` from the string (strict SemVer 2.0:
//! three numeric components, an optional prerelease, optional build metadata)
//! and keeps the major, the minor, and the patch rounded down to its hundred.
//! A prerelease survives as its first two dot-separated identifiers ("treat
//! preview versions as their own feature bands"), unless its text contains
//! `dev`, `ci` or `rtm` anywhere (an ordinal substring test, so `specific.1`
//! collapses too), when the band is the release one. Build metadata never
//! survives. So `11.0.100-rc.1.26425.128` is band `11.0.100-rc.1`, and
//! `10.0.401` is `10.0.400`.
//!
//! [`FeatureBand::parse`] accepts a subset of what `ReleaseVersion` does: each
//! number at most nine digits, so none overflows its `int`. Everything else
//! is `None`, which the callers treat as the resolver failing, and decline on.
//! `tests/workload_locator_diff.rs` holds the spelling and the order to the
//! resolver's own over a generated grid of version strings.

use std::cmp::Ordering;
use std::fmt;

/// One dot-separated prerelease identifier, compared as SemVer 2.0 §11 says:
/// numerically when all digits, ordinally otherwise, numeric before
/// alphanumeric.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Identifier {
    Numeric(u32),
    Alphanumeric(String),
}

impl Ord for Identifier {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Identifier::Numeric(a), Identifier::Numeric(b)) => a.cmp(b),
            (Identifier::Numeric(_), Identifier::Alphanumeric(_)) => Ordering::Less,
            (Identifier::Alphanumeric(_), Identifier::Numeric(_)) => Ordering::Greater,
            (Identifier::Alphanumeric(a), Identifier::Alphanumeric(b)) => {
                a.as_bytes().cmp(b.as_bytes())
            }
        }
    }
}

impl PartialOrd for Identifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Identifier::Numeric(n) => write!(f, "{n}"),
            Identifier::Alphanumeric(s) => f.write_str(s),
        }
    }
}

/// A feature band: `major.minor.band[-prerelease]`, where `band` is a
/// multiple of a hundred and `prerelease` holds at most two identifiers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FeatureBand {
    major: u32,
    minor: u32,
    band: u32,
    /// Empty for a release band.
    prerelease: Vec<Identifier>,
}

/// A SemVer numeric component: digits, no leading zero, at most nine of them.
fn number(text: &str) -> Option<u32> {
    let plain = !text.is_empty()
        && text.len() <= 9
        && text.bytes().all(|b| b.is_ascii_digit())
        && (text == "0" || !text.starts_with('0'));
    plain.then(|| text.parse().ok()).flatten()
}

/// A SemVer prerelease identifier, or `None` where the text is not one we
/// accept.
fn identifier(text: &str) -> Option<Identifier> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
        return None;
    }
    if text.bytes().all(|b| b.is_ascii_digit()) {
        number(text).map(Identifier::Numeric)
    } else {
        Some(Identifier::Alphanumeric(text.to_owned()))
    }
}

impl FeatureBand {
    /// The feature band of `version` (`new SdkFeatureBand(version)`), or
    /// `None` where the resolver would throw or where we do not certify the
    /// spelling.
    pub(crate) fn parse(version: &str) -> Option<FeatureBand> {
        let (version, metadata) = match version.split_once('+') {
            Some((version, metadata)) => (version, Some(metadata)),
            None => (version, None),
        };
        if let Some(metadata) = metadata
            && !metadata.split('.').all(|part| {
                !part.is_empty() && part.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
            })
        {
            return None;
        }
        let (core, prerelease) = match version.split_once('-') {
            Some((core, prerelease)) => (core, Some(prerelease)),
            None => (version, None),
        };
        let mut parts = core.split('.');
        let (Some(major), Some(minor), Some(patch), None) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            return None;
        };
        let (major, minor, patch) = (number(major)?, number(minor)?, number(patch)?);
        let identifiers = match prerelease {
            Some(prerelease) => prerelease
                .split('.')
                .map(identifier)
                .collect::<Option<Vec<_>>>()?,
            None => Vec::new(),
        };
        let collapses =
            prerelease.is_none_or(|p| p.contains("dev") || p.contains("ci") || p.contains("rtm"));
        Some(FeatureBand {
            major,
            minor,
            band: patch / 100 * 100,
            prerelease: if collapses {
                Vec::new()
            } else {
                identifiers.into_iter().take(2).collect()
            },
        })
    }

    /// The release band this one belongs to (`ToStringWithoutPrerelease`).
    pub(crate) fn without_prerelease(&self) -> FeatureBand {
        FeatureBand {
            prerelease: Vec::new(),
            ..self.clone()
        }
    }
}

impl Ord for FeatureBand {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.major, self.minor, self.band)
            .cmp(&(other.major, other.minor, other.band))
            .then_with(|| {
                match (self.prerelease.is_empty(), other.prerelease.is_empty()) {
                    (true, true) => Ordering::Equal,
                    // A release outranks its prereleases.
                    (true, false) => Ordering::Greater,
                    (false, true) => Ordering::Less,
                    (false, false) => self.prerelease.cmp(&other.prerelease),
                }
            })
    }
}

impl PartialOrd for FeatureBand {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for FeatureBand {
    /// `SdkFeatureBand.ToString()`: the directory name the resolver looks in.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.band)?;
        for (i, identifier) in self.prerelease.iter().enumerate() {
            f.write_str(if i == 0 { "-" } else { "." })?;
            write!(f, "{identifier}")?;
        }
        Ok(())
    }
}
