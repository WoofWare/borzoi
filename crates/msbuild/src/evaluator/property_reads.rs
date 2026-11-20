//! What a read of a property name sees at the end of the walk, and whether
//! that is the real build's answer: one [`PropertyRead`] per name, published
//! on [`crate::ParsedProject::property_reads`].
//!
//! A read has four outcomes, not two, because "the walk holds no value" says
//! two different things: the name is undefined in the real build too
//! ([`PropertyRead::Unset`]), or the real build may hold a value the walk does
//! not ([`PropertyRead::UnsetInexact`]), a refused write among them. A
//! consumer that reads a value off a map and treats a missing key as "never
//! written" conflates the two (#780).

use std::collections::HashMap;

use super::{State, is_toolset_initial_property_name};
use crate::UntrustedCause;
use crate::properties::Worlds;

/// A read of one property at the end of the walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropertyRead {
    /// A value the walk trusts, unescaped as a target's read sees it.
    Value(String),
    /// Undefined, and undefined in the real build too.
    Unset,
    /// Undefined in the walk, but the real build may define it.
    UnsetInexact(InexactUnset),
    /// A value the walk holds but may have wrong: computed from something it
    /// could not pin down, or held from before content it could not see, which
    /// may have rewritten it.
    Untrusted(UntrustedCause),
}

impl PropertyRead {
    /// The value, when the walk trusts one.
    pub fn value(&self) -> Option<&str> {
        match self {
            PropertyRead::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Why the walk's value may not be the real build's, for a value it
    /// holds and may have wrong.
    pub fn untrusted_cause(&self) -> Option<&UntrustedCause> {
        match self {
            PropertyRead::Untrusted(cause) => Some(cause),
            _ => None,
        }
    }

    /// Whether the read is the real build's: a trusted value, or a name the
    /// real build leaves undefined too.
    pub fn is_exact(&self) -> bool {
        matches!(self, PropertyRead::Value(_) | PropertyRead::Unset)
    }
}

/// Why an undefined name might be defined in the real build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InexactUnset {
    /// The walk refused a write of it (a value it could not evaluate), so the
    /// real build holds a value where the walk holds none.
    Refused,
    /// The environment may define it.
    Environment,
    /// MSBuild's toolset defines it before evaluation starts, and the walk
    /// does not model that one.
    Toolset,
    /// The walk passed content it could not see, which may define it.
    Opaque(UntrustedCause),
    /// A name the walk keeps inexact for its own consumers (`DefineConstants`).
    ConsumerCarveOut,
    /// MSBuild may reject the whole project, so no name has a value in it
    /// ([`crate::ParsedProject::rejection`]).
    Rejected(Box<crate::Rejection>),
}

impl InexactUnset {
    /// Why a read of `name`, undefined to the walk for this reason, may not be
    /// the real build's.
    pub fn cause(&self, name: &str) -> UntrustedCause {
        let undefined = |hidden_by: Option<&UntrustedCause>| UntrustedCause::UndefinedProperty {
            name: name.into(),
            hidden_by: hidden_by.map(|cause| Box::new(cause.clone())),
        };
        match self {
            InexactUnset::Refused => UntrustedCause::Refused { name: name.into() },
            InexactUnset::Opaque(cause) => undefined(Some(cause)),
            InexactUnset::Rejected(rejection) => UntrustedCause::Rejected(rejection.clone()),
            InexactUnset::Environment | InexactUnset::Toolset | InexactUnset::ConsumerCarveOut => {
                undefined(None)
            }
        }
    }
}

/// The read of every property name at the end of the walk, globals and
/// reserved names included: what `$(Name)` in a target running on the
/// evaluation would see.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyReads {
    /// The read of each name the walk holds an entry for (bound, or given a
    /// verdict such as a refusal), or whose read otherwise depends on the
    /// name, keyed by the lowercased name.
    pub named: HashMap<String, PropertyRead>,
    /// The read of a name not in [`Self::named`] and not one of MSBuild's
    /// toolset names: [`PropertyRead::Unset`], or, once the walk has passed
    /// content it could not see, [`InexactUnset::Opaque`], or, when MSBuild may
    /// reject the project, [`InexactUnset::Rejected`].
    pub otherwise: PropertyRead,
}

impl Default for PropertyReads {
    fn default() -> Self {
        Self {
            named: HashMap::new(),
            otherwise: PropertyRead::Unset,
        }
    }
}

impl PropertyReads {
    /// The read of `name`, compared case-insensitively.
    pub fn read(&self, name: &str) -> PropertyRead {
        let lower = name.to_ascii_lowercase();
        if let Some(read) = self.named.get(&lower) {
            return read.clone();
        }
        // No name has a value in a project MSBuild may reject, a toolset
        // name included.
        if let PropertyRead::UnsetInexact(InexactUnset::Rejected(_)) = &self.otherwise {
            return self.otherwise.clone();
        }
        if is_toolset_initial_property_name(&lower) {
            return PropertyRead::UnsetInexact(InexactUnset::Toolset);
        }
        self.otherwise.clone()
    }
}

impl State<'_> {
    /// What a read of `name` sees at the end of the walk.
    pub(super) fn read_property(&self, name: &str) -> PropertyRead {
        // MSBuild may hold no value for anything (`ParsedProject::rejection`).
        if let Some(rejection) = &self.rejection {
            let rejection = Box::new(rejection.clone());
            return if self.lookup.is_bound(name) {
                PropertyRead::Untrusted(UntrustedCause::Rejected(rejection))
            } else {
                PropertyRead::UnsetInexact(InexactUnset::Rejected(rejection))
            };
        }
        let trust = self.trust_of(name);
        if trust.reference_is_untrusted() {
            let cause = trust
                .untrusted_cause()
                .expect("an untrusted reference has a cause");
            return PropertyRead::Untrusted(cause);
        }
        // A value bound before content the walk could not see, or computed
        // from one, may have been rewritten there.
        if let Some(stale) = trust.stale() {
            return PropertyRead::Untrusted(UntrustedCause::of_opacity(stale));
        }
        // The entry's trust is the two questions answered just above. A value
        // that turns on MSBuild's startup directory is no one value; the
        // reader gets each, to collapse on what it reads if it can.
        if let Some(value) = self.lookup.get_unescaped_ignoring_trust(name) {
            return match value {
                Worlds::Same(value) => PropertyRead::Value(value),
                split @ Worlds::Split(_) => {
                    PropertyRead::Untrusted(UntrustedCause::StartupDirectory(Box::new(split)))
                }
            };
        }
        if self.undefined_read_is_exact(name) {
            return PropertyRead::Unset;
        }
        let lower = name.to_ascii_lowercase();
        let why = if trust.refused() {
            InexactUnset::Refused
        } else if self.env_property_names.contains(&lower) {
            InexactUnset::Environment
        } else if is_toolset_initial_property_name(&lower) {
            InexactUnset::Toolset
        } else if let Some(cause) = &self.walk_opaque {
            InexactUnset::Opaque(UntrustedCause::of_opacity(cause))
        } else {
            InexactUnset::ConsumerCarveOut
        };
        PropertyRead::UnsetInexact(why)
    }

    /// [`Self::read_property`] of every name, as [`PropertyReads`] holds it.
    ///
    /// A name outside the table's entries, the environment's names and the
    /// consumer carve-outs reads as `otherwise` or as a toolset name: its
    /// trust is certain and it is unbound, so `read_property` decides it on
    /// the walk's opacity and the toolset rule alone.
    pub(super) fn property_reads(&self) -> PropertyReads {
        let named = self
            .lookup
            .names()
            .map(str::to_string)
            .chain(self.env_property_names.iter().cloned())
            .chain(["defineconstants".to_string(), "targetframework".to_string()])
            .map(|lower| {
                let read = self.read_property(&lower);
                (lower, read)
            })
            .collect();
        let otherwise = match (&self.rejection, &self.walk_opaque) {
            (Some(rejection), _) => {
                PropertyRead::UnsetInexact(InexactUnset::Rejected(Box::new(rejection.clone())))
            }
            (None, Some(cause)) => {
                PropertyRead::UnsetInexact(InexactUnset::Opaque(UntrustedCause::of_opacity(cause)))
            }
            (None, None) => PropertyRead::Unset,
        };
        PropertyReads { named, otherwise }
    }
}
