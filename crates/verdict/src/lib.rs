//! Answers that can be incomplete, as types that cannot be read as complete.
//!
//! A lookup over data the producer may not have seen all of has three
//! outcomes, not two: it found the thing, it proved there is none, or it
//! cannot say. An `Option<T>` or a `bool` has room for two, so "provably
//! absent" and "didn't look" share a representation, and every consumer has
//! to remember a second fact (a `*_uncertain` flag, a `hidden_content`
//! cause) to tell them apart. A consumer that forgets reads "didn't look" as
//! "absent", and publishes a wrong answer.
//!
//! This crate gives the two shapes such an answer takes a type each:
//!
//! - [`Verdict`]: a value the producer commits to ([`Verdict::Certain`]), or
//!   why it does not ([`Verdict::Unknown`]). For an answer that has no
//!   "absent" case of its own: a list whose emptiness is itself the answer,
//!   say.
//! - [`Lookup`]: the answer to "is there one, and what is it?". It is
//!   [`Lookup::Found`], [`Lookup::ProvedAbsent`] or [`Lookup::Unknown`].
//!
//! The two are the same information: `Lookup<T, C>` is
//! `Verdict<Option<T>, C>`, and [`Lookup::into_verdict`] and
//! [`Verdict::into_lookup`] convert between them without loss.
//!
//! The cause `C` is the producer's own type, saying why it cannot answer.
//! Crossing from one producer's causes to another's is [`Verdict::map_cause`]
//! or [`Lookup::map_cause`].
//!
//! # Operations and their laws
//!
//! The operations are few, and each obeys the laws stated on it.
//! `tests/laws.rs` checks every law exhaustively over a finite domain,
//! including every function between its finite types.
//!
//! - **map:** [`Verdict::map`] and [`Lookup::map`] are functors.
//!   [`Verdict::map_cause`] and [`Lookup::map_cause`] are functors in the cause.
//! - **sequence:** [`Verdict::and_then`] and [`Lookup::and_then`] are monads,
//!   with [`Verdict::Certain`] and [`Lookup::Found`] as unit. `Unknown` (and,
//!   for a lookup, `ProvedAbsent`) passes through unchanged.
//! - **and:** [`Verdict::zip`] commits to both values when both are certain,
//!   and otherwise keeps the leftmost `Unknown`. Collecting an iterator of
//!   verdicts into a verdict of a collection ([`FromIterator`]) gives the
//!   leftmost `Unknown`, whatever the collection reads, and otherwise the
//!   certain collection; for a `Vec` it is a fold of [`Verdict::zip`]. It
//!   reads the source no further than its first `Unknown`.
//! - **or:** [`Lookup::or_shadowed`] is a search of an inner scope, then an
//!   outer one. An inner `Unknown` is never skipped: the inner scope may hold
//!   the name, and if it does, it shadows whatever the outer scope finds.
//!
//! # What is missing, deliberately
//!
//! Each of these would let an incomplete answer be read as a complete one,
//! so none exists:
//!
//! - **No conversion from `Option` or `bool`** (`From`, `Into`, a
//!   constructor taking one). Each would assert that the search behind the
//!   `None` or the `false` was complete. Every [`Lookup::ProvedAbsent`] is
//!   written as that variant where it is made, so the claim can be audited
//!   there.
//! - **No projection to `Option` or `bool`** (`ok`, `is_found`, `unwrap_or`,
//!   iteration). Each would merge `ProvedAbsent` or `Unknown` with another
//!   variant. A consumer `match`es.
//! - **No `Default`.** A default `Unknown` has no cause, and a default
//!   `ProvedAbsent` is an unproven absence.
//! - **No `or` on [`Verdict`].** Falling back to another value when the
//!   producer cannot commit is a guess, not a verdict.
//!
//! A best guess, where a consumer is entitled to one, is the producer's
//! separate data, never a payload of `Unknown`.
//!
//! ```compile_fail
//! // No conversion from `Option`:
//! let absent: borzoi_verdict::Lookup<u8, ()> = None::<u8>.into();
//! ```
//!
//! ```compile_fail
//! // No projection to `Option`:
//! let found: Option<u8> = borzoi_verdict::Lookup::<u8, ()>::ProvedAbsent.into();
//! ```
//!
//! ```compile_fail
//! // No conversion from `bool`:
//! let certain: borzoi_verdict::Verdict<(), ()> = true.into();
//! ```
//!
//! ```compile_fail
//! // No projection to `bool`:
//! let found: bool = borzoi_verdict::Lookup::<(), ()>::Found(()).into();
//! ```
//!
//! ```compile_fail
//! // No `Default`:
//! let unknown: borzoi_verdict::Lookup<u8, ()> = Default::default();
//! ```
//!
//! ```compile_fail
//! // No `Default`:
//! let unknown: borzoi_verdict::Verdict<u8, ()> = Default::default();
//! ```
//!
//! ```compile_fail
//! // No iteration, which would yield nothing for both `ProvedAbsent` and
//! // `Unknown`:
//! for _ in borzoi_verdict::Lookup::<u8, ()>::Found(1) {}
//! ```
//!
//! ```compile_fail
//! // No iteration of a verdict either:
//! for _ in borzoi_verdict::Verdict::<u8, ()>::Certain(1) {}
//! ```
//!
//! ```compile_fail
//! // No projection to `bool` by method:
//! let found = borzoi_verdict::Lookup::<u8, ()>::Found(1).is_found();
//! ```
//!
//! ```compile_fail
//! // No projection to `Option` by method:
//! let found = borzoi_verdict::Lookup::<u8, ()>::Found(1).ok();
//! ```
//!
//! ```compile_fail
//! // No fallback value:
//! let found = borzoi_verdict::Lookup::<u8, ()>::Found(1).unwrap_or(0);
//! ```
//!
//! These name the readings the docs above rule out. A reading can be added
//! under any other name, so `tests/pin.rs` pins the exact text of every file
//! under `src`: no change to the crate lands without a reviewed change to the
//! pin.
//!
//! ```compile_fail
//! // No `or` on a verdict:
//! let guess = borzoi_verdict::Verdict::<u8, ()>::Unknown(()).or(borzoi_verdict::Verdict::Certain(1));
//! ```
//!
//! The lines each of those blocks replaces compile:
//!
//! ```
//! use borzoi_verdict::{Lookup, Verdict};
//! let absent: Lookup<u8, ()> = Lookup::ProvedAbsent;
//! let found: Option<u8> = match Lookup::<u8, ()>::ProvedAbsent {
//!     Lookup::Found(value) => Some(value),
//!     Lookup::ProvedAbsent => None,
//!     Lookup::Unknown(()) => None,
//! };
//! let certain: Verdict<(), ()> = Verdict::Certain(());
//! let unknown: Verdict<u8, ()> = Verdict::Unknown(());
//! let guess = Verdict::<u8, ()>::Unknown(()).zip(Verdict::<u8, ()>::Certain(1));
//! # let _ = (absent, found, certain, unknown, guess);
//! ```

#![no_std]
#![forbid(unsafe_code)]

/// A value the producer commits to, or why it does not.
///
/// For an answer with no "absent" case of its own. Where there may be no
/// value, use [`Lookup`] (equivalently, `Verdict<Option<T>, C>`), so that
/// "there is none" is a certain answer and not a missing one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Verdict<T, C> {
    /// The producer commits to this value.
    Certain(T),
    /// The producer does not commit to any value, for this reason.
    Unknown(C),
}

/// The answer to "is there one, and what is it?", from a producer that may
/// not have seen everything.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Lookup<T, C> {
    /// There is one, and this is it.
    Found(T),
    /// There is none, and the producer saw everything that could hold one.
    ProvedAbsent,
    /// The producer cannot say whether there is one, for this reason.
    Unknown(C),
}

impl<T, C> Verdict<T, C> {
    /// The certain value transformed by `f`; an `Unknown` unchanged.
    ///
    /// Laws: `v.map(|x| x) == v`, and `v.map(f).map(g) == v.map(|x| g(f(x)))`.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Verdict<U, C> {
        match self {
            Verdict::Certain(value) => Verdict::Certain(f(value)),
            Verdict::Unknown(cause) => Verdict::Unknown(cause),
        }
    }

    /// The cause transformed by `f`; a certain value unchanged.
    ///
    /// Laws: `v.map_cause(|c| c) == v`, and
    /// `v.map_cause(f).map_cause(g) == v.map_cause(|c| g(f(c)))`.
    pub fn map_cause<D>(self, f: impl FnOnce(C) -> D) -> Verdict<T, D> {
        match self {
            Verdict::Certain(value) => Verdict::Certain(value),
            Verdict::Unknown(cause) => Verdict::Unknown(f(cause)),
        }
    }

    /// The verdict `f` gives on the certain value; an `Unknown` unchanged.
    ///
    /// Laws: `Certain(x).and_then(f) == f(x)`, `v.and_then(Certain) == v`,
    /// `v.and_then(f).and_then(g) == v.and_then(|x| f(x).and_then(g))`, and
    /// `Unknown(c).and_then(f) == Unknown(c)`.
    pub fn and_then<U>(self, f: impl FnOnce(T) -> Verdict<U, C>) -> Verdict<U, C> {
        match self {
            Verdict::Certain(value) => f(value),
            Verdict::Unknown(cause) => Verdict::Unknown(cause),
        }
    }

    /// Both values, when the producer commits to both; otherwise the leftmost
    /// `Unknown`.
    ///
    /// Laws: `v.zip(w) == v.and_then(|x| w.map(|y| (x, y)))`, and `zip` is
    /// associative up to regrouping the tuple.
    pub fn zip<U>(self, other: Verdict<U, C>) -> Verdict<(T, U), C> {
        match (self, other) {
            (Verdict::Certain(left), Verdict::Certain(right)) => Verdict::Certain((left, right)),
            (Verdict::Unknown(cause), _) | (Verdict::Certain(_), Verdict::Unknown(cause)) => {
                Verdict::Unknown(cause)
            }
        }
    }

    /// A verdict borrowing this one's value or cause.
    pub fn as_ref(&self) -> Verdict<&T, &C> {
        match self {
            Verdict::Certain(value) => Verdict::Certain(value),
            Verdict::Unknown(cause) => Verdict::Unknown(cause),
        }
    }
}

impl<T, C> Verdict<Option<T>, C> {
    /// The same answer as a [`Lookup`]: `Certain(Some(x))` is `Found(x)`,
    /// `Certain(None)` is `ProvedAbsent`, and `Unknown(c)` is `Unknown(c)`.
    ///
    /// Law: `v.into_lookup().into_verdict() == v`.
    pub fn into_lookup(self) -> Lookup<T, C> {
        match self {
            Verdict::Certain(Some(value)) => Lookup::Found(value),
            Verdict::Certain(None) => Lookup::ProvedAbsent,
            Verdict::Unknown(cause) => Lookup::Unknown(cause),
        }
    }
}

/// The first `Unknown` in the source, if it holds one before it ends;
/// otherwise `Certain` of the collection `V` makes of the certain values.
///
/// The source is read up to and including its first `Unknown`, or up to its
/// end, and never past either, whatever `V` does. A `V` that stops reading
/// early (an `Option` or a `Result` collection, at its first `None` or `Err`)
/// does not hide a later `Unknown`: the rest of the source is still checked.
/// A `V` that asks again after being told the values are over is told so
/// again. A source that ends and then yields more is read only to its first
/// end.
///
/// The collection is offered a size hint whose lower bound is zero, since
/// the source may hold an `Unknown`, after which no value is offered, and
/// whose upper bound is the source's.
///
/// Law: the result is `Unknown(c)` for the leftmost `Unknown(c)` of the
/// source, else `Certain` of what the collection makes of the source's values
/// offered under that size hint. For a collection whose result depends only on
/// the values it reads, that is `Certain(values.collect())`; for one that also
/// reads every value it is offered (a `Vec`), it is the fold of
/// [`Verdict::zip`] from `Certain` of the empty collection, appending each
/// certain value.
impl<T, C, V: FromIterator<T>> FromIterator<Verdict<T, C>> for Verdict<V, C> {
    fn from_iter<I: IntoIterator<Item = Verdict<T, C>>>(iter: I) -> Self {
        let mut source = UntilUnknown {
            source: iter.into_iter(),
            state: Reading::Values,
        };
        let values: V = (&mut source).collect();
        // `V` may have stopped before the source did; an `Unknown` it did not
        // read still decides the answer.
        while let Reading::Values = source.state {
            source.next();
        }
        match source.state {
            Reading::Unknown(cause) => Verdict::Unknown(cause),
            Reading::Values | Reading::Ended => Verdict::Certain(values),
        }
    }
}

/// How far [`UntilUnknown`] has read its source.
enum Reading<C> {
    /// Every verdict so far was certain, and the source has not ended.
    Values,
    /// The source ended with every verdict certain.
    Ended,
    /// The source yielded this cause, and is read no further.
    Unknown(C),
}

/// A source of verdicts read as the certain values before its first
/// `Unknown` or its first end, whichever comes first. Once either is reached
/// it yields nothing more, however often it is asked.
struct UntilUnknown<I, C> {
    source: I,
    state: Reading<C>,
}

impl<T, C, I: Iterator<Item = Verdict<T, C>>> Iterator for UntilUnknown<I, C> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if !matches!(self.state, Reading::Values) {
            return None;
        }
        match self.source.next() {
            Some(Verdict::Certain(value)) => Some(value),
            Some(Verdict::Unknown(cause)) => {
                self.state = Reading::Unknown(cause);
                None
            }
            None => {
                self.state = Reading::Ended;
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.state {
            Reading::Values => (0, self.source.size_hint().1),
            Reading::Ended | Reading::Unknown(_) => (0, Some(0)),
        }
    }
}

impl<T, C> Lookup<T, C> {
    /// The found value transformed by `f`; `ProvedAbsent` and `Unknown`
    /// unchanged.
    ///
    /// Laws: `l.map(|x| x) == l`, and `l.map(f).map(g) == l.map(|x| g(f(x)))`.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Lookup<U, C> {
        match self {
            Lookup::Found(value) => Lookup::Found(f(value)),
            Lookup::ProvedAbsent => Lookup::ProvedAbsent,
            Lookup::Unknown(cause) => Lookup::Unknown(cause),
        }
    }

    /// The cause transformed by `f`; `Found` and `ProvedAbsent` unchanged.
    ///
    /// Laws: `l.map_cause(|c| c) == l`, and
    /// `l.map_cause(f).map_cause(g) == l.map_cause(|c| g(f(c)))`.
    pub fn map_cause<D>(self, f: impl FnOnce(C) -> D) -> Lookup<T, D> {
        match self {
            Lookup::Found(value) => Lookup::Found(value),
            Lookup::ProvedAbsent => Lookup::ProvedAbsent,
            Lookup::Unknown(cause) => Lookup::Unknown(f(cause)),
        }
    }

    /// The lookup `f` gives on the found value; `ProvedAbsent` and `Unknown`
    /// unchanged.
    ///
    /// Laws: `Found(x).and_then(f) == f(x)`, `l.and_then(Found) == l`,
    /// `l.and_then(f).and_then(g) == l.and_then(|x| f(x).and_then(g))`,
    /// `ProvedAbsent.and_then(f) == ProvedAbsent`, and
    /// `Unknown(c).and_then(f) == Unknown(c)`.
    pub fn and_then<U>(self, f: impl FnOnce(T) -> Lookup<U, C>) -> Lookup<U, C> {
        match self {
            Lookup::Found(value) => f(value),
            Lookup::ProvedAbsent => Lookup::ProvedAbsent,
            Lookup::Unknown(cause) => Lookup::Unknown(cause),
        }
    }

    /// This lookup, an inner scope's, shadowing `outer`, the next scope out:
    /// what the inner scope found, else what the outer scope finds when the
    /// inner one proved it holds nothing, else the inner scope's `Unknown`.
    ///
    /// `outer` is called only when the inner scope proved it holds nothing.
    /// An inner `Unknown` is kept, not skipped: the inner scope may hold the
    /// name, and if it does, it shadows whatever the outer scope finds.
    ///
    /// Laws: `ProvedAbsent` is a two-sided identity
    /// (`ProvedAbsent.or_shadowed(|| l) == l == l.or_shadowed(|| ProvedAbsent)`),
    /// `Found` and `Unknown` are left zeros, and the operation is associative.
    pub fn or_shadowed(self, outer: impl FnOnce() -> Lookup<T, C>) -> Lookup<T, C> {
        match self {
            Lookup::Found(value) => Lookup::Found(value),
            Lookup::ProvedAbsent => outer(),
            Lookup::Unknown(cause) => Lookup::Unknown(cause),
        }
    }

    /// A lookup borrowing this one's value or cause.
    pub fn as_ref(&self) -> Lookup<&T, &C> {
        match self {
            Lookup::Found(value) => Lookup::Found(value),
            Lookup::ProvedAbsent => Lookup::ProvedAbsent,
            Lookup::Unknown(cause) => Lookup::Unknown(cause),
        }
    }

    /// The same answer as a [`Verdict`]: `Found(x)` is `Certain(Some(x))`,
    /// `ProvedAbsent` is `Certain(None)`, and `Unknown(c)` is `Unknown(c)`.
    ///
    /// Law: `l.into_verdict().into_lookup() == l`.
    pub fn into_verdict(self) -> Verdict<Option<T>, C> {
        match self {
            Lookup::Found(value) => Verdict::Certain(Some(value)),
            Lookup::ProvedAbsent => Verdict::Certain(None),
            Lookup::Unknown(cause) => Verdict::Unknown(cause),
        }
    }
}
