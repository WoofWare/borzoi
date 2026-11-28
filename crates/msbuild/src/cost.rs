//! Counts of the walk's work, for the tests that hold its cost to a bound
//! (`tests/deep_nesting.rs`): a count is the same on a loaded machine and an
//! idle one, where a wall-clock time is not. Each count is kept only under
//! `test` or the `test-support` feature, per thread, and read through
//! `test_support::count_walk_costs`; elsewhere counting is a no-op.
//!
//! A count bounds the work the counted operation does, and nothing else: a
//! test over it says that operation is linear, not that the walk around it
//! is. Work a change adds outside a counted operation (a search before it, a
//! lookup replaced by a scan) is not seen, so code that does such work on a
//! path a test bounds counts it here, in a field of its own.

/// The work one walk did, by kind.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct WalkCosts {
    /// The `<When>` gates `rejection::arm_is_dead` decided.
    pub arm_gate_decisions: u64,
    /// The writes on a speculative walk's paths the item pass examined,
    /// judging the groups deferred from it: each name once, settling which
    /// are not certain, and each write of a name a group's judgement reads
    /// (`PathOf::reaches`).
    pub path_writes_examined: u64,
    /// The texts `condition::strike` built, each in one pass over its text.
    pub strikes: u64,
    /// The bytes `condition::strike` copied, building them.
    pub struck_bytes: u64,
    /// The `<UsingTask>` values `rejection::registration_value` expanded
    /// for the registration's rules.
    pub registration_expansions: u64,
    /// The comparisons of two names `loader::first_repeat` made, finding a
    /// repeated parameter name.
    pub name_comparisons: u64,
    /// The second walks an evaluation ran, judging a name refused then
    /// rebound as certain (`evaluator::rejection`'s module docs): one
    /// wherever the first walk rebound such a name.
    pub second_walks: u64,
    /// The lookups and comparisons the first walk made adopting the second
    /// walk's sites (`State::adopt_second_walk`), placing them among its own.
    pub site_merge_probes: u64,
    /// The property writes the first walk stored.
    pub property_writes: u64,
    /// The property writes the second walk stored: the work it adds, as a
    /// share of [`Self::property_writes`].
    pub second_walk_property_writes: u64,
    /// The groups the first walk judged from a path the walk did not take
    /// on which a name whose only doubt is a refusal's mark reaches the group
    /// (`PathOf::reaches`): a narrower trigger for the second walk than the
    /// one it runs on, kept as a census, and counted only where the caller
    /// asks (`test_support::with_refusal_census`).
    pub refusal_paths: u64,
    /// The fragment keys MSBuild's batch of `Update`s was asked about
    /// (`item_pass::batch_fragment_key`).
    pub batch_keys: u64,
    /// The keys copied into another outcome of MSBuild's batch of `Update`s
    /// (`item_pass::copy_world`).
    pub batch_keys_copied: u64,
    /// The bytes of those keys, and of the keys two outcomes were compared
    /// by.
    pub batch_bytes_copied: u64,
    /// The most bytes of keys one outcome of a batch of `Update`s held at
    /// once (`item_pass::UpdateBatchRun::insert`): a peak, not a sum.
    pub batch_bytes_held_peak: u64,
    /// The `Update` specs the batch of `Update`s expanded to feed itself
    /// (`item_pass::feed_update_batch`).
    pub batch_spec_expansions: u64,
    /// The fragments of `Update` specs the batch read
    /// (`item_pass::batch_fragments`).
    pub batch_fragments_read: u64,
    /// The texts the item pass expanded silently, to judge rather than to
    /// record (`item_pass::expand_silent`).
    pub silent_expansions: u64,
    /// The expanded `Update` specs the batch checked whole for an item
    /// expression holding a `;` (`item_pass::SplitSpec::of`).
    pub batch_specs_split: u64,
}

/// Whether the caller asked for `WalkCosts::refusal_paths`'s census on
/// this thread ([`crate::test_support::with_refusal_census`]): it costs work
/// in each group the walk judges from a path, so nothing else pays it.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn census_requested() -> bool {
    CENSUS.with(std::cell::Cell::get)
}

/// [`census_requested`]'s flag, set for the span of a closure.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn with_census<T>(walk: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            CENSUS.with(|census| census.set(self.0));
        }
    }
    let _restore = Restore(CENSUS.with(|census| census.replace(true)));
    walk()
}

#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static CENSUS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static COSTS: std::cell::Cell<WalkCosts> = const {
        std::cell::Cell::new(WalkCosts {
            arm_gate_decisions: 0,
            path_writes_examined: 0,
            strikes: 0,
            struck_bytes: 0,
            name_comparisons: 0,
            registration_expansions: 0,
            second_walks: 0,
            site_merge_probes: 0,
            property_writes: 0,
            second_walk_property_writes: 0,
            refusal_paths: 0,
            batch_keys: 0,
            batch_keys_copied: 0,
            batch_bytes_copied: 0,
            batch_bytes_held_peak: 0,
            batch_spec_expansions: 0,
            batch_fragments_read: 0,
            silent_expansions: 0,
            batch_specs_split: 0,
        })
    };
}

/// Count work of the kind `add` adds to.
#[cfg_attr(not(any(test, feature = "test-support")), allow(unused_variables))]
pub(crate) fn count(add: impl FnOnce(&mut WalkCosts)) {
    #[cfg(any(test, feature = "test-support"))]
    COSTS.with(|costs| {
        let mut held = costs.get();
        add(&mut held);
        costs.set(held);
    });
}

/// The work counted on this thread since the last [`take`], and start again.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn take() -> WalkCosts {
    COSTS.with(|costs| costs.replace(WalkCosts::default()))
}
