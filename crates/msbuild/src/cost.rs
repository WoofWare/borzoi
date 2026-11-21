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
}

#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static COSTS: std::cell::Cell<WalkCosts> = const {
        std::cell::Cell::new(WalkCosts {
            arm_gate_decisions: 0,
            path_writes_examined: 0,
            strikes: 0,
            struck_bytes: 0,
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
