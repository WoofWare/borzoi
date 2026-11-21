//! Counts of the walk's work, for the tests that hold its cost to a bound
//! (`tests/deep_nesting.rs`): a count is the same on a loaded machine and an
//! idle one, where a wall-clock time is not. Each count is kept only under
//! `test` or the `test-support` feature, per thread, and read through
//! `test_support::count_walk_costs`; elsewhere counting is a no-op.

/// The work one walk did, by kind.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct WalkCosts {
    /// The `<When>` gates `rejection::arm_is_dead` decided.
    pub arm_gate_decisions: u64,
    /// The `<UsingTask>` values `rejection::registration_value` expanded
    /// for the registration's rules.
    pub registration_expansions: u64,
    /// The comparisons of two names `loader::first_repeat` made, finding a
    /// repeated parameter name.
    pub name_comparisons: u64,
}

#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static COSTS: std::cell::Cell<WalkCosts> = const {
        std::cell::Cell::new(WalkCosts {
            arm_gate_decisions: 0,
            name_comparisons: 0,
            registration_expansions: 0,
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
