//! The env build reads each reference's friend declarations against the
//! consuming project's name (`build_env_from_dll_paths`'s `consumer`), and a
//! reference that may name the project as a friend grades the env's public
//! view incomplete.
//!
//! The reference is the SDK's `System.Runtime.CompilerServices.VisualC.dll`,
//! whose one declaration names `mscorlib` (pinned by `borzoi-assembly`'s
//! `friend_declarations` census). The resolution-level grading against FCS is
//! `borzoi-sema`'s `friend_assembly_grid`.

use borzoi::assembly_cache::AssemblyCache;
use borzoi::semantic::build_env_from_dll_paths;
use borzoi_sema::ConsumerName;

use crate::common::ensure_system_runtime_dll;

#[test]
fn a_reference_naming_the_consumer_withdraws_the_public_view() {
    let visual_c = ensure_system_runtime_dll()
        .parent()
        .expect("System.Runtime.dll sits in a ref dir")
        .join("System.Runtime.CompilerServices.VisualC.dll");
    let incomplete = |consumer: ConsumerName| {
        let (env, kept) = build_env_from_dll_paths(
            std::iter::once(visual_c.as_path()),
            &consumer,
            &AssemblyCache::disabled(),
            &borzoi_msbuild::observed::Observer::new(),
        );
        assert_eq!(
            kept,
            std::slice::from_ref(&visual_c),
            "the reference is read"
        );
        assert!(!env.identities_incomplete(), "its identity is known");
        env.public_view_incomplete()
    };
    assert!(
        incomplete(ConsumerName::Known("mscorlib".to_string())),
        "a friend sees internals the public view skips"
    );
    assert!(
        incomplete(ConsumerName::Unknown),
        "an unknown consumer may be the friend"
    );
    assert!(
        !incomplete(ConsumerName::Known("App".to_string())),
        "a consumer the declarations do not name sees the public view"
    );
    assert!(
        !incomplete(ConsumerName::Known("MSCORLIB".to_string())),
        "FCS compares names ordinally"
    );
}
