//! Every law the crate documents, checked exhaustively.
//!
//! The domain is finite: values are `0` and `1`, causes `'a'` and `'b'`. So a
//! verdict takes 4 values and a lookup 5, and every function the laws
//! quantify over is enumerated as a table over that domain. A value function
//! is a `[u8; 2]`, a verdict-valued one a `[Verdict; 2]`, and so on. Each law
//! is checked for every combination of its operands. The operations are
//! parametric in the value and cause types, so a law that holds over a
//! two-element domain with every function on it holds over any.

use std::cell::Cell;

use borzoi_verdict::{Lookup, Verdict};

type V = Verdict<u8, char>;
type L = Lookup<u8, char>;

const VALUES: [u8; 2] = [0, 1];
const CAUSES: [char; 2] = ['a', 'b'];

fn verdicts() -> Vec<V> {
    let mut all: Vec<V> = VALUES.iter().map(|&x| Verdict::Certain(x)).collect();
    all.extend(CAUSES.iter().map(|&c| Verdict::Unknown(c)));
    all
}

fn lookups() -> Vec<L> {
    let mut all: Vec<L> = VALUES.iter().map(|&x| Lookup::Found(x)).collect();
    all.push(Lookup::ProvedAbsent);
    all.extend(CAUSES.iter().map(|&c| Lookup::Unknown(c)));
    all
}

/// Every verdict on an optional value: what a lookup is the same answer as.
fn optional_verdicts() -> Vec<Verdict<Option<u8>, char>> {
    let mut all: Vec<Verdict<Option<u8>, char>> = vec![Verdict::Certain(None)];
    all.extend(VALUES.iter().map(|&x| Verdict::Certain(Some(x))));
    all.extend(CAUSES.iter().map(|&c| Verdict::Unknown(c)));
    all
}

/// Every function from a two-element domain into `range`, as a table.
fn tables<T: Copy>(range: &[T]) -> Vec<[T; 2]> {
    range
        .iter()
        .flat_map(|&at0| range.iter().map(move |&at1| [at0, at1]))
        .collect()
}

fn at<T: Copy>(table: [T; 2], x: u8) -> T {
    table[usize::from(x)]
}

fn at_cause<T: Copy>(table: [T; 2], c: char) -> T {
    table[CAUSES
        .iter()
        .position(|&k| k == c)
        .expect("a cause of the domain")]
}

#[test]
fn the_domain_is_what_the_laws_assume() {
    // Anti-vacuity: the enumerations are complete and distinct.
    assert_eq!(verdicts().len(), 4);
    assert_eq!(lookups().len(), 5);
    assert_eq!(optional_verdicts().len(), 5);
    assert_eq!(tables(&VALUES).len(), 4);
    assert_eq!(tables(&verdicts()).len(), 16);
    assert_eq!(tables(&lookups()).len(), 25);
    let distinct = |n: usize, items: Vec<String>| {
        let set: std::collections::BTreeSet<_> = items.into_iter().collect();
        assert_eq!(set.len(), n);
    };
    distinct(4, verdicts().iter().map(|v| format!("{v:?}")).collect());
    distinct(5, lookups().iter().map(|l| format!("{l:?}")).collect());
}

// ---- Verdict --------------------------------------------------------------

#[test]
fn verdict_map_is_a_functor() {
    for v in verdicts() {
        assert_eq!(v.map(|x| x), v);
        for f in tables(&VALUES) {
            for g in tables(&VALUES) {
                assert_eq!(
                    v.map(|x| at(f, x)).map(|x| at(g, x)),
                    v.map(|x| at(g, at(f, x))),
                    "{v:?} {f:?} {g:?}"
                );
            }
        }
    }
}

#[test]
fn verdict_map_cause_is_a_functor() {
    for v in verdicts() {
        assert_eq!(v.map_cause(|c| c), v);
        for f in tables(&CAUSES) {
            for g in tables(&CAUSES) {
                assert_eq!(
                    v.map_cause(|c| at_cause(f, c))
                        .map_cause(|c| at_cause(g, c)),
                    v.map_cause(|c| at_cause(g, at_cause(f, c))),
                    "{v:?} {f:?} {g:?}"
                );
            }
        }
    }
}

#[test]
fn verdict_map_leaves_unknown_and_map_cause_leaves_certain() {
    for v in verdicts() {
        for f in tables(&VALUES) {
            if let Verdict::Unknown(_) = v {
                assert_eq!(v.map(|x| at(f, x)), v);
            }
        }
        for f in tables(&CAUSES) {
            if let Verdict::Certain(_) = v {
                assert_eq!(v.map_cause(|c| at_cause(f, c)), v);
            }
        }
    }
}

#[test]
fn verdict_and_then_is_a_monad() {
    for f in tables(&verdicts()) {
        // Left identity.
        for x in VALUES {
            assert_eq!(Verdict::Certain(x).and_then(|y| at(f, y)), at(f, x));
        }
        // Unknown passes through.
        for c in CAUSES {
            assert_eq!(V::Unknown(c).and_then(|y| at(f, y)), V::Unknown(c));
        }
    }
    for v in verdicts() {
        // Right identity.
        assert_eq!(v.and_then(Verdict::Certain), v);
        // Associativity.
        for f in tables(&verdicts()) {
            for g in tables(&verdicts()) {
                assert_eq!(
                    v.and_then(|x| at(f, x)).and_then(|y| at(g, y)),
                    v.and_then(|x| at(f, x).and_then(|y| at(g, y))),
                    "{v:?} {f:?} {g:?}"
                );
            }
        }
    }
}

#[test]
fn verdict_zip_is_sequencing_and_keeps_the_leftmost_unknown() {
    for v in verdicts() {
        for w in verdicts() {
            assert_eq!(v.zip(w), v.and_then(|x| w.map(|y| (x, y))), "{v:?} {w:?}");
            let expected = match (v, w) {
                (Verdict::Certain(x), Verdict::Certain(y)) => Verdict::Certain((x, y)),
                (Verdict::Unknown(c), _) => Verdict::Unknown(c),
                (Verdict::Certain(_), Verdict::Unknown(c)) => Verdict::Unknown(c),
            };
            assert_eq!(v.zip(w), expected, "{v:?} {w:?}");
        }
    }
}

#[test]
fn verdict_zip_is_associative() {
    for u in verdicts() {
        for v in verdicts() {
            for w in verdicts() {
                assert_eq!(
                    u.zip(v).zip(w).map(|((a, b), c)| (a, (b, c))),
                    u.zip(v.zip(w)),
                    "{u:?} {v:?} {w:?}"
                );
            }
        }
    }
}

/// Every sequence of verdicts up to `max_len` long.
fn sequences(max_len: usize) -> Vec<Vec<V>> {
    let mut all = vec![vec![]];
    let mut frontier: Vec<Vec<V>> = vec![vec![]];
    for _ in 0..max_len {
        frontier = frontier
            .iter()
            .flat_map(|prefix| {
                verdicts().into_iter().map(move |v| {
                    let mut longer = prefix.clone();
                    longer.push(v);
                    longer
                })
            })
            .collect();
        all.extend(frontier.iter().cloned());
    }
    all
}

#[test]
fn verdict_collect_is_a_fold_of_zip() {
    let all = sequences(4);
    assert_eq!(all.len(), 1 + 4 + 16 + 64 + 256);
    for seq in all {
        let folded = seq.iter().fold(
            Verdict::Certain(Vec::new()),
            |acc: Verdict<Vec<u8>, char>, &v| {
                acc.zip(v).map(|(mut xs, x)| {
                    xs.push(x);
                    xs
                })
            },
        );
        let collected: Verdict<Vec<u8>, char> = seq.iter().copied().collect();
        assert_eq!(collected, folded, "{seq:?}");
    }
}

#[test]
fn verdict_collect_stops_at_the_first_unknown() {
    for seq in sequences(4) {
        let pulled = Cell::new(0usize);
        let _: Verdict<Vec<u8>, char> = seq
            .iter()
            .inspect(|_| pulled.set(pulled.get() + 1))
            .copied()
            .collect();
        let expected = seq
            .iter()
            .position(|v| matches!(v, Verdict::Unknown(_)))
            .map_or(seq.len(), |at| at + 1);
        assert_eq!(pulled.get(), expected, "{seq:?}");
    }
}

#[test]
fn verdict_as_ref_borrows_the_same_answer() {
    for v in verdicts() {
        assert_eq!(v.as_ref().map(|x| *x).map_cause(|c| *c), v);
    }
}

// ---- Lookup ---------------------------------------------------------------

#[test]
fn lookup_map_is_a_functor() {
    for l in lookups() {
        assert_eq!(l.map(|x| x), l);
        for f in tables(&VALUES) {
            for g in tables(&VALUES) {
                assert_eq!(
                    l.map(|x| at(f, x)).map(|x| at(g, x)),
                    l.map(|x| at(g, at(f, x))),
                    "{l:?} {f:?} {g:?}"
                );
            }
        }
    }
}

#[test]
fn lookup_map_cause_is_a_functor() {
    for l in lookups() {
        assert_eq!(l.map_cause(|c| c), l);
        for f in tables(&CAUSES) {
            for g in tables(&CAUSES) {
                assert_eq!(
                    l.map_cause(|c| at_cause(f, c))
                        .map_cause(|c| at_cause(g, c)),
                    l.map_cause(|c| at_cause(g, at_cause(f, c))),
                    "{l:?} {f:?} {g:?}"
                );
            }
        }
    }
}

#[test]
fn lookup_map_and_map_cause_leave_the_other_variants() {
    for l in lookups() {
        for f in tables(&VALUES) {
            if !matches!(l, Lookup::Found(_)) {
                assert_eq!(l.map(|x| at(f, x)), l);
            }
        }
        for f in tables(&CAUSES) {
            if !matches!(l, Lookup::Unknown(_)) {
                assert_eq!(l.map_cause(|c| at_cause(f, c)), l);
            }
        }
    }
}

#[test]
fn lookup_and_then_is_a_monad() {
    for f in tables(&lookups()) {
        // Left identity.
        for x in VALUES {
            assert_eq!(Lookup::Found(x).and_then(|y| at(f, y)), at(f, x));
        }
        // ProvedAbsent and Unknown pass through.
        assert_eq!(L::ProvedAbsent.and_then(|y| at(f, y)), L::ProvedAbsent);
        for c in CAUSES {
            assert_eq!(L::Unknown(c).and_then(|y| at(f, y)), L::Unknown(c));
        }
    }
    for l in lookups() {
        // Right identity.
        assert_eq!(l.and_then(Lookup::Found), l);
        // Associativity.
        for f in tables(&lookups()) {
            for g in tables(&lookups()) {
                assert_eq!(
                    l.and_then(|x| at(f, x)).and_then(|y| at(g, y)),
                    l.and_then(|x| at(f, x).and_then(|y| at(g, y))),
                    "{l:?} {f:?} {g:?}"
                );
            }
        }
    }
}

#[test]
fn or_shadowed_has_proved_absent_as_identity() {
    for l in lookups() {
        assert_eq!(L::ProvedAbsent.or_shadowed(|| l), l, "{l:?}");
        assert_eq!(l.or_shadowed(|| L::ProvedAbsent), l, "{l:?}");
    }
}

#[test]
fn or_shadowed_never_looks_past_a_found_or_an_unknown_inner_scope() {
    for outer in lookups() {
        for x in VALUES {
            assert_eq!(L::Found(x).or_shadowed(|| outer), L::Found(x), "{outer:?}");
        }
        // The inner scope may hold the name and shadow whatever the outer one
        // finds, so its doubt is the answer.
        for c in CAUSES {
            assert_eq!(
                L::Unknown(c).or_shadowed(|| outer),
                L::Unknown(c),
                "{outer:?}"
            );
        }
    }
}

#[test]
fn or_shadowed_is_associative() {
    for x in lookups() {
        for y in lookups() {
            for z in lookups() {
                assert_eq!(
                    x.or_shadowed(|| y).or_shadowed(|| z),
                    x.or_shadowed(|| y.or_shadowed(|| z)),
                    "{x:?} {y:?} {z:?}"
                );
            }
        }
    }
}

#[test]
fn or_shadowed_asks_the_outer_scope_only_when_the_inner_one_holds_nothing() {
    for inner in lookups() {
        for outer in lookups() {
            let asked = Cell::new(0usize);
            let _ = inner.or_shadowed(|| {
                asked.set(asked.get() + 1);
                outer
            });
            let expected = usize::from(inner == L::ProvedAbsent);
            assert_eq!(asked.get(), expected, "{inner:?} {outer:?}");
        }
    }
}

#[test]
fn lookup_as_ref_borrows_the_same_answer() {
    for l in lookups() {
        assert_eq!(l.as_ref().map(|x| *x).map_cause(|c| *c), l);
    }
}

// ---- The isomorphism -----------------------------------------------------

#[test]
fn lookup_and_optional_verdict_are_the_same_answer() {
    for l in lookups() {
        assert_eq!(l.into_verdict().into_lookup(), l, "{l:?}");
    }
    for v in optional_verdicts() {
        assert_eq!(v.into_lookup().into_verdict(), v, "{v:?}");
    }
    // The correspondence is the documented one, variant by variant.
    assert_eq!(L::ProvedAbsent.into_verdict(), Verdict::Certain(None));
    for x in VALUES {
        assert_eq!(L::Found(x).into_verdict(), Verdict::Certain(Some(x)));
    }
    for c in CAUSES {
        assert_eq!(L::Unknown(c).into_verdict(), Verdict::Unknown(c));
    }
}

#[test]
fn the_isomorphism_commutes_with_map_and_and_then() {
    for l in lookups() {
        for f in tables(&VALUES) {
            assert_eq!(
                l.map(|x| at(f, x)).into_verdict(),
                l.into_verdict().map(|o| o.map(|x| at(f, x))),
                "{l:?} {f:?}"
            );
        }
        for f in tables(&lookups()) {
            assert_eq!(
                l.and_then(|x| at(f, x)).into_verdict(),
                l.into_verdict().and_then(|o| match o {
                    Some(x) => at(f, x).into_verdict(),
                    None => Verdict::Certain(None),
                }),
                "{l:?} {f:?}"
            );
        }
        for f in tables(&CAUSES) {
            assert_eq!(
                l.map_cause(|c| at_cause(f, c)).into_verdict(),
                l.into_verdict().map_cause(|c| at_cause(f, c)),
                "{l:?} {f:?}"
            );
        }
    }
}
