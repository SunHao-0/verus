#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_map_from_set verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map_new() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s1, |k: int| 10 * k);
            assert(m1[2] == 20);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s1, |k: int| 10 * k);
            assert(m1.index(2) == 20);
            let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
            let m2 = Map::new(s2, |k: int| 3 * k + 7 * k);
            assert(m1 =~= m2);
            let m3 = map![10int => true ==> false, 20int => false ==> true];
            assert(!m3.index(10));
            assert(m3.index(20));
            let m4 = map![10int => true ==> false, 20int => false ==> true,];
            assert(!m4.index(10));
            assert(m4.index(20));
        }

        proof fn testfun_eq() {
            let s = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s, |x: int| x + 4);
            let m2 = Map::new(s, |y: int| y + (2 + 2));
            // m1 and m2 are equal even without extensional equality:
            assert(equal(m1, m2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s1, |k: int| 10 * k);
            assert(m1.index(2) == 20);
            assert(m1.index(4) == 40); // FAILS
            let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
            let m2 = Map::new(s2, |k: int| 3 * k + 7 * k);
            assert(m1 =~= m2);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s1, |k: int| 10 * k);
            assert(m1.index(2) == 20);
            let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
            let m2 = Map::new(s2, |k: int| 3 * k + 8 * k);
            assert(equal(m1, m2)) by {} // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails_subtype verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s1, |k: int| 10 * k);
            let m3: Map<int, int> = m1;
            let m4: Map<nat, int> = m1; // FAILS: see https://github.com/FStarLang/FStar/issues/1542
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test1_fails_eq verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        #[verifier::auto_ext_equal(/* no auto_ext_equal */)]
        proof fn testfun_eq() {
            let s = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = Map::new(s, |x: int| x + 4);
            let m2 = Map::new(s, |y: int| (2 + 2) + y);
            // would require extensional equality:
            assert(m1 == m2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] map_contains verus_code! {
        use vstd::set::*;
        use vstd::map::*;
        use vstd::map_lib::group_map_extra;

        proof fn test() {
            broadcast use group_map_extra;

            let m = map![10int => 100int, 20int => 200int];
            assert(m.contains_key(10));
            assert(m.contains_value(200));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_insert_implies_contains verus_code! {
        use vstd::set::*;
        use vstd::map::*;
        use vstd::map_lib::group_map_extra;

        proof fn test(m: Map<int, int>) {
            broadcast use group_map_extra;

            let m2 = m.insert(1int, 2int).insert(3int, 4int);
            assert(m2.contains_key(1));
            assert(m2.contains_value(4));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_overwrite verus_code! {
        use vstd::set::*;
        use vstd::map::*;
        use vstd::map_lib::group_map_extra;

        proof fn test() {
            broadcast use group_map_extra;

            let m = map![
                1int => 1int,
                2int => 3int,
            ].insert(1, 2).insert(2, 4);

            // inclusions
            assert(m.contains_value(2));
            assert(m.contains_value(4));

            // non-inclusions
            assert(!m.contains_value(1));
            assert(!m.contains_value(3));
            assert(!m.contains_value(5));

            // overwrite one of the keys
            let m2 = m.insert(1, 3);
            assert(m.insert(1, 3).contains_value(3)); // it has the new value
            assert(!m.insert(1, 3).contains_value(2)); // it does not have the old value
            assert(m.insert(1, 3).contains_value(4)); // it retains the unrelated value from the other key
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_choose_regression_408 verus_code! {
        use vstd::set::Set;
        proof fn choose_contains_set(m: Set<nat>)
            requires m.finite(), m.len() > 0
        {
            let c = m.choose();
            assert(m.contains(c));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_tracked_union_prefer_right_rejects_spec_right verus_code! {
        use vstd::set::*;
        use vstd::map::*;
        use vstd::cell::pcell::*;

        proof fn conjure<V>(v: V) -> (tracked out: V)
            ensures
                out == v,
        {
            let tracked mut m = Map::<int, V>::tracked_empty();
            let ghost right = Map::<int, V>::empty().insert(0, v);
            m.tracked_union_prefer_right(right);
            assert(m.dom() =~= Set::<int>::empty().insert(0));
            assert(m[0] == v);
            m.tracked_remove(0)
        }

        proof fn contradiction(tracked p: PointsTo<u64>)
            ensures
                false,
        {
            let ghost g = p;
            let tracked mut p2 = conjure(g);
            assert(p2 == p);
            p2.is_exclusive(&p);
            assert(p2.id() != p.id());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] imap_tracked_union_prefer_right_rejects_spec_right verus_code! {
        use vstd::iset::*;
        use vstd::imap::*;
        use vstd::cell::pcell::*;

        proof fn conjure<V>(v: V) -> (tracked out: V)
            ensures
                out == v,
        {
            let tracked mut m = IMap::<int, V>::tracked_empty();
            let ghost right = IMap::<int, V>::empty().insert(0, v);
            m.tracked_union_prefer_right(right);
            assert(m.dom() =~= ISet::<int>::empty().insert(0));
            assert(m[0] == v);
            m.tracked_remove(0)
        }

        proof fn contradiction(tracked p: PointsTo<u64>)
            ensures
                false,
        {
            let ghost g = p;
            let tracked mut p2 = conjure(g);
            assert(p2 == p);
            p2.is_exclusive(&p);
            assert(p2.id() != p.id());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] map_tracked_union_prefer_right_tracked_right verus_code! {
        use vstd::set::*;
        use vstd::map::*;
        use vstd::cell::pcell::*;

        fn test() {
            let (c, Tracked(p)) = PCell::<u64>::new(5);
            proof {
                let tracked mut left = Map::<int, PointsTo<u64>>::tracked_empty();
                let tracked mut right = Map::<int, PointsTo<u64>>::tracked_empty();
                right.tracked_insert(0, p);
                left.tracked_union_prefer_right(right);
                assert(left.dom() =~= Set::<int>::empty().insert(0));
                let tracked q = left.tracked_remove(0);
                assert(q.id() == c.id());
                assert(*q.value() == 5u64);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] imap_tracked_union_prefer_right_tracked_right verus_code! {
        use vstd::iset::*;
        use vstd::imap::*;
        use vstd::cell::pcell::*;

        fn test() {
            let (c, Tracked(p)) = PCell::<u64>::new(5);
            proof {
                let tracked mut left = IMap::<int, PointsTo<u64>>::tracked_empty();
                let tracked mut right = IMap::<int, PointsTo<u64>>::tracked_empty();
                right.tracked_insert(0, p);
                left.tracked_union_prefer_right(right);
                assert(left.dom() =~= ISet::<int>::empty().insert(0));
                let tracked q = left.tracked_remove(0);
                assert(q.id() == c.id());
                assert(*q.value() == 5u64);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_tracked_union_prefer_right_overlapping_key verus_code! {
        use vstd::set::*;
        use vstd::map::*;
        use vstd::cell::pcell::*;

        fn test() {
            let (_c1, Tracked(p1)) = PCell::<u64>::new(5);
            let (c2, Tracked(p2)) = PCell::<u64>::new(7);
            proof {
                let tracked mut left = Map::<int, PointsTo<u64>>::tracked_empty();
                left.tracked_insert(0, p1);
                let tracked mut right = Map::<int, PointsTo<u64>>::tracked_empty();
                right.tracked_insert(0, p2);
                left.tracked_union_prefer_right(right);
                let tracked q = left.tracked_remove(0);
                assert(q.id() == c2.id());
                assert(*q.value() == 7u64);
            }
        }
    } => Ok(())
}
