#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_len verus_code! {
        use vstd::set::*;

        proof fn test_len<A>(s: Set<A>) {
            assert(s.len() as int >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_len_fails verus_code! {
        use vstd::set::*;

        proof fn test_len<A>(s1: Set<A>, s2: Set<A>) {
            assert(s1.len() == s2.len()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::iset::*;
        use vstd::iset_lib::*;

        proof fn test_set() {
            let nonneg = ISet::new(|i: int| i >= 0);
            assert(forall|i: int| nonneg.contains(i) == (i >= 0));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall|i: int| pos1.contains(i) == (i > 0));
            let pos2 = nonneg.map(|i: int| i + 1);
            assert forall|i: int| pos2.contains(i) == (i > 0) by {
                assert(pos2.contains(i) == nonneg.contains(i - 1));
            }
            assert(forall|i: int| pos2.contains(i) == (i > 0));
            assert(pos1 =~= pos2);
            assert(pos1 == pos2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        use vstd::iset::*;

        pub closed spec fn set_map<A>(s: ISet<A>, f: spec_fn(A) -> A) -> ISet<A> {
            ISet::new(|a: A| exists|x: A| s.contains(x) && a == f(x))
        }

        proof fn test_set() {
            let nonneg = ISet::new(|i: int| i >= 0);
            assert(forall|i: int| nonneg.contains(i) == (i >= 0));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall|i: int| pos1.contains(i) == (i > 0));
            let pos2 = set_map(nonneg, |i: int| i + 1);
            assert forall|i: int| pos2.contains(i) == (i > 0) by {} // FAILS
            assert(forall|i: int| pos2.contains(i) == (i > 0));
            assert(pos1 =~= pos2);
            assert(pos1 == pos2);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_choose_assert_witness verus_code! {
        use vstd::iset::*;

        #[verifier(opaque)]
        spec fn f(x: int) -> bool {
            true
        }

        proof fn test_witness() {
            assume(exists|x: int| f(x));

            let s = ISet::new(|x: int| f(x));
            assert(exists|x: int| f(x) && s.contains(x));

            assert(s.contains(s.choose()));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_choose_fails_witness verus_code! {
        use vstd::iset::*;

        #[verifier(opaque)]
        spec fn f(x: int) -> bool {
            true
        }

        proof fn test_witness() {
            assume(exists|x: int| f(x));

            let s = ISet::new(|x: int| f(x));

            assert(s.contains(s.choose())); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_iset_fold verus_code! {
        use vstd::iset::*;

        proof fn test() {
            let s: ISet<nat> = iset![9];
            broadcast use {fold::lemma_fold_insert, fold::lemma_fold_empty};
            assert(s.finite());
            assert(s.len() > 0);
            assert(s.fold(0, |p: nat, a: nat| p + a) == 9);

            assert(iset![].fold(0, |p: nat, a: nat| p + a) == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_set_fold verus_code! {
        use vstd::iset::*;
        use vstd::set::*;

        proof fn test() {
            let s: Set<nat> = set![9];
            assert(s.to_iset() =~= iset![9]);
            broadcast use {vstd::iset::fold::lemma_fold_insert, vstd::iset::fold::lemma_fold_empty};
            assert(s.len() > 0);
            assert(s.fold(0, |p: nat, a: nat| p + a) == 9);

            let s2: Set<nat> = set![];
            assert(s2.to_iset() =~= iset![]);
            assert(s2.fold(0, |p: nat, a: nat| p + a) == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_map_by verus_code! {
        use vstd::set::*;

        proof fn test<A, B>(sa: Set<A>, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A)
            requires
                forall|a: A| sa.contains(a) ==> rev(fwd(a)) == a,
        {
            assert(sa.map(fwd) =~= sa.map_by(fwd, rev));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_set_build verus_code! {
        use vstd::iset::*;
        use vstd::set::*;

        proof fn test1() {
            let s = set_build!{ (x, x): (u8, u8) | x: u8 };
            let z = ISet::new(|p: (u8, u8)| p.0 == p.1);
            assert(s.congruent(z));
        }

        proof fn test2() {
            let s = set_build!{ (x, x): (u8, u8) | exists x: u8 };
            let z = ISet::new(|p: (u8, u8)| p.0 == p.1);

            // assert(s == z); // FAILS by itself, because of the "exists x: u8"

            assert(s.congruent(z)) by {
                assert forall|p: (u8, u8)| p.0 == p.1 implies #[trigger] s.contains(p) by {
                    // Exhibit the witness x of type u8 to trigger the "exists":
                    assert(set_build!{ x: u8 }.contains(p.0));
                }
            }
        }

        proof fn test3() {
            let s = set_build!{ (x, y, x - y): (int, int, int) | x: int in 10..20, y: int in x..20, x + y != 25 };
            let z = ISet::new(|t: (int, int, int)| 10 <= t.0 < 20 && t.0 <= t.1 < 20 && t.0 + t.1 != 25 && t.2 == t.0 - t.1);
            assert(s.congruent(z));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_set_new_assuming_finite verus_code! {
        use vstd::iset::*;
        use vstd::iset_lib::*;
        use vstd::set::*;

        #[allow(deprecated)]
        proof fn test(a: int) {
            lemma_int_range(0, 42);
            assert(ISet::new(|x: int| 0 <= x < 42) =~= set_int_range(0, 42));
            let s = Set::<int>::new_assuming_finite(|x: int| 0 <= x < 42);
            assert(s.contains(a) == (0 <= a < 42));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_set_new_assuming_finite_infinite_fails verus_code! {
        use vstd::set::*;

        #[allow(deprecated)]
        proof fn test(a: int) {
            let s = Set::<int>::new_assuming_finite(|x: int| true);
            assert(s.contains(a)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_set_new_assuming_finite_false_fails verus_code! {
        use vstd::iset_lib::*;
        use vstd::set::*;

        proof fn contradiction(s: Set<int>)
            requires
                forall|a: int| s.contains(a),
            ensures
                false,
        {
            lemma_to_iset_finite(s);
            lemma_to_iset_len(s);
            let n = s.len() as int;
            lemma_int_range(0, n + 1);
            assert(set_int_range(0, n + 1).subset_of(s.to_iset()));
            lemma_len_subset(set_int_range(0, n + 1), s.to_iset());
            assert(n + 1 <= n);
        }

        #[allow(deprecated)]
        proof fn test() {
            let s = Set::<int>::new_assuming_finite(|x: int| true);
            contradiction(s); // FAILS
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}
