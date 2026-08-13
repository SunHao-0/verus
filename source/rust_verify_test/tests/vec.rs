#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_vec_into_iter verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::vec::*;

        fn test() {
            let mut v1: Vec<u32> = Vec::new();
            let mut v2: Vec<u32> = Vec::new();
            v1.push(3);
            v1.push(4);
            assert(v1@ == seq![3u32, 4u32]);

            v2.push(5);
            assert(v2.len() == 1);
            v2.push(7);
            assert(v2@.len() == 2);
            v2.insert(1, 6);
            assert(v2@ == seq![5u32, 6u32, 7u32]);

            v1.append(&mut v2);
            assert(v2@.len() == 0);
            assert(v1@.len() == 5);
            assert(v1@ == seq![3u32, 4u32, 5u32, 6u32, 7u32]);
            v1.remove(2);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32]);

            v1.push(8u32);
            v1.push(9u32);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

            v1.swap_remove(5);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32]);

            let mut i: usize = 0;
            for x in it: v1
                invariant
                    i == it.index(),
                    it.seq() == seq![3u32, 4u32, 6u32, 7u32, 8u32],
            {
                assert(x > 2);
                assert(x < 10);
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_vec_dec verus_code! {
        use vstd::prelude::*;
        struct Tree {
            children: Vec<Tree>,
        }

        fn recurse(tree: &Tree)
            decreases *tree
        {
            if tree.children.len() > 0 {
                recurse(&tree.children[0]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vec_push_length_overflow verus_code! {
        use vstd::prelude::*;

        fn fill_to_max() -> (v: Vec<()>)
            ensures
                v@.len() == usize::MAX,
        {
            vec![(); usize::MAX]
        }

        fn overflow(v: &mut Vec<()>)
            requires
                old(v)@.len() == usize::MAX,
            ensures
                false,
        {
            v.push(()); // FAILS
            let n = v.len();
            assert(n == v@.len());
        }

        fn derive() {
            let mut v = fill_to_max();
            overflow(&mut v);
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] vec_insert_length_overflow verus_code! {
        use vstd::prelude::*;

        fn overflow(v: &mut Vec<()>)
            requires
                old(v)@.len() == usize::MAX,
            ensures
                false,
        {
            v.insert(0, ()); // FAILS
            let n = v.len();
            assert(n == v@.len());
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] vec_append_length_overflow verus_code! {
        use vstd::prelude::*;

        fn overflow(v: &mut Vec<()>, other: &mut Vec<()>)
            requires
                old(v)@.len() == usize::MAX,
                old(other)@.len() == 1,
            ensures
                false,
        {
            v.append(other); // FAILS
            let n = v.len();
            assert(n == v@.len());
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] vec_extend_from_slice_length_overflow verus_code! {
        use vstd::prelude::*;

        fn overflow(v: &mut Vec<()>, other: &[()])
            requires
                old(v)@.len() == usize::MAX,
                other@.len() == 1,
            ensures
                false,
        {
            v.extend_from_slice(other); // FAILS
            let n = v.len();
            assert(n == v@.len());
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] vec_growth_within_bounds verus_code! {
        use vstd::prelude::*;

        fn push_when_there_is_room(v: &mut Vec<u32>, x: u32)
            requires
                old(v)@.len() < usize::MAX,
            ensures
                final(v)@ == old(v)@.push(x),
        {
            v.push(x);
        }

        fn extend_when_there_is_room(v: &mut Vec<u32>, other: &[u32])
            requires
                old(v)@.len() + other@.len() <= usize::MAX,
            ensures
                final(v)@.len() == old(v)@.len() + other@.len(),
        {
            v.extend_from_slice(other);
        }

        fn copy_slice(src: &[u32]) -> (dst: Vec<u32>)
            ensures
                dst@ == src@,
        {
            let mut dst: Vec<u32> = Vec::new();
            let mut i: usize = 0;
            while i < src.len()
                invariant
                    i <= src@.len(),
                    dst@ == src@.take(i as int),
                decreases src@.len() - i,
            {
                dst.push(src[i]);
                assert(src@.take(i + 1) =~= src@.take(i as int).push(src@[i as int]));
                i = i + 1;
            }
            assert(src@.take(src@.len() as int) =~= src@);
            dst
        }
    } => Ok(())
}
