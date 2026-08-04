#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] eq_cmp1 verus_code! {
        use vstd::laws_eq::*;
        use vstd::laws_cmp::*;
        use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};
        use core::cmp::Ordering;

        fn test_eq<T: Ord>(x: &T, y: &T) -> (r: bool)
            requires
                obeys_cmp::<T>(),
            ensures
                r <==> x.eq_spec(y),
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);

            if x.lt(y) {
                return false;
            }
            if x.gt(y) {
                return false;
            }
            true
        }

        fn test_eq_wrong<T: Ord>(x: &T, y: &T) -> (r: bool)
            requires
                obeys_cmp::<T>(),
            ensures
                r <==> x.eq_spec(y),
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);

            if x.lt(y) {
                return false;
            }
            if x.gt(y) {
                return true; // FAILS
            }
            true
        }

        fn test() {
            let b = test_eq(&Some(5u8), &Some(4u8 + 1));
            assert(b);

            let b = test_eq(&Some(5u8), &Some(4u8 - 1));
            assert(!b);
        }

        struct P(u8, bool);

        impl PartialEq for P {
            fn eq(&self, other: &P) -> (b: bool)
                ensures
                    b <==> self == other
            {
                self.0 == other.0 && self.1 == other.1
            }
        }
        impl vstd::std_specs::cmp::PartialEqSpecImpl for P {
            closed spec fn obeys_eq_spec() -> bool {
                true
            }

            closed spec fn eq_spec(&self, other: &P) -> bool {
                self == other
            }
        }
        impl Eq for P {
        }

        broadcast proof fn lemma_s_obeys_eq_spec()
            ensures
                #[trigger] obeys_eq::<P>(),
        {
            reveal(obeys_eq_spec_properties);
        }

        broadcast proof fn lemma_s_obeys_concrete_eq()
            ensures
                #[trigger] obeys_concrete_eq::<P>(),
        {
            reveal(obeys_concrete_eq);
        }

        fn test_p_eq() {
            let b = P(3, true).eq(&P(3, false));
            assert(!b);
        }

        fn test_p_ee() {
            let b = P(3, true) == P(3, false);
            assert(!b);
        }

        #[derive(PartialEq, Eq, StructuralEq)]
        struct S(u8, bool);

        fn check_eq<T: Eq>(x: &T, y: &T) -> (b: bool)
            requires
                obeys_concrete_eq::<T>(),
            ensures
                b <==> x == y,
        {
            reveal(obeys_concrete_eq);
            x.eq(y)
        }

        fn test_s() {
            let b = check_eq(&S(3, true), &S(3, false));
            assert(!b);
            let b = S(3, true) == S(3, false);
            assert(!b);
        }
    } => Err(err) => assert_one_fails(err)
}

const ORD_DISAGREES_WITH_PARTIAL_ORD: &str = verus_code_str! {
    use vstd::std_specs::cmp::{OrdSpecImpl, PartialEqSpecImpl, PartialOrdSpecImpl};
    use core::cmp::Ordering;

    pub struct P(pub u8);

    impl PartialEq for P {
        fn eq(&self, other: &P) -> (b: bool) {
            self.0 == other.0
        }
    }

    impl PartialEqSpecImpl for P {
        open spec fn obeys_eq_spec() -> bool {
            true
        }

        open spec fn eq_spec(&self, other: &P) -> bool {
            self.0 == other.0
        }
    }

    impl Eq for P {
    }

    impl PartialOrd for P {
        fn partial_cmp(&self, other: &P) -> (r: Option<Ordering>) {
            if self.0 < other.0 {
                Some(Ordering::Greater)
            } else if self.0 == other.0 {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Less)
            }
        }
    }

    impl PartialOrdSpecImpl for P {
        open spec fn obeys_partial_cmp_spec() -> bool {
            true
        }

        open spec fn partial_cmp_spec(&self, other: &P) -> Option<Ordering> {
            if self.0 < other.0 {
                Some(Ordering::Greater)
            } else if self.0 == other.0 {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Less)
            }
        }
    }

    impl Ord for P {
        fn cmp(&self, other: &P) -> (r: Ordering) {
            if self.0 < other.0 {
                Ordering::Less
            } else if self.0 == other.0 {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        }
    }

    impl OrdSpecImpl for P {
        open spec fn obeys_cmp_spec() -> bool {
            true
        }

        open spec fn cmp_spec(&self, other: &P) -> Ordering {
            if self.0 < other.0 {
                Ordering::Less
            } else if self.0 == other.0 {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        }
    }
};

test_verify_one_file! {
    #[test] ord_max_disagreeing_partial_ord ORD_DISAGREES_WITH_PARTIAL_ORD.to_string() + verus_code_str! {
        fn test() {
            let m = P(1).max(P(2));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ord_min_disagreeing_partial_ord ORD_DISAGREES_WITH_PARTIAL_ORD.to_string() + verus_code_str! {
        fn test() {
            let m = P(1).min(P(2));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ord_clamp_disagreeing_partial_ord ORD_DISAGREES_WITH_PARTIAL_ORD.to_string() + verus_code_str! {
        fn test() {
            let c = P(5).clamp(P(9), P(1));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ord_ref_max_disagreeing_partial_ord ORD_DISAGREES_WITH_PARTIAL_ORD.to_string() + verus_code_str! {
        fn test() {
            let a = P(1);
            let b = P(2);
            let m = (&a).max(&b);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ord_max_derived_partial_ord_reversed_cmp verus_code! {
        use vstd::std_specs::cmp::OrdSpecImpl;
        use core::cmp::Ordering;

        #[derive(PartialEq, Eq, PartialOrd)]
        pub struct D(pub u8);

        impl Ord for D {
            fn cmp(&self, other: &D) -> (r: Ordering) {
                if self.0 < other.0 {
                    Ordering::Greater
                } else if self.0 == other.0 {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            }
        }

        impl OrdSpecImpl for D {
            open spec fn obeys_cmp_spec() -> bool {
                true
            }

            open spec fn cmp_spec(&self, other: &D) -> Ordering {
                if self.0 < other.0 {
                    Ordering::Greater
                } else if self.0 == other.0 {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            }
        }

        fn test() {
            let m = D(1).max(D(2));
            assert(m.0 == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

const ORD_AGREES_WITH_PARTIAL_ORD: &str = verus_code_str! {
    use vstd::std_specs::cmp::{OrdSpecImpl, PartialEqSpecImpl, PartialOrdSpecImpl};
    use core::cmp::Ordering;

    pub struct Q(pub u8);

    impl PartialEq for Q {
        fn eq(&self, other: &Q) -> (b: bool) {
            self.0 == other.0
        }
    }

    impl PartialEqSpecImpl for Q {
        open spec fn obeys_eq_spec() -> bool {
            true
        }

        open spec fn eq_spec(&self, other: &Q) -> bool {
            self.0 == other.0
        }
    }

    impl Eq for Q {
    }

    impl PartialOrd for Q {
        fn partial_cmp(&self, other: &Q) -> (r: Option<Ordering>) {
            if self.0 < other.0 {
                Some(Ordering::Less)
            } else if self.0 == other.0 {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Greater)
            }
        }
    }

    impl PartialOrdSpecImpl for Q {
        open spec fn obeys_partial_cmp_spec() -> bool {
            true
        }

        open spec fn partial_cmp_spec(&self, other: &Q) -> Option<Ordering> {
            if self.0 < other.0 {
                Some(Ordering::Less)
            } else if self.0 == other.0 {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Greater)
            }
        }
    }

    impl Ord for Q {
        fn cmp(&self, other: &Q) -> (r: Ordering) {
            if self.0 < other.0 {
                Ordering::Less
            } else if self.0 == other.0 {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        }
    }

    impl OrdSpecImpl for Q {
        open spec fn obeys_cmp_spec() -> bool {
            true
        }

        open spec fn cmp_spec(&self, other: &Q) -> Ordering {
            if self.0 < other.0 {
                Ordering::Less
            } else if self.0 == other.0 {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        }
    }
};

test_verify_one_file! {
    #[test] ord_max_min_clamp_agreeing_partial_ord ORD_AGREES_WITH_PARTIAL_ORD.to_string() + verus_code_str! {
        fn test() {
            let m = Q(1).max(Q(2));
            assert(m.0 == 2);
            let n = Q(1).min(Q(2));
            assert(n.0 == 1);
            let c = Q(5).clamp(Q(1), Q(3));
            assert(c.0 == 3);
            let d = Q(0).clamp(Q(1), Q(3));
            assert(d.0 == 1);
            let e = Q(2).clamp(Q(1), Q(3));
            assert(e.0 == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ord_max_min_clamp_ties_agreeing_partial_ord ORD_AGREES_WITH_PARTIAL_ORD.to_string() + verus_code_str! {
        fn test(x: Q, y: Q)
            requires
                x.0 == y.0,
        {
            let m = Q(x.0).max(Q(y.0));
            assert(m == Q(y.0));
            let n = Q(x.0).min(Q(y.0));
            assert(n == Q(x.0));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ord_max_min_clamp_primitives verus_code! {
        use vstd::prelude::*;

        fn test() {
            let m = 3u8.max(5u8);
            assert(m == 5);
            let n = 3u8.min(5u8);
            assert(n == 3);
            let c = 7i32.clamp(1i32, 5i32);
            assert(c == 5);
            let d = (-7i32).clamp(1i32, 5i32);
            assert(d == 1);
            let e = 3i32.clamp(1i32, 5i32);
            assert(e == 3);
        }

        fn test_symbolic(x: u64, y: u64) {
            let m = x.max(y);
            assert(m == if x >= y { x } else { y });
            let n = x.min(y);
            assert(n == if x <= y { x } else { y });
        }

        fn test_refs() {
            let a = 3u8;
            let b = 5u8;
            let m = (&a).max(&b);
            assert(*m == 5);
            let n = (&a).min(&b);
            assert(*n == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ord_max_min_clamp_obeys_cmp verus_code! {
        use vstd::laws_cmp::*;
        use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
        use core::cmp::Ordering;

        fn test_max<T: Ord>(x: T, y: T) -> (r: T)
            requires
                obeys_cmp::<T>(),
            ensures
                y.cmp_spec(&x) is Less ==> r == x,
                !(y.cmp_spec(&x) is Less) ==> r == y,
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);
            x.max(y)
        }

        fn test_min<T: Ord>(x: T, y: T) -> (r: T)
            requires
                obeys_cmp::<T>(),
            ensures
                y.cmp_spec(&x) is Less ==> r == y,
                !(y.cmp_spec(&x) is Less) ==> r == x,
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);
            x.min(y)
        }

        fn test_clamp<T: Ord>(x: T, lo: T, hi: T) -> (r: T)
            requires
                obeys_cmp::<T>(),
                lo.cmp_spec(&hi) is Less || lo.cmp_spec(&hi) is Equal,
            ensures
                x.cmp_spec(&lo) is Less ==> r == lo,
                !(x.cmp_spec(&lo) is Less) && x.cmp_spec(&hi) is Greater ==> r == hi,
                !(x.cmp_spec(&lo) is Less) && !(x.cmp_spec(&hi) is Greater) ==> r == x,
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);
            x.clamp(lo, hi)
        }

        fn test() {
            broadcast use group_laws_cmp;

            let m = test_max(3u8, 5u8);
            assert(m == 5);
            let n = test_min(3u8, 5u8);
            assert(n == 3);
            let c = test_clamp(7u8, 1u8, 5u8);
            assert(c == 5);
            let r = test_max(&3u8, &5u8);
            assert(*r == 5);
        }
    } => Ok(())
}
