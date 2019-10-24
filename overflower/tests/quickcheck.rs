use std::cmp::Ordering;
use std::panic::{self, catch_unwind};
use std::sync::Once;
use quickcheck::quickcheck;
use overflower::*;

static HANDLER : Once = Once::new();

fn install_handler() {
    HANDLER.call_once(|| {
        let p = panic::take_hook();
        panic::set_hook(Box::new(move|info| {
            if info.location().map_or(false, |l| l.file() != "src/lib.rs" &&
                    !l.file().ends_with("/num/mod.rs")) {
                p(info);
            }
        }));
    })
}

macro_rules! test_add_panic {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_add(args.1);
                let actual = catch_unwind(
                    || AddPanic::add_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_add_panic!(usize, test_add_panic_usize);
test_add_panic!(u64, test_add_panic_u64);
test_add_panic!(u32, test_add_panic_u32);
test_add_panic!(u16, test_add_panic_u16);
test_add_panic!(u8,  test_add_panic_u8);
test_add_panic!(isize, test_add_panic_isize);
test_add_panic!(i64, test_add_panic_i64);
test_add_panic!(i32, test_add_panic_i32);
test_add_panic!(i16, test_add_panic_i16);
test_add_panic!(i8,  test_add_panic_i8);

macro_rules! test_add_wrap {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.wrapping_add(args.1);
                let actual = AddWrap::add_wrap(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_add_wrap!(usize, test_add_wrap_usize);
test_add_wrap!(u64, test_add_wrap_u64);
test_add_wrap!(u32, test_add_wrap_u32);
test_add_wrap!(u16, test_add_wrap_u16);
test_add_wrap!(u8,  test_add_wrap_u8);
test_add_wrap!(isize, test_add_wrap_isize);
test_add_wrap!(i64, test_add_wrap_i64);
test_add_wrap!(i32, test_add_wrap_i32);
test_add_wrap!(i16, test_add_wrap_i16);
test_add_wrap!(i8,  test_add_wrap_i8);

macro_rules! test_add_saturate {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.saturating_add(args.1);
                let actual = AddSaturate::add_saturate(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_add_saturate!(usize, test_add_saturate_usize);
test_add_saturate!(u64, test_add_saturate_u64);
test_add_saturate!(u32, test_add_saturate_u32);
test_add_saturate!(u16, test_add_saturate_u16);
test_add_saturate!(u8,  test_add_saturate_u8);
test_add_saturate!(isize, test_add_saturate_isize);
test_add_saturate!(i64, test_add_saturate_i64);
test_add_saturate!(i32, test_add_saturate_i32);
test_add_saturate!(i16, test_add_saturate_i16);
test_add_saturate!(i8,  test_add_saturate_i8);

macro_rules! test_sub_panic {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_sub(args.1);
                let actual = catch_unwind(
                             || SubPanic::sub_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_sub_panic!(usize, test_sub_panic_usize);
test_sub_panic!(u64, test_sub_panic_u64);
test_sub_panic!(u32, test_sub_panic_u32);
test_sub_panic!(u16, test_sub_panic_u16);
test_sub_panic!(u8,  test_sub_panic_u8);
test_sub_panic!(isize, test_sub_panic_isize);
test_sub_panic!(i64, test_sub_panic_i64);
test_sub_panic!(i32, test_sub_panic_i32);
test_sub_panic!(i16, test_sub_panic_i16);
test_sub_panic!(i8,  test_sub_panic_i8);

macro_rules! test_sub_wrap {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.wrapping_sub(args.1);
                let actual = SubWrap::sub_wrap(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_sub_wrap!(usize, test_sub_wrap_usize);
test_sub_wrap!(u64, test_sub_wrap_u64);
test_sub_wrap!(u32, test_sub_wrap_u32);
test_sub_wrap!(u16, test_sub_wrap_u16);
test_sub_wrap!(u8,  test_sub_wrap_u8);
test_sub_wrap!(isize, test_sub_wrap_isize);
test_sub_wrap!(i64, test_sub_wrap_i64);
test_sub_wrap!(i32, test_sub_wrap_i32);
test_sub_wrap!(i16, test_sub_wrap_i16);
test_sub_wrap!(i8,  test_sub_wrap_i8);

macro_rules! test_sub_saturate {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.saturating_sub(args.1);
                let actual = SubSaturate::sub_saturate(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_sub_saturate!(usize, test_sub_saturate_usize);
test_sub_saturate!(u64, test_sub_saturate_u64);
test_sub_saturate!(u32, test_sub_saturate_u32);
test_sub_saturate!(u16, test_sub_saturate_u16);
test_sub_saturate!(u8,  test_sub_saturate_u8);
test_sub_saturate!(isize, test_sub_saturate_isize);
test_sub_saturate!(i64, test_sub_saturate_i64);
test_sub_saturate!(i32, test_sub_saturate_i32);
test_sub_saturate!(i16, test_sub_saturate_i16);
test_sub_saturate!(i8,  test_sub_saturate_i8);

macro_rules! test_mul_panic {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_mul(args.1);
                let actual = catch_unwind(
                             || MulPanic::mul_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_mul_panic!(usize, test_mul_panic_usize);
test_mul_panic!(u64, test_mul_panic_u64);
test_mul_panic!(u32, test_mul_panic_u32);
test_mul_panic!(u16, test_mul_panic_u16);
test_mul_panic!(u8,  test_mul_panic_u8);
test_mul_panic!(isize, test_mul_panic_isize);
test_mul_panic!(i64, test_mul_panic_i64);
test_mul_panic!(i32, test_mul_panic_i32);
test_mul_panic!(i16, test_mul_panic_i16);
test_mul_panic!(i8,  test_mul_panic_i8);

macro_rules! test_mul_wrap {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.wrapping_mul(args.1);
                let actual = MulWrap::mul_wrap(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_mul_wrap!(usize, test_mul_wrap_usize);
test_mul_wrap!(u64, test_mul_wrap_u64);
test_mul_wrap!(u32, test_mul_wrap_u32);
test_mul_wrap!(u16, test_mul_wrap_u16);
test_mul_wrap!(u8,  test_mul_wrap_u8);
test_mul_wrap!(isize, test_mul_wrap_isize);
test_mul_wrap!(i64, test_mul_wrap_i64);
test_mul_wrap!(i32, test_mul_wrap_i32);
test_mul_wrap!(i16, test_mul_wrap_i16);
test_mul_wrap!(i8,  test_mul_wrap_i8);

macro_rules! test_mul_saturate {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.saturating_mul(args.1);
                let actual = MulSaturate::mul_saturate(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_mul_saturate!(usize, test_mul_saturate_usize);
test_mul_saturate!(u64, test_mul_saturate_u64);
test_mul_saturate!(u32, test_mul_saturate_u32);
test_mul_saturate!(u16, test_mul_saturate_u16);
test_mul_saturate!(u8,  test_mul_saturate_u8);
test_mul_saturate!(isize, test_mul_saturate_isize);
test_mul_saturate!(i64, test_mul_saturate_i64);
test_mul_saturate!(i32, test_mul_saturate_i32);
test_mul_saturate!(i16, test_mul_saturate_i16);
test_mul_saturate!(i8,  test_mul_saturate_i8);

macro_rules! test_div_panic {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_div(args.1);
                let actual = catch_unwind(
                             || DivPanic::div_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_div_panic!(usize, test_div_panic_usize);
test_div_panic!(u64, test_div_panic_u64);
test_div_panic!(u32, test_div_panic_u32);
test_div_panic!(u16, test_div_panic_u16);
test_div_panic!(u8,  test_div_panic_u8);
test_div_panic!(isize, test_div_panic_isize);
test_div_panic!(i64, test_div_panic_i64);
test_div_panic!(i32, test_div_panic_i32);
test_div_panic!(i16, test_div_panic_i16);
test_div_panic!(i8,  test_div_panic_i8);

macro_rules! test_div_wrap {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_div(args.1);
                let actual = catch_unwind(
                             || DivWrap::div_wrap(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_div_wrap!(usize, test_div_wrap_usize);
test_div_wrap!(u64, test_div_wrap_u64);
test_div_wrap!(u32, test_div_wrap_u32);
test_div_wrap!(u16, test_div_wrap_u16);
test_div_wrap!(u8,  test_div_wrap_u8);
test_div_wrap!(isize, test_div_wrap_isize);
test_div_wrap!(i64, test_div_wrap_i64);
test_div_wrap!(i32, test_div_wrap_i32);
test_div_wrap!(i16, test_div_wrap_i16);
test_div_wrap!(i8,  test_div_wrap_i8);

macro_rules! test_div_saturate {
    ($ty:ty, $name:ident, $max:expr) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = if args.1 == 0 {
                    if args.0 == 0 { 0 } else { $max } 
                } else { args.0 / args.1 };
                let actual = DivSaturate::div_saturate(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_div_saturate!(usize, test_div_saturate_usize, std::usize::MAX);
test_div_saturate!(u64, test_div_saturate_u64, std::u64::MAX);
test_div_saturate!(u32, test_div_saturate_u32, std::u32::MAX);
test_div_saturate!(u16, test_div_saturate_u16, std::u16::MAX);
test_div_saturate!(u8,  test_div_saturate_u8, std::u8::MAX);

macro_rules! test_idiv_saturate {
    ($ty:ty, $name:ident, $max:expr, $min:expr) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = match args.1 {
                    0 => match args.0.cmp(&0) {
                        Ordering::Greater => $max,
                        Ordering::Equal => 0,
                        Ordering::Less => $min
                    },
                    -1 => if args.0 == $min { $max } else { -args.0 },
                    _ => args.0 / args.1
                };
                let actual = DivSaturate::div_saturate(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_idiv_saturate!(isize, test_div_saturate_isize, std::isize::MAX, std::isize::MIN);
test_idiv_saturate!(i64, test_div_saturate_i64, std::i64::MAX, std::i64::MIN);
test_idiv_saturate!(i32, test_div_saturate_i32, std::i32::MAX, std::i32::MIN);
test_idiv_saturate!(i16, test_div_saturate_i16, std::i16::MAX, std::i16::MIN);
test_idiv_saturate!(i8,  test_div_saturate_i8, std::i8::MAX, std::i8::MIN);

macro_rules! test_rem_panic {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_rem(args.1);
                let actual = catch_unwind(
                             || RemPanic::rem_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_rem_panic!(usize, test_rem_panic_usize);
test_rem_panic!(u64, test_rem_panic_u64);
test_rem_panic!(u32, test_rem_panic_u32);
test_rem_panic!(u16, test_rem_panic_u16);
test_rem_panic!(u8,  test_rem_panic_u8);
test_rem_panic!(isize, test_rem_panic_isize);
test_rem_panic!(i64, test_rem_panic_i64);
test_rem_panic!(i32, test_rem_panic_i32);
test_rem_panic!(i16, test_rem_panic_i16);
test_rem_panic!(i8,  test_rem_panic_i8);

macro_rules! test_rem_wrap {
    ($ty:ty, $name:ident) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = args.0.checked_rem(args.1);
                let actual = catch_unwind(
                             || RemWrap::rem_wrap(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_rem_wrap!(usize, test_rem_wrap_usize);
test_rem_wrap!(u64, test_rem_wrap_u64);
test_rem_wrap!(u32, test_rem_wrap_u32);
test_rem_wrap!(u16, test_rem_wrap_u16);
test_rem_wrap!(u8,  test_rem_wrap_u8);
test_rem_wrap!(isize, test_rem_wrap_isize);
test_rem_wrap!(i64, test_rem_wrap_i64);
test_rem_wrap!(i32, test_rem_wrap_i32);
test_rem_wrap!(i16, test_rem_wrap_i16);
test_rem_wrap!(i8,  test_rem_wrap_i8);

macro_rules! test_rem_saturate {
    ($ty:ty, $name:ident, $max:expr) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = if args.1 == 0 {
                    if args.0 == 0 { 0 } else { $max }
                } else {
                    args.0 % args.1
                };
                let actual = RemSaturate::rem_saturate(args.0, args.1);
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_rem_saturate!(usize, test_rem_saturate_usize, std::usize::MAX);
test_rem_saturate!(u64, test_rem_saturate_u64, std::u64::MAX);
test_rem_saturate!(u32, test_rem_saturate_u32, std::u32::MAX);
test_rem_saturate!(u16, test_rem_saturate_u16, std::u16::MAX);
test_rem_saturate!(u8,  test_rem_saturate_u8, std::u8::MAX);
test_rem_saturate!(isize, test_rem_saturate_isize, std::isize::MAX);
test_rem_saturate!(i64, test_rem_saturate_i64, std::i64::MAX);
test_rem_saturate!(i32, test_rem_saturate_i32, std::i32::MAX);
test_rem_saturate!(i16, test_rem_saturate_i16, std::i16::MAX);
test_rem_saturate!(i8,  test_rem_saturate_i8, std::i8::MAX);

#[cfg(target_pointer_width = "16")]
const USIZE_BITS: usize = 16;

#[cfg(target_pointer_width = "32")]
const USIZE_BITS: usize = 16;

#[cfg(target_pointer_width = "64")]
const USIZE_BITS: usize = 64;

macro_rules! test_shl_panic {
    ($ty:ty, $name:ident, $bits:expr) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = if args.0 == 0 {
                    Some(0)
                } else if args.1 < $bits as $ty && (!0) >> args.1 >= args.0 {
                    Some(args.0 << args.1)
                } else {
                    None
                };
                let actual = catch_unwind(
                             || ShlPanic::shl_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_shl_panic!(usize, test_shl_panic_usize, USIZE_BITS);
test_shl_panic!(u64, test_shl_panic_u64, 64);
test_shl_panic!(u32, test_shl_panic_u32, 32);
test_shl_panic!(u16, test_shl_panic_u16, 16);
test_shl_panic!(u8,  test_shl_panic_u8, 8);

macro_rules! test_ishl_panic {
    ($ty:ty, $name:ident, $bits:expr, $max:expr, $min:expr) => {
        #[test]
        fn $name() {
            fn check(args: ($ty, $ty)) -> bool {
                let expected = match args.0.cmp(&0) {
                    Ordering::Equal => Some(0),
                    Ordering::Greater => {
                        if args.1 as usize >= $bits || ($max >> args.1) < args.0 { None } else { Some(args.0 << args.1) }
                    }
                    Ordering::Less => {
                        if args.1 as usize >= $bits || ($min >> args.1) > args.0 { None } else { Some(args.0 << args.1) }
                    }
                };
                let actual = catch_unwind(
                             || ShlPanic::shl_panic(args.0, args.1)).ok();
                expected == actual
            }
            install_handler();
            quickcheck(check as fn(($ty, $ty)) -> bool);
        }
    };
}

test_ishl_panic!(isize, test_shl_panic_isize, (USIZE_BITS - 1), std::isize::MAX, std::isize::MIN);
test_ishl_panic!(i64, test_shl_panic_i64, 63, std::i64::MAX, std::i64::MIN);
test_ishl_panic!(i32, test_shl_panic_i32, 31, std::i32::MAX, std::i32::MIN);
test_ishl_panic!(i16, test_shl_panic_i16, 15, std::i16::MAX, std::i16::MIN);
test_ishl_panic!(i8,  test_shl_panic_i8, 7, std::i8::MAX, std::i8::MIN);

#[test]
fn check_shl_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = catch_unwind(|| args.0.wrapping_shl(args.1 as u32)).ok();
        let actual = catch_unwind(|| ShlWrap::shl_wrap(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_shl_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = if args.1 as usize >= 64 || ((!0) >> args.1) < args.0 {
            if args.0 == 0 { 0 } else { std::usize::MAX }
        } else {
            args.0 << args.1
        };
        let actual = ShlSaturate::shl_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_shr_panic_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_shr(args.1 as u32);
        let actual = catch_unwind(|| ShrPanic::shr_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_shr_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = catch_unwind(|| args.0.wrapping_shr(args.1 as u32)).ok();
        let actual = catch_unwind(|| ShrWrap::shr_wrap(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_shr_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_shr(args.1 as u32).unwrap_or(0);
        let actual = ShrSaturate::shr_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}
