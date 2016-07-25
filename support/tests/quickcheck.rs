extern crate quickcheck;
extern crate overflower_support;

use std::panic::{self, catch_unwind};
use quickcheck::quickcheck;
use overflower_support::*;

fn install_handler() {
    let p = panic::take_hook();
    panic::set_hook(Box::new(move|info| {
        if info.location().map_or(false, |l| l.file() != "src/lib.rs" &&
                !l.file().ends_with("/num/mod.rs")) {
            p(info);
        }
    }));
}

#[test]
fn check_add_panic_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_add(args.1);
        let actual = catch_unwind(|| AddPanic::add_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_add_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.wrapping_add(args.1);
        let actual = AddWrap::add_wrap(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_add_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.saturating_add(args.1);
        let actual = AddSaturate::add_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}


#[test]
fn check_sub_panic_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_sub(args.1);
        let actual = catch_unwind(|| SubPanic::sub_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_sub_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.wrapping_sub(args.1);
        let actual = SubWrap::sub_wrap(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_sub_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.saturating_sub(args.1);
        let actual = SubSaturate::sub_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}


#[test]
fn check_mul_panic_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_mul(args.1);
        let actual = catch_unwind(|| MulPanic::mul_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_mul_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.wrapping_mul(args.1);
        let actual = MulWrap::mul_wrap(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_mul_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.saturating_mul(args.1);
        let actual = MulSaturate::mul_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}


#[test]
fn check_div_panic_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_div(args.1);
        let actual = catch_unwind(|| DivPanic::div_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_div_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_div(args.1);
        let actual = catch_unwind(|| DivWrap::div_wrap(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_div_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = if args.1 == 0 {
            if args.0 == 0 { 0 } else { std::usize::MAX } 
        } else { args.0 / args.1 };
        let actual = DivSaturate::div_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}


#[test]
fn check_rem_panic_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_rem(args.1);
        let actual = catch_unwind(|| RemPanic::rem_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_rem_wrap_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = args.0.checked_rem(args.1);
        let actual = catch_unwind(|| RemWrap::rem_wrap(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_rem_saturate_usize() {
    fn check(args: (usize, usize)) -> bool {
        let expected = if args.1 == 0 {
            if args.0 == 0 { 0 } else { std::usize::MAX }
        } else {
            args.0 % args.1
        };
        let actual = RemSaturate::rem_saturate(args.0, args.1);
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

#[test]
fn check_shl_panic_usize() {
    fn check(args: (usize, usize)) -> bool {        
        let expected = if args.0 == 0 { 
            Some(0)
        } else if args.1 < 64 && (!0) >> args.1 >= args.0 {
            Some(args.0 << args.1)
        } else {
            None
        };
        let actual = catch_unwind(|| ShlPanic::shl_panic(args.0, args.1)).ok();
        expected == actual
    }
    install_handler();
    quickcheck(check as fn((usize, usize)) -> bool);
}

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
