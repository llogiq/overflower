extern crate quickcheck;
extern crate overflower_support;

use quickcheck::{TestResult, quickcheck};
use std::panic;
use overflower_support::{AddPanic, AddWrap, AddSaturate};

#[test]
fn check_add_panic() {
    fn check(args: (usize, usize)) -> TestResult {
        if let Some(expected) = args.0.checked_add(args.1) {
            let actual = AddPanic::add_panic(args.0, args.1);
            if expected != actual {
                return TestResult::error(format!(
                        "{} + {}: expected {}, got {}", args.0, args.1,
                        expected, actual));
            }
        } else {
            if let Ok(actual) = panic::catch_unwind(
                    || AddPanic::add_panic(args.0, args.1)) {
                return TestResult::error(format!(
                        "{} + {}: expected panic, got {}",
                        args.0, args.1, actual));
            }
        }
        TestResult::passed()
    }
    quickcheck(check as fn((usize, usize)) -> TestResult);
}

#[test]
fn check_add_wrap() {
    fn check(args: (usize, usize)) -> TestResult {
        let expected = args.0.wrapping_add(args.1);
        let actual = AddWrap::add_wrap(args.0, args.1);
        if expected != actual {
             TestResult::error(format!(
                 "{} + {}: expected {} got {}", args.0, args.1, expected, actual))
        } else { TestResult::passed() }
    }
    quickcheck(check as fn((usize, usize)) -> TestResult);
}

#[test]
fn check_add_saturate() {
    fn check(args: (usize, usize)) -> TestResult {
        let expected = args.0.saturating_add(args.1);
        let actual = AddSaturate::add_saturate(args.0, args.1);
        if expected != actual {
             TestResult::error(format!(
                 "{} + {}: expected {} got {}", args.0, args.1, expected, actual))
        } else { TestResult::passed() }
    }
    quickcheck(check as fn((usize, usize)) -> TestResult);
}

// same for sub, mul, div, rem – for i8..i64, isize, u8..u64, usize
