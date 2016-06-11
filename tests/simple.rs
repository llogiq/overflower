#![feature(plugin)]
#![plugin(overflower)]
#![allow(const_err)]

extern crate overflower_support;
use overflower_support::*;

#[test]
#[overflow(wrap)]
fn test_simple_wrap() {
    255u8 + 1;
}

#[test]
#[overflow(wrap)]
fn test_double_wrap() {
    1u8 - 2 + 2;
}

#[test]
#[overflow(panic)]
#[should_panic]
fn test_simple_panic_sub() {
    1u8 - 2;
}

#[test]
#[overflow(panic)]
#[should_panic]
fn test_simple_panic_add() {
    255u8 + 1;
}

#[test]
#[overflow(panic)]
#[should_panic]
fn test_macro_panic_add() {
    assert_eq!(0, 255u8 + 1);
}
