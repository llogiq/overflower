#![allow(const_err, unused)]

#[macro_use] extern crate overflower;
extern crate overflower_support;

macro_rules! id {
    ($x:expr) => { $x };
}

#[test]
#[overflow(wrap)]
fn test_macro_wrap() {
    id!(255u8 + 1);
}

#[test]
#[should_panic]
#[overflow(panic)]
fn test_macro_panic() {
    id!(127i8 + 1);
}
