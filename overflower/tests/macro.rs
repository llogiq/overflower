#![feature(proc_macro_hygiene)]
#![allow(const_err, unused)]

use overflower::overflow;

macro_rules! id {
    ($x:expr) => {
        $x
    };
}

#[test]
#[ignore]
#[overflow(wrap)]
fn test_macro_wrap() {
    id!(255u8 + 1);
}

#[test]
#[ignore]
#[should_panic]
#[overflow(panic)]
fn test_macro_panic() {
    id!(127i8 + 1);
}
