#![feature(plugin)]
#![plugin(overflower)]

extern crate overflower_support;

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
#[overflow(wrap)]
fn test_simple_wrap_abs() {
    i8::abs(-128 as i8);
}

#[test]
#[overflow(wrap)]
#[allow(unused)]
fn test_simple_wrap_assign_ops() {
    let mut x = 1u8;
    x += 1;
    x -= 1;
    x *= 2;
    x /= 2;
    x <<= 1;
    x >>= 1;
    x &= 1;
    x |= 2;
}
