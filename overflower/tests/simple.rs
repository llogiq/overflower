use overflower::*;
use std::borrow::Cow;

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

#[overflow(panic)]
#[test]
#[should_panic]
fn test_simple_panic_sub() {
    1u8 - 2;
}

#[overflow(panic)]
#[test]
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

#[test]
#[overflow(wrap)]
fn test_refs() {
    let x = &255u8;
    let _ = x + x;
}

#[test]
#[overflow(wrap)]
fn test_strings() {
    let s = String::from("Hello, ");
    let _ = s + "World!";

    let mut x = String::from("What's ");
    x += "up";

    let cow = Cow::Borrowed("Hi, ");
    cow + "there!";

    let mut cow = Cow::Borrowed("Hi, ");
    cow += "you!";
    cow += Cow::Borrowed(" Rust is great!");
}

#[test]
fn test_add_panic_normal() {
    assert_eq!(1 + 2, 1.add_panic(2));
}

#[test]
#[should_panic]
fn test_add_panic_panics() {
    ::std::panic::set_hook(Box::new(|_| ()));
    255u8.add_panic(2u8);
}

#[test]
fn test_sub_wrap() {
    assert_eq!(255, 1u8.sub_wrap(2));
}

#[test]
fn test_saturating_mul() {
    assert_eq!(255, 16u8.mul_saturate(16u8));
}
