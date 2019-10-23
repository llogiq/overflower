//! This defines some traits so we can replace ops with method calls of the respective traits
//! (provided they're in scope) without worrying about argument types (hopefully)
//!
//! The traits are:
//! * AddPanic, SubPanic, MulPanic, DivPanic, RemPanic, ShlPanic, ShrPanic, NegPanic
//! * AddWrap, SubWrap, Mulwrap, DivWrap, RemWrap, ShlWrap, ShrWrap, NegWrap
//! * AddSaturate, SubSaturate, MulSaturate, DivSaturate, RemSaturate, ShlSaturate,
//!   ShrSaturate, NegSaturate
//!
//! The `*Panic` traits all panic on overflow, the `*Wrap` traits wrap around and the
//! `*Saturate` traits saturate.
//!
//! Note: You can use this with a stable Rust version, but if you have any annotated code
//! containing an arithmetic operation over any custom type, you'll have to use the `impls!`
//! macro to get the traits implemented for the type or use a nightly Rust and add the
//! `specialization` feature.

#![cfg_attr(feature = "specialization", feature(specialization))]
#![cfg_attr(feature = "specialization", feature(specialization))]
#![cfg_attr(feature = "wrapping_int_impl", feature(wrapping_int_impl))]
#![deny(missing_docs, unsafe_code)]

use std::ops::*;
use std::cmp::*;

#[cfg(feature = "proc_macro")]
pub use overflower_plugin::overflow;

/// Add two values, panicking on overflow
///
/// This does the same as the `std::ops::Add` trait for all non-integer types.
/// It is specialized for integer types to panic on over- or underflow.
pub trait AddPanic<RHS = Self> {
    /// The output type of the addition
    type Output;
    /// add two values, panicking on overflow
    fn add_panic(self, rhs: RHS) -> Self::Output;
}

/// Subtract two values, panicking on overflow
///
/// This does the same as the `std::ops::Sub` trait for all non-integer types.
/// It is specialized for integer types to panic on over- or underflow.
pub trait SubPanic<RHS = Self> {
    /// The output type of the subtraction
    type Output;
    /// subtract two values, panicking on overflow
    fn sub_panic(self, rhs: RHS) -> Self::Output;
}

/// Multiply two values, panicking on overflow
///
/// This does the same as the `std::ops::Mul` trait for all non-integer types.
/// It is specialized for integer types to panic on over- or underflow.
pub trait MulPanic<RHS = Self> {
    /// The output type of the multiplication
    type Output;
    /// multiply two values, panicking on overflow
    fn mul_panic(self, rhs: RHS) -> Self::Output;
}

/// Divide two values, panicking on overflow
///
/// This does the same as the `std::ops::Div` trait for all non-integer types.
/// It is specialized for integer types to panic on over- or underflow.
pub trait DivPanic<RHS = Self> {
    /// The output type of the multiplication
    type Output;
    /// divide two values, panicking on overflow
    fn div_panic(self, rhs: RHS) -> Self::Output;
}

/// Get the remainder of dividing one value by another, panicking on overflow
///
/// This does the same as the `std::ops::Rem` trait for all non-integer types.
/// It is specialized for integer types to panic on over- or underflow.
pub trait RemPanic<RHS = Self> {
    /// The output type of the remainder operation
    type Output;
    /// divide two values and get the remainder, panicking on overflow
    fn rem_panic(self, rhs: RHS) -> Self::Output;
}

macro_rules! panic_biself {
    ($trait_name:ident, $trait_panic:ident, $fn_name:ident, $fn_panic:ident, $checked_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_panic<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_panic(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        panic_biself!($trait_panic, $fn_panic, $checked_fn, u8);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, u16);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, u32);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, u64);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, usize);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, i8);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, i16);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, i32);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, i64);
        panic_biself!($trait_panic, $fn_panic, $checked_fn, isize);
    };
    ($trait_panic:ident, $fn_panic:ident, $checked_fn:ident, $ty:ty) => {
        impl $trait_panic<$ty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_panic(self, rhs: $ty) -> $ty {
                if let Some(x) = self.$checked_fn(rhs) { x }
                else { panic!("arithmetic overflow") }
            }
        }

        impl $trait_panic<$ty> for &$ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_panic(self, rhs: $ty) -> $ty {
                if let Some(x) = self.$checked_fn(rhs) { x }
                else { panic!("arithmetic overflow") }
            }
        }

        impl $trait_panic<&$ty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_panic(self, rhs: &$ty) -> $ty {
                if let Some(x) = self.$checked_fn(*rhs) { x }
                else { panic!("arithmetic overflow") }
            }
        }

        impl $trait_panic<&$ty> for &$ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_panic(self, rhs: &$ty) -> $ty {
                if let Some(x) = self.$checked_fn(*rhs) { x }
                else { panic!("arithmetic overflow") }
            }
        }
    }
}

panic_biself!(Add, AddPanic, add, add_panic, checked_add);
panic_biself!(Sub, SubPanic, sub, sub_panic, checked_sub);
panic_biself!(Mul, MulPanic, mul, mul_panic, checked_mul);
panic_biself!(Div, DivPanic, div, div_panic, checked_div);
panic_biself!(Rem, RemPanic, rem, rem_panic, checked_rem);

/// Add a value to a given value in-place, panicking on overflow
///
/// This trait does the same as the `std::ops::AddAssign` trait for most values.
/// it is specialized for integer types to panic on over- or underflow.
pub trait AddAssignPanic<RHS = Self> {
    /// add the right-hand side value to this value, panicking on overflow
    fn add_assign_panic(&mut self, rhs: RHS);
}

/// SUbtract a value from a given value in-place, panicking on overflow
///
/// This trait does the same as the `std::ops::SubAssign` trait for most values.
/// it is specialized for integer types to panic on over- or underflow.
pub trait SubAssignPanic<RHS = Self> {
    /// subtract the right-hand side value from this value, panicking on overflow
    fn sub_assign_panic(&mut self, rhs: RHS);
}

/// Multiply a value with a given value in-place, panicking on overflow
///
/// This trait does the same as the `std::ops::MulAssign` trait for most values.
/// it is specialized for integer types to panic on over- or underflow.
pub trait MulAssignPanic<RHS = Self> {
    /// multiply the right-hand side value with this value, panicking on overflow
    fn mul_assign_panic(&mut self, rhs: RHS);
}

/// Divide this value by a given value in-place, panicking on overflow
///
/// This trait does the same as the `std::ops::DivAssign` trait for most values.
/// it is specialized for integer types to panic on over- or underflow.
pub trait DivAssignPanic<RHS = Self> {
    /// divide this value by the right-hand side value, panicking on overflow
    fn div_assign_panic(&mut self, rhs: RHS);
}

/// Get the remainder of dividing this value by a given value in-place, panicking on overflow
///
/// This trait does the same as the `std::ops::RemAssign` trait for most values.
/// it is specialized for integer types to panic on over- or underflow.
pub trait RemAssignPanic<RHS = Self> {
    /// divide this value by the right-hand side value and get the remainder, panicking on overflow
    fn rem_assign_panic(&mut self, rhs: RHS);
}

macro_rules! panic_assign_biself {
    ($trait_name:ident, $trait_panic:ident, $fn_name:ident, $fn_panic:ident, $checked_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_panic<R> for T where T: $trait_name<R> {
            default fn $fn_panic(&mut self, rhs: R) {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, u8);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, u16);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, u32);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, u64);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, usize);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, i8);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, i16);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, i32);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, i64);
        panic_assign_biself!($trait_panic, $fn_panic, $checked_fn, isize);
    };
    ($trait_panic:ident, $fn_panic:ident, $checked_fn:ident, $ty:ty) => {
        impl $trait_panic<$ty> for $ty {
            fn $fn_panic(&mut self, rhs: $ty) {
                *self = if let Some(x) = self.$checked_fn(rhs) { x } else { panic!("arithmetic overflow"); }
            }
        }
    };
}

panic_assign_biself!(AddAssign, AddAssignPanic, add_assign, add_assign_panic, checked_add);
panic_assign_biself!(SubAssign, SubAssignPanic, sub_assign, sub_assign_panic, checked_sub);
panic_assign_biself!(MulAssign, MulAssignPanic, mul_assign, mul_assign_panic, checked_mul);
panic_assign_biself!(DivAssign, DivAssignPanic, div_assign, div_assign_panic, checked_div);
panic_assign_biself!(RemAssign, RemAssignPanic, rem_assign, rem_assign_panic, checked_rem);

/// Add two values, wrapping on overflow
///
/// This trait does the same as `std::ops::Add` for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait AddWrap<RHS = Self> {
    /// The result type of the addition
    type Output;

    /// add two values, wrap on overflow
    fn add_wrap(self, rhs: RHS) -> Self::Output;
}

/// Subtract two values, wrapping on overflow
///
/// This trait does the same as `std::ops::Sub` for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait SubWrap<RHS = Self> {
    /// The result type of the subtraction
    type Output;

    /// subtract two values, wrap on overflow
    fn sub_wrap(self, rhs: RHS) -> Self::Output;
}

/// Multiply two values, wrapping on overflow
///
/// This trait does the same as `std::ops::Mul` for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait MulWrap<RHS = Self> {
    /// The result type of the multiplication
    type Output;

    /// multiply two values, wrap on overflow
    fn mul_wrap(self, rhs: RHS) -> Self::Output;
}

/// Divide two values, wrapping on overflow
///
/// This trait does the same as `std::ops::Div` for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait DivWrap<RHS = Self> {
    /// The result type of the division
    type Output;

    /// divide two values, wrap on overflow
    fn div_wrap(self, rhs: RHS) -> Self::Output;
}

/// Divide two values and get the remainder, wrapping on overflow
///
/// This trait does the same as `std::ops::Rem` for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait RemWrap<RHS = Self> {
    /// The result type of the division remainder
    type Output;

    /// divide two values and get the remainder, wrap on overflow
    fn rem_wrap(self, rhs: RHS) -> Self::Output;
}

macro_rules! wrap_biself {
    ($trait_name:ident, $trait_wrap:ident, $fn_name:ident, $fn_wrap:ident, $wrapped_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_wrap<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_wrap(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u8);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u16);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u32);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u64);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, usize);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i8);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i16);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i32);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i64);
        wrap_biself!($trait_wrap, $fn_wrap, $wrapped_fn, isize);
    };
    ($trait_wrap:ident, $fn_wrap:ident, $wrapped_fn:ident, $ty:ty) => {
        impl $trait_wrap<$ty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_wrap(self, rhs: $ty) -> $ty {
                self.$wrapped_fn(rhs)
            }
        }

        impl $trait_wrap<&$ty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_wrap(self, rhs: &$ty) -> $ty {
                self.$wrapped_fn(*rhs)
            }
        }

        impl $trait_wrap<$ty> for &$ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_wrap(self, rhs: $ty) -> $ty {
                self.$wrapped_fn(rhs)
            }
        }
        impl $trait_wrap<&$ty> for &$ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_wrap(self, rhs: &$ty) -> $ty {
                self.$wrapped_fn(*rhs)
            }
        }
    }
}

wrap_biself!(Add, AddWrap, add, add_wrap, wrapping_add);
wrap_biself!(Sub, SubWrap, sub, sub_wrap, wrapping_sub);
wrap_biself!(Mul, MulWrap, mul, mul_wrap, wrapping_mul);
wrap_biself!(Div, DivWrap, div, div_wrap, wrapping_div);
wrap_biself!(Rem, RemWrap, rem, rem_wrap, wrapping_rem);

/// Add a value to a given value in-place, wrapping on overflow
///
/// This trait does the same as the `std::ops::AddAssign` trait for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait AddAssignWrap<RHS = Self> {
    /// add a value to a given value in-place, wrapping on overflow
    fn add_assign_wrap(&mut self, rhs: RHS);
}

/// Subtract a value from a given value in-place, wrapping on overflow
///
/// This trait does the same as the `std::ops::SubAssign` trait for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait SubAssignWrap<RHS = Self> {
    /// subtract a value from a given value in-place, wrapping on overflow
    fn sub_assign_wrap(&mut self, rhs: RHS);
}

/// Multiply a value with a given value in-place, wrapping on overflow
///
/// This trait does the same as the `std::ops::MulAssign` trait for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait MulAssignWrap<RHS = Self> {
    /// multiply a value with a given value in-place, wrapping on overflow
    fn mul_assign_wrap(&mut self, rhs: RHS);
}

/// Divide a value by a given value in-place, wrapping on overflow
///
/// This trait does the same as the `std::ops::DivAssign` trait for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait DivAssignWrap<RHS = Self> {
    /// divide a value by a given value in-place, wrapping on overflow
    fn div_assign_wrap(&mut self, rhs: RHS);
}

/// Divide a value to a given value, getting the remainder in-place, wrapping
/// on overflow
///
/// This trait does the same as the `std::ops::RemAssign` trait for most values.
/// it is specialized for integer types to wrap on over- or underflow.
pub trait RemAssignWrap<RHS = Self> {
    /// get the remainder of a division in place, wrapping on overflow
    fn rem_assign_wrap(&mut self, rhs: RHS);
}

macro_rules! wrap_assign_biself {
    ($trait_name:ident, $trait_wrap:ident, $fn_name:ident, $fn_wrap:ident, $wrapped_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_wrap<R> for T where T: $trait_name<R> {
            default fn $fn_wrap(&mut self, rhs: R) {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u8);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u16);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u32);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, u64);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, usize);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i8);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i16);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i32);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, i64);
        wrap_assign_biself!($trait_wrap, $fn_wrap, $wrapped_fn, isize);
    };
    ($trait_wrap:ident, $fn_wrap:ident, $wrapped_fn:ident, $ty:ty) => {
        impl $trait_wrap<$ty> for $ty {
            fn $fn_wrap(&mut self, rhs: $ty) {
                *self = self.$wrapped_fn(rhs);
            }
        }
    }
}

wrap_assign_biself!(AddAssign, AddAssignWrap, add_assign, add_assign_wrap, wrapping_add);
wrap_assign_biself!(SubAssign, SubAssignWrap, sub_assign, sub_assign_wrap, wrapping_sub);
wrap_assign_biself!(MulAssign, MulAssignWrap, mul_assign, mul_assign_wrap, wrapping_mul);
wrap_assign_biself!(DivAssign, DivAssignWrap, div_assign, div_assign_wrap, wrapping_div);
wrap_assign_biself!(RemAssign, RemAssignWrap, rem_assign, rem_assign_wrap, wrapping_rem);

//----

/// Add two values, saturating on overflow
///
/// This trait does the same as `std::ops::Add` for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait AddSaturate<RHS = Self> {
    /// The result type of the addition
    type Output;

    /// add two values, saturate on overflow
    fn add_saturate(self, rhs: RHS) -> Self::Output;
}

/// Subtract two values, saturating on overflow
///
/// This trait does the same as `std::ops::Sub` for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait SubSaturate<RHS = Self> {
    /// The result type of the subtraction
    type Output;

    /// subtract two values, saturate on overflow
    fn sub_saturate(self, rhs: RHS) -> Self::Output;
}

/// Multiply two values, saturating on overflow
///
/// This trait does the same as `std::ops::Mul` for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait MulSaturate<RHS = Self> {
    /// The result type of the multiplication
    type Output;

    /// multiply two values, saturate on overflow
    fn mul_saturate(self, rhs: RHS) -> Self::Output;
}

/// Divide two values, saturating on overflow
///
/// This trait does the same as `std::ops::Div` for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait DivSaturate<RHS = Self> {
    /// The result type of the division
    type Output;

    /// divide two values, saturate on overflow
    fn div_saturate(self, rhs: RHS) -> Self::Output;
}

/// Divide two values and get the remainder, saturating on overflow
///
/// This trait does the same as `std::ops::Rem` for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait RemSaturate<RHS = Self> {
    /// The result type of the division remainder
    type Output;

    /// divide two values and get the remainder, saturate on overflow
    fn rem_saturate(self, rhs: RHS) -> Self::Output;
}

/// Add a value to a given value in-place, saturating on overflow
///
/// This trait does the same as the `std::ops::AddAssign` trait for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait AddAssignSaturate<RHS = Self> {
    /// add a value to a given value in-place, saturating on overflow
    fn add_assign_saturate(&mut self, rhs: RHS);
}

/// Subtract a value from a given value in-place, saturating on overflow
///
/// This trait does the same as the `std::ops::SubAssign` trait for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait SubAssignSaturate<RHS = Self> {
    /// subtract a value from a given value in-place, saturating on overflow
    fn sub_assign_saturate(&mut self, rhs: RHS);
}

/// Multiply a value with a given value in-place, saturating on overflow
///
/// This trait does the same as the `std::ops::MulAssign` trait for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait MulAssignSaturate<RHS = Self> {
    /// multiply a value with a given value in-place, saturating on overflow
    fn mul_assign_saturate(&mut self, rhs: RHS);
}

/// Divide a value by a given value in-place, saturating on overflow
///
/// This trait does the same as the `std::ops::DivAssign` trait for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait DivAssignSaturate<RHS = Self> {
    /// divide a value by a given value in-place, saturating on overflow
    fn div_assign_saturate(&mut self, rhs: RHS);
}

/// Divide a value to a given value, getting the remainder in-place, saturating
/// on overflow
///
/// This trait does the same as the `std::ops::RemAssign` trait for most values.
/// it is specialized for integer types to saturate on over- or underflow.
pub trait RemAssignSaturate<RHS = Self> {
    /// get the remainder of a division in place, saturating on overflow
    fn rem_assign_saturate(&mut self, rhs: RHS);
}


macro_rules! saturate_biself {
    ($trait_name:ident, $trait_saturate:ident, $fn_name:ident, $fn_saturate:ident, $saturated_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_saturate<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_saturate(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, u8);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, u16);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, u32);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, u64);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, usize);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, i8);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, i16);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, i32);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, i64);
        saturate_biself!($trait_saturate, $fn_saturate, $saturated_fn, isize);
    };
    ($trait_saturate:ident, $fn_saturate:ident, $saturated_fn:ident, $ty:ty) => {
        impl $trait_saturate<$ty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_saturate(self, rhs: $ty) -> $ty {
                self.$saturated_fn(rhs)
            }
        }

        impl $trait_saturate<$ty> for &$ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_saturate(self, rhs: $ty) -> $ty {
                self.$saturated_fn(rhs)
            }
        }

        impl $trait_saturate<&$ty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_saturate(self, rhs: &$ty) -> $ty {
                self.$saturated_fn(*rhs)
            }
        }

        impl $trait_saturate<&$ty> for &$ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_saturate(self, rhs: &$ty) -> $ty {
                self.$saturated_fn(*rhs)
            }
        }
    }
}

saturate_biself!(Add, AddSaturate, add, add_saturate, saturating_add);
saturate_biself!(Sub, SubSaturate, sub, sub_saturate, saturating_sub);
saturate_biself!(Mul, MulSaturate, mul, mul_saturate, saturating_mul);


macro_rules! saturate_assign_biself {
    ($trait_name:ident, $trait_saturate:ident, $fn_name:ident, $fn_saturate:ident, $saturated_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_saturate<R> for T where T: $trait_name<R> {
            default fn $fn_saturate(&mut self, rhs: R) {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, u8);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, u16);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, u32);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, u64);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, usize);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, i8);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, i16);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, i32);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, i64);
        saturate_assign_biself!($trait_saturate, $fn_saturate, $saturated_fn, isize);
    };
    ($trait_saturate:ident, $fn_saturate:ident, $saturated_fn:ident, $ty:ty) => {
        impl $trait_saturate<$ty> for $ty {
            fn $fn_saturate(&mut self, rhs: $ty) {
                *self = self.$saturated_fn(rhs);
            }
        }
    }
}

saturate_assign_biself!(AddAssign, AddAssignSaturate, add_assign, add_assign_saturate, saturating_add);
saturate_assign_biself!(SubAssign, SubAssignSaturate, sub_assign, sub_assign_saturate, saturating_sub);
saturate_assign_biself!(MulAssign, MulAssignSaturate, mul_assign, mul_assign_saturate, saturating_mul);
// TODO: by zero → min/max value depending on sign
saturate_assign_biself!(DivAssign, DivAssignSaturate, div_assign, div_assign_saturate, div);
saturate_assign_biself!(RemAssign, RemAssignSaturate, rem_assign, rem_assign_saturate, rem);


#[cfg(feature = "specialization")]
impl<R, T: Div<R>> DivSaturate<R> for T {
    type Output = <T as Div<R>>::Output;
    default fn div_saturate(self, rhs: R) -> Self::Output {
        Div::div(self, rhs)
    }
}

#[cfg(feature = "specialization")]
impl<R, T: Rem<R>> RemSaturate<R> for T {
    type Output = <T as Rem<R>>::Output;
    default fn rem_saturate(self, rhs: R) -> Self::Output {
        Rem::rem(self, rhs)
    }
}

macro_rules! saturate_signed {
    ($ty:ty, $min:path, $max:path) => {
        #[allow(unused_comparisons)]
        impl DivSaturate for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn div_saturate(self, rhs: $ty) -> $ty {
                match rhs {
                    0 => match self.cmp(&0) {
                        Ordering::Greater => $max,
                        Ordering::Equal => 0,
                        Ordering::Less => $min
                    },
                    -1 => if self == $min { $max } else { -self },
                    _ => self / rhs
                }
            }
        }

        impl RemSaturate for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn rem_saturate(self, rhs: $ty) -> $ty {
                if rhs == 0 { if self == 0 { 0 } else { $max }
                } else { self % rhs }
            }
        }
    };
}

macro_rules! saturate_unsigned {
    ($ty:ty, $max:path) => {
        #[allow(unused_comparisons)]
        impl DivSaturate for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn div_saturate(self, rhs: $ty) -> $ty {
                match rhs {
                    0 => if self == 0 { 0 } else { $max },
                    _ => self / rhs
                }
            }
        }

        impl RemSaturate for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn rem_saturate(self, rhs: $ty) -> $ty {
                if rhs == 0 { if self == 0 { 0 } else { $max }
                } else { self % rhs }
            }
        }
    };
}

saturate_unsigned!(u8,    std::u8::MAX);
saturate_unsigned!(u16,   std::u16::MAX);
saturate_unsigned!(u32,   std::u32::MAX);
saturate_unsigned!(u64,   std::u64::MAX);
saturate_unsigned!(usize, std::usize::MAX);
saturate_signed!(i8,    std::i8::MIN,    std::i8::MAX);
saturate_signed!(i16,   std::i16::MIN,   std::i16::MAX);
saturate_signed!(i32,   std::i32::MIN,   std::i32::MAX);
saturate_signed!(i64,   std::i64::MIN,   std::i64::MAX);
saturate_signed!(isize, std::isize::MIN, std::isize::MAX);

/// Shift right, panic if the number of bits shifted are higher than the width
/// of the type
///
/// This does the same as the `std::ops::Shr` trait for most types.
/// it is specialized for integer types to panic on over- or underflow.
pub trait ShrPanic<RHS=usize> {
    /// THe output type of the shift operation
    type Output;

    /// shift right, panic if the number of bits shifted are higher than the
    /// width of the type
    fn shr_panic(self, rhs: RHS) -> Self::Output;
}

/// Shift right in place, panic if the number of bits shifted are higher than
/// the width of the type
///
/// This does the same as the `std::ops::ShrAssign` trait for most types.
/// it is specialized for integer types to panic on over- or underflow.
pub trait ShrAssignPanic<RHS=usize> {
    /// shift right in place, panic if the number of bits shifted are higher
    /// than the width of the type
    fn shr_assign_panic(&mut self, rhs: RHS);
}

macro_rules! panic_shifts {
    (@$trait_name:ident,
      $trait_assign_name:ident,
      $trait_panic:ident,
      $trait_assign_panic:ident,
      $fn_name:ident,
      $fn_assign_name:ident,
      $fn_panic:ident,
      $fn_assign_panic:ident,
      $checked_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_panic<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_panic(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        #[cfg(feature = "specialization")]
        impl<T, R> $trait_assign_panic<R> for T where T: $trait_assign_name<R> {
            default fn $fn_assign_panic(&mut self, rhs: R) {
                $trait_assign_name::$fn_assign_name(self, rhs)
            }
        }

        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, u8);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, u16);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, u32);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, u64);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, usize);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, i8);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, i16);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, i32);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, i64);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, isize);
    };
    ($trait_panic:ident, $trait_assign_panic:ident, $fn_panic:ident, $fn_assign_panic:ident, $checked_fn:ident, $ty:ty) => {
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, u8);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, u16);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, u32);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, u64);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, usize);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, i8);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, i16);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, i32);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, i64);
        panic_shifts!($trait_panic, $trait_assign_panic, $fn_panic, $fn_assign_panic, $checked_fn, $ty, isize);
    };
    ($trait_panic:ident, $trait_assign_panic:ident, $fn_panic:ident, $fn_assign_panic:ident, $checked_fn:ident, $ty:ty, $rty:ty) => {
        impl $trait_panic<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_panic(self, rhs: $rty) -> Self::Output {
                if let Some(x) = self.$checked_fn(rhs as u32) { x } else
                            { panic!("Arithmetic overflow") }
            }
        }

        impl $trait_assign_panic<$rty> for $ty {
            fn $fn_assign_panic(&mut self, rhs: $rty) {
                *self = if let Some(x) = self.$checked_fn(rhs as u32) { x } else
                            { panic!("Arithmetic overflow") }
            }
        }
    }
}

panic_shifts!(@Shr, ShrAssign, ShrPanic, ShrAssignPanic, shr, shr_assign, shr_panic, shr_assign_panic, checked_shr);

/// Shift left, return 0 if the number of bits shifted are higher than the
/// width of the type
///
/// This does the same as the `std::ops::Shl` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShlWrap<RHS=usize> {
    /// the return type of our shift operation
    type Output;
    /// shift left, return 0 if the number of bits shifted are higher than the
    /// width of the type
    fn shl_wrap(self, rhs: RHS) -> Self::Output;
}

/// Shift left in place, set self to 0 if the number of bits shifted are higher
/// than the width of the type
///
/// This does the same as the `std::ops::ShlAssign` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShlAssignWrap<RHS=usize> {
    /// Shift left in place, set self to 0 if the number of bits shifted are
    /// higher than the width of the type
    fn shl_assign_wrap(&mut self, rhs: RHS);
}

/// Shift right, return 0 if the number of bits shifted are higher than the
/// width of the type
///
/// This does the same as the `std::ops::Shr` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShrWrap<RHS=usize> {
    /// the return type of our shift operation
    type Output;
    /// shift right, return 0 if the number of bits shifted are higher than the
    /// width of the type
    fn shr_wrap(self, rhs: RHS) -> Self::Output;
}

/// Shift right in place, set self to 0 if the number of bits shifted are
/// higher than the width of the type
///
/// This does the same as the `std::ops::ShrAssign` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShrAssignWrap<RHS=usize> {
    /// Shift right in place, set self to 0 if the number of bits shifted are
    /// higher than the width of the type
    fn shr_assign_wrap(&mut self, rhs: RHS);
}

macro_rules! wrap_shifts {
    (@$trait_name:ident, $trait_assign_name:ident, $trait_wrap:ident, $trait_assign_wrap:ident, $fn_name:ident, $fn_assign_name:ident, $fn_wrap:ident, $fn_assign_wrap:ident, $wrapping_fn:ident) => {
        #[cfg(feature = "specialization")]
        impl<T, R> $trait_wrap<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_wrap(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        #[cfg(feature = "specialization")]
        impl<T, R> $trait_assign_wrap<R> for T where T: $trait_assign_name<R> {
            default fn $fn_assign_wrap(&mut self, rhs: R) {
                $trait_assign_name::$fn_assign_name(self, rhs)
            }
        }

        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, u8);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, u16);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, u32);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, u64);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, usize);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, i8);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, i16);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, i32);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, i64);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, isize);
    };
    ($trait_wrap:ident, $trait_assign_wrap:ident, $fn_wrap:ident, $fn_assign_wrap:ident, $wrapping_fn:ident, $ty:ty) => {
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, u8);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, u16);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, u32);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, u64);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, usize);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, i8);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, i16);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, i32);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, i64);
        wrap_shifts!($trait_wrap, $trait_assign_wrap, $fn_wrap, $fn_assign_wrap, $wrapping_fn, $ty, isize);
    };
    ($trait_wrap:ident, $trait_assign_wrap:ident, $fn_wrap:ident, $fn_assign_wrap:ident, $wrapping_fn:ident, $ty:ty, $rty:ty) => {
        impl $trait_wrap<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn $fn_wrap(self, rhs: $rty) -> Self::Output {
                self.$wrapping_fn(rhs as u32)
            }
        }

        impl $trait_assign_wrap<$rty> for $ty {
            fn $fn_assign_wrap(&mut self, rhs: $rty) {
                *self = self.$wrapping_fn(rhs as u32)
            }
        }
    }
}

wrap_shifts!(@Shl, ShlAssign, ShlWrap, ShlAssignWrap, shl, shl_assign, shl_wrap, shl_assign_wrap, wrapping_shl);
wrap_shifts!(@Shr, ShrAssign, ShrWrap, ShrAssignWrap, shr, shr_assign, shr_wrap, shr_assign_wrap, wrapping_shr);

/// Shift right, return 0 if the number of bits shifted are higher than the
/// width of the type
///
/// This does the same as the `std::ops::Shr` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShrSaturate<RHS=usize> {
    /// the return type of our shift operation
    type Output;
    /// shift right, return 0 if the number of bits shifted are higher than the
    /// width of the type
    fn shr_saturate(self, rhs: RHS) -> Self::Output;
}


/// Shift right in place, set self to 0 if the number of bits shifted are
/// higher than the width of the type
///
/// This does the same as the `std::ops::ShrAssign` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShrSaturateAssign<RHS=usize> {
    /// shift right in place, set self to 0 if the number of bits shifted are
    /// higher than the width of the type
    fn shr_assign_saturate(&mut self, rhs: RHS);
}

#[cfg(feature = "specialization")]
impl<R, T: Shr<R>> ShrSaturate<R> for T {
    type Output = <T as Shr<R>>::Output;
    default fn shr_saturate(self, rhs: R) -> Self::Output { self >> rhs }
}

#[cfg(feature = "specialization")]
impl<R, T: ShrAssign<R>> ShrSaturateAssign<R> for T {
    default fn shr_assign_saturate(&mut self, rhs: R) { *self >>= rhs; }
}

/// Shift left, return 0 if the number of bits shifted are higher than the
/// width of the type
///
/// This does the same as the `std::ops::Shl` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShlSaturate<RHS=usize> {
    /// the return type of our shift operation
    type Output;
    /// shift left, return 0 if the number of bits shifted are higher than the
    /// width of the type
    fn shl_saturate(self, rhs: RHS) -> Self::Output;
}

/// Shift left in place, set self to 0 if the number of bits shifted are
/// higher than the width of the type
///
/// This does the same as the `std::ops::ShlAssign` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShlAssignSaturate<RHS=usize> {
    /// shift left in place, set self to 0 if the number of bits shifted are
    /// higher than the width of the type
    fn shl_assign_saturate(&mut self, rhs: RHS);
}

#[cfg(feature = "specialization")]
impl<R, T: Shl<R>> ShlSaturate<R> for T {
    type Output = <T as Shl<R>>::Output;
    default fn shl_saturate(self, rhs: R) -> Self::Output { self << rhs }
}

#[cfg(feature = "specialization")]
impl<R, T: ShlAssign<R>> ShlAssignSaturate<R> for T {
    default fn shl_assign_saturate(&mut self, rhs: R) { *self <<= rhs; }
}

/// Shift left, panic if bits are shifted out of the value
///
/// This does the same as the `std::ops::Shl` trait for most types.
/// it is specialized for integer types to panic on over- or underflow.
pub trait ShlPanic<RHS=usize> {
    /// the result type of our left shift
    type Output;

    /// shift left, panic if bits are shifted out of the value
    fn shl_panic(self, rhs: RHS) -> Self::Output;
}

#[cfg(feature = "specialization")]
impl<T, R> ShlPanic<R> for T where T: Shl<R> {
    type Output = <T as Shl<R>>::Output;
    default fn shl_panic(self, rhs: R) -> Self::Output {
        std::ops::Shl::shl(self, rhs)
    }
}

/// Shift left in place, panic if bits are shifted out of the value
///
/// This does the same as the `std::ops::Shl` trait for most types.
/// it is specialized for integer types to panic on over- or underflow.
pub trait ShlAssignPanic<RHS=usize> {
    /// Shift left in place, panic if bits are shifted out of the value
    fn shl_assign_panic(&mut self, rhs: RHS);
}

#[cfg(feature = "specialization")]
impl<T, R> ShlAssignPanic<R> for T where T: ShlAssign<R> {
    default fn shl_assign_panic(&mut self, rhs: R) {
        ShlAssign::shl_assign(self, rhs)
    }
}

/// Shift right in place, set self to 0 if the number of bits shifted are
/// higher than the width of the type
///
/// This does the same as the `std::ops::ShlAssign` trait for most types.
/// it is specialized for integer types to return zero on over- or underflow.
pub trait ShrAssignSaturate<RHS=usize> {
    /// shift right in place, set self to 0 if the number of bits shifted are
    /// higher than the width of the type
    fn shr_assign_saturate(&mut self, rhs: RHS);
}

macro_rules! saturate_shl_unsigned {
    ($ty:ty, $max:expr, $bits:expr) => {
        saturate_shl_unsigned!($ty, $max, $bits, u8);
        saturate_shl_unsigned!($ty, $max, $bits, u16);
        saturate_shl_unsigned!($ty, $max, $bits, u32);
        saturate_shl_unsigned!($ty, $max, $bits, u64);
        saturate_shl_unsigned!($ty, $max, $bits, usize);
        saturate_shl_unsigned!($ty, $max, $bits, i8);
        saturate_shl_unsigned!($ty, $max, $bits, i16);
        saturate_shl_unsigned!($ty, $max, $bits, i32);
        saturate_shl_unsigned!($ty, $max, $bits, i64);
        saturate_shl_unsigned!($ty, $max, $bits, isize);
    };
    ($ty:ty, $max:expr, $bits:expr, $rty:ty) => {
        impl ShlSaturate<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn shl_saturate(self, rhs: $rty) -> Self::Output {
                if self == 0 { return 0; }
                if rhs as usize >= $bits || ((!0) >> rhs) < self {
                    $max
                } else {
                    self << rhs
                }
            }
        }

        impl ShrSaturate<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn shr_saturate(self, rhs: $rty) -> Self::Output {
                if rhs as usize >= $bits { 0 } else { self >> rhs }
            }
        }

        impl ShlAssignSaturate<$rty> for $ty {
            fn shl_assign_saturate(&mut self, rhs: $rty) {
                if *self == 0 { return; }
                *self = if rhs as usize >= $bits || (!0) >> rhs < *self {
                    $max
                } else {
                    *self << rhs
                }
            }
        }

        impl ShrAssignSaturate<$rty> for $ty {
            fn shr_assign_saturate(&mut self, rhs: $rty) {
                *self = self.checked_shr(rhs as u32).unwrap_or(0);
            }
        }

        impl ShlPanic<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn shl_panic(self, rhs: $rty) -> Self::Output {
                if self == 0 { return 0; }
                if (rhs as usize >= $bits || ((!0) >> rhs) < self) && self != 0 {
                    panic!("Arithmetic overflow");
                }
                self << rhs
            }
        }

        impl ShlAssignPanic<$rty> for $ty {
            fn shl_assign_panic(&mut self, rhs: $rty) {
                if *self == 0 { return; }
                *self = if rhs as usize >= $bits || (!0) >> rhs < *self {
                    panic!("Arithmetic overflow");
                } else {
                    *self << rhs
                }
            }
        }
    };
}

#[cfg(target_pointer_width = "16")]
const USIZE_BITS: usize = 16;

#[cfg(target_pointer_width = "32")]
const USIZE_BITS: usize = 16;

#[cfg(target_pointer_width = "64")]
const USIZE_BITS: usize = 64;

saturate_shl_unsigned!(u8, std::u8::MAX, 8);
saturate_shl_unsigned!(u16, std::u16::MAX, 16);
saturate_shl_unsigned!(u32, std::u32::MAX, 32);
saturate_shl_unsigned!(u64, std::u64::MAX, 64);
saturate_shl_unsigned!(usize, std::usize::MAX, USIZE_BITS);

macro_rules! saturate_shl_signed {
    ($ty:ty, $max:expr, $min:expr, $bits:expr) => {
        saturate_shl_signed!($ty, $max, $min, $bits, u8);
        saturate_shl_signed!($ty, $max, $min, $bits, u16);
        saturate_shl_signed!($ty, $max, $min, $bits, u32);
        saturate_shl_signed!($ty, $max, $min, $bits, u64);
        saturate_shl_signed!($ty, $max, $min, $bits, usize);
        saturate_shl_signed!($ty, $max, $min, $bits, i8);
        saturate_shl_signed!($ty, $max, $min, $bits, i16);
        saturate_shl_signed!($ty, $max, $min, $bits, i32);
        saturate_shl_signed!($ty, $max, $min, $bits, i64);
        saturate_shl_signed!($ty, $max, $min, $bits, isize);
    };
    ($ty:ty, $max:expr, $min:expr, $bits:expr, $rty:ty) => {
        impl ShlSaturate<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn shl_saturate(self, rhs: $rty) -> Self::Output {
                match self.cmp(&0) {
                    Ordering::Equal => 0,
                    Ordering::Greater => {
                        if rhs as usize >= $bits || ($max >> rhs) < self { $max } else { self << rhs }
                    }
                    Ordering::Less => {
                        if rhs as usize >= $bits || ($min >> rhs) > self { $min } else { self << rhs }
                    }
                }
            }
        }

        impl ShrSaturate<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn shr_saturate(self, rhs: $rty) -> Self::Output {
                if rhs as usize >= $bits { 0 } else { self >> rhs }
            }
        }

        impl ShlAssignSaturate<$rty> for $ty {
            fn shl_assign_saturate(&mut self, rhs: $rty) {
                let s = *self;
                *self = match s.cmp(&0) {
                    Ordering::Equal => 0,
                    Ordering::Greater => {
                        if rhs as usize >= $bits || ($max >> rhs) < s { $max } else { s << rhs }
                    }
                    Ordering::Less => {
                        if rhs as usize >= $bits || ($min >> rhs) > s { $min } else { s << rhs }
                    }
                }
            }
        }

        impl ShrAssignSaturate<$rty> for $ty {
            fn shr_assign_saturate(&mut self, rhs: $rty) {
                *self = self.checked_shr(rhs as u32).unwrap_or(0);
            }
        }

        impl ShlPanic<$rty> for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn shl_panic(self, rhs: $rty) -> Self::Output {
                match self.cmp(&0) {
                    Ordering::Equal => return 0,
                    Ordering::Greater => {
                        if rhs as usize >= $bits || ($max >> rhs) < self { panic!("Arithmetic overflow"); }
                    }
                    Ordering::Less => {
                        if rhs as usize >= $bits || ($min >> rhs) > self { panic!("Arithmetic overflow"); }
                    }
                }
                self << rhs
            }
        }

        impl ShlAssignPanic<$rty> for $ty {
            fn shl_assign_panic(&mut self, rhs: $rty) {
                let s = *self;
                match s.cmp(&0) {
                    Ordering::Equal => return,
                    Ordering::Greater => {
                        if rhs as usize >= $bits || ($max >> rhs) < s { panic!("Arithmetic overflow"); }
                    }
                    Ordering::Less => {
                        if rhs as usize >= $bits || ($min >> rhs) > s { panic!("Arithmetic overflow"); }
                    }
                }
                *self <<= rhs
            }
        }
    };
}

#[cfg(target_pointer_width = "16")]
const ISIZE_BITS: usize = 15;

#[cfg(target_pointer_width = "32")]
const ISIZE_BITS: usize = 31;

#[cfg(target_pointer_width = "64")]
const ISIZE_BITS: usize = 63;


saturate_shl_signed!(i8, std::i8::MAX, std::i8::MIN, 7);
saturate_shl_signed!(i16, std::i16::MAX, std::i16::MIN, 15);
saturate_shl_signed!(i32, std::i32::MAX, std::i32::MIN, 31);
saturate_shl_signed!(i64, std::i64::MAX, std::i64::MIN, 64);
saturate_shl_signed!(isize, std::isize::MAX, std::isize::MIN, ISIZE_BITS);

/// Negate a value, panic on overflow
///
/// This does the same as the `std::ops::Neg` trait for most types.
/// it is specialized for integer types to panic on overflow.
pub trait NegPanic {
    /// the result type of the negation
    type Output;
    /// negate a value, panic on overflow
    fn neg_panic(self) -> Self::Output;
}

#[cfg(feature = "specialization")]
impl<T> NegPanic for T where T: Neg {
    type Output = <T as Neg>::Output;
    default fn neg_panic(self) -> Self::Output {
        -self
    }
}

macro_rules! neg_panic {
    ($ty:ty) => {
        impl NegPanic for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn neg_panic(self) -> Self::Output {
                if let Some(x) = self.checked_neg() { x }
                else { panic!("arithmetic overflow") }
            }
        }
    }
}

neg_panic!(i8);
neg_panic!(i16);
neg_panic!(i32);
neg_panic!(i64);
neg_panic!(isize);

/// Negate a value, wrap on overflow
///
/// This does the same as the `std::ops::Neg` trait for most types.
/// it is specialized for integer types to wrap on overflow.
pub trait NegWrap {
    /// the result type of the negation
    type Output;
    /// negate a value, wrap on overflow
    fn neg_wrap(self) -> Self::Output;
}

#[cfg(feature = "specialization")]
impl<T> NegWrap for T where T: Neg {
    type Output = <T as Neg>::Output;
    default fn neg_wrap(self) -> Self::Output {
        -self
    }
}

macro_rules! neg_wrap {
    ($ty:ty) => {
        impl NegWrap for $ty {
            #[cfg(not(feature = "specialization"))]
            type Output = $ty;

            fn neg_wrap(self) -> Self::Output {
                self.wrapping_neg()
            }
        }
    }
}

neg_wrap!(i8);
neg_wrap!(i16);
neg_wrap!(i32);
neg_wrap!(i64);
neg_wrap!(isize);

/// Negate a value, saturate on overflow
///
/// This does the same as the `std::ops::Neg` trait for most types.
/// it is specialized for integer types to saturate on overflow.
pub trait NegSaturate {
    /// the output type of the negation
    type Output;
    /// negate a value, saturate on overflow
    fn neg_saturate(self) -> Self::Output;
}

macro_rules! neg_saturate {
    ($ty:ty, $min:expr, $max:expr) => {
        impl NegSaturate for $ty {
            type Output = Self;

            fn neg_saturate(self) -> Self {
                if self == $min { $max } else { -self }
            }
        }
    };
}

neg_saturate!(i8, std::i8::MIN, std::i8::MAX);
neg_saturate!(i16, std::i16::MIN, std::i16::MAX);
neg_saturate!(i32, std::i32::MIN, std::i32::MAX);
neg_saturate!(i64, std::i64::MIN, std::i64::MAX);
neg_saturate!(isize, std::isize::MIN, std::isize::MAX);

/// Compute the absolute value of `self`, panicking on overflow
///
/// This does the same as the `std::i*::abs(_)` methods, but panics on overflow
pub trait AbsPanic {
    /// compute the absolute value of `self`, panicking on overflow
    fn abs_panic(self) -> Self;
}

/// Compute the absolute value of `self`, wrapping on overflow
///
/// This does the same as the `std::i*::abs(_)` methods, but wraps on overflow
pub trait AbsWrap {
    /// compute the absolute value of `self`, wrapping on overflow
    fn abs_wrap(self) -> Self;
}

/// Compute the absolute value of `self`, saturating on overflow
///
/// This does the same as the `std::i*::abs(_)` methods, but saturates on
/// overflow
pub trait AbsSaturate {
    /// compute the absolute value of `self`, saturating on overflow
    fn abs_saturate(self) -> Self;
}

macro_rules! abs_unsigned {
    ($ty:ty) => {
        impl AbsPanic for $ty {
            fn abs_panic(self) -> Self {
                self
            }
        }

        impl AbsWrap for $ty {
            fn abs_wrap(self) -> Self {
                self
            }
        }

        impl AbsSaturate for $ty {
            fn abs_saturate(self) -> Self {
                self
            }
        }
    };
}

abs_unsigned!(u8);
abs_unsigned!(u16);
abs_unsigned!(u32);
abs_unsigned!(u64);
abs_unsigned!(usize);

macro_rules! abs_signed {
    ($ty:ty) => {
        impl AbsPanic for $ty {
            fn abs_panic(self) -> Self {
                if self < 0 { 0.sub_panic(self) } else { self }
            }
        }

        impl AbsWrap for $ty {
            fn abs_wrap(self) -> Self {
                if self < 0 { 0.sub_wrap(self) } else { self }
            }
        }

        impl AbsSaturate for $ty {
            fn abs_saturate(self) -> Self {
                if self < 0 { 0.sub_saturate(self) } else { self }
            }
        }
    };
}

abs_signed!(i8);
abs_signed!(i16);
abs_signed!(i32);
abs_signed!(i64);
abs_signed!(isize);

macro_rules! impls_inner {
    (op all, $ty:ty, $($gen:tt),*) => {
        impls_inner!(op add, $ty, $($gen),*);
        impls_inner!(op sub, $ty, $($gen),*);
        impls_inner!(op mul, $ty, $($gen),*);
        impls_inner!(op div, $ty, $($gen),*);
        impls_inner!(op rem, $ty, $($gen),*);
        impls_inner!(op shl, $ty, $($gen),*);
        impls_inner!(op shr, $ty, $($gen),*);
        impls_inner!(op neg, $ty, $($gen),*);
        impls_inner!(op add_assign, $ty, $($gen),*);
        impls_inner!(op sub_assign, $ty, $($gen),*);
        impls_inner!(op mul_assign, $ty, $($gen),*);
        impls_inner!(op div_assign, $ty, $($gen),*);
        impls_inner!(op rem_assign, $ty, $($gen),*);
        impls_inner!(op shl_assign, $ty, $($gen),*);
        impls_inner!(op shr_assign, $ty, $($gen),*);
    };
    (op add, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin +, Add, AddWrap, add_wrap, $ty, $($gen),*);
        impls_inner!(bin +, Add, AddPanic, add_panic, $ty, $($gen),*);
        impls_inner!(bin +, Add, AddSaturate, add_saturate, $ty, $($gen),*);
    };
    (op sub, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin -, Sub, SubWrap, sub_wrap, $ty, $($gen),*);
        impls_inner!(bin -, Sub, SubPanic, sub_panic, $ty, $($gen),*);
        impls_inner!(bin -, Sub, SubSaturate, sub_saturate, $ty, $($gen),*);
    };
    (op mul, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin *, Mul, MulWrap, mul_wrap, $ty, $($gen),*);
        impls_inner!(bin *, Mul, MulPanic, mul_panic, $ty, $($gen),*);
        impls_inner!(bin *, Mul, MulSaturate, mul_saturate, $ty, $($gen),*);
    };
    (op div, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin /, Div, DivWrap, div_wrap, $ty, $($gen),*);
        impls_inner!(bin /, Div, DivPanic, div_panic, $ty, $($gen),*);
        impls_inner!(bin /, Div, DivSaturate, div_saturate, $ty, $($gen),*);
    };
    (op rem, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin %, Rem, RemWrap, rem_wrap, $ty, $($gen),*);
        impls_inner!(bin %, Rem, RemPanic, rem_panic, $ty, $($gen),*);
        impls_inner!(bin %, Rem, RemSaturate, rem_saturate, $ty, $($gen),*);
    };
    (op shl, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin <<, Shl, ShlWrap, shl_wrap, $ty, $($gen),*);
        impls_inner!(bin <<, Shl, ShlPanic, shl_panic, $ty, $($gen),*);
        impls_inner!(bin <<, Shl, ShlSaturate, shl_saturate, $ty, $($gen),*);
    };
    (op shr, $ty:ty, $($gen:tt),*) => {
        impls_inner!(bin >>, Shr, ShrWrap, shr_wrap, $ty, $($gen),*);
        impls_inner!(bin >>, Shr, ShrPanic, shr_panic, $ty, $($gen),*);
        impls_inner!(bin >>, Shr, ShrSaturate, shr_saturate, $ty, $($gen),*);
    };
    (op neg, $ty:ty, $($gen:tt),*) => {
        impls_inner!(neg Neg, NegWrap, neg_wrap, $ty, $($gen),*);
        impls_inner!(neg Neg, NegPanic, neg_panic, $ty, $($gen),*);
        impls_inner!(neg Neg, NegSaturate, neg_saturate, $ty, $($gen),*);
    };
    (op abs, $ty:ty, $($gen:tt),*) => {
        impls_inner!(abs AbsWrap, abs_wrap, $ty, $($gen),*);
        impls_inner!(abs AbsPanic, abs_panic, $ty, $($gen),*);
        impls_inner!(abs AbsSaturate, abs_saturate, $ty, $($gen),*);
    };
    (op add_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign +=, AddAssign, AddAssignWrap, add_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign +=, AddAssign, AddAssignPanic, add_assign_panic, $ty, $($gen),*);
        impls_inner!(assign +=, AddAssign, AddAssignSaturate, add_assign_saturate, $ty, $($gen),*);
    };
    (op sub_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign -=, SubAssign, SubAssignWrap, sub_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign -=, SubAssign, SubAssignPanic, sub_assign_panic, $ty, $($gen),*);
        impls_inner!(assign -=, SubAssign, SubAssignSaturate, sub_assign_saturate, $ty, $($gen),*);
    };
    (op mul_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign *=, MulAssign, MulAssignWrap, mul_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign *=, MulAssign, MulAssignPanic, mul_assign_panic, $ty, $($gen),*);
        impls_inner!(assign *=, MulAssign, MulAssignSaturate, mul_assign_saturate, $ty, $($gen),*);
    };
    (op div_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign /=, DivAssign, DivAssignWrap, div_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign /=, DivAssign, DivAssignPanic, div_assign_panic, $ty, $($gen),*);
        impls_inner!(assign /=, DivAssign, DivAssignSaturate, div_assign_saturate, $ty, $($gen),*);
    };
    (op rem_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign %=, RemAssign, RemAssignWrap, rem_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign %=, RemAssign, RemAssignPanic, rem_assign_panic, $ty, $($gen),*);
        impls_inner!(assign %=, RemAssign, RemAssignSaturate, rem_assign_saturate, $ty, $($gen),*);
    };
    (op shl_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign <<=, ShlAssign, ShlAssignWrap, shl_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign <<=, ShlAssign, ShlAssignPanic, shl_assign_panic, $ty, $($gen),*);
        impls_inner!(assign <<=, ShlAssign, ShlAssignSaturate, shl_assign_saturate, $ty, $($gen),*);
    };
    (op shr_assign, $ty:ty, $($gen:tt),*) => {
        impls_inner!(assign >>=, ShrAssign, ShrAssignWrap, shr_assign_wrap, $ty, $($gen),*);
        impls_inner!(assign >>=, ShrAssign, ShrAssignPanic, shr_assign_panic, $ty, $($gen),*);
        impls_inner!(assign >>=, ShrAssign, ShrAssignSaturate, shr_assign_saturate, $ty, $($gen),*);
    };
    (neg $origtrait:ident, $newtrait:ident, $fun:ident, $ty:ty,) => {
        impl $newtrait for $ty
        where $ty: $origtrait {
            #[cfg(not(feature = "specialization"))]
            type Output = <$ty as $origtrait>::Output;

            fn $fun(self) -> Self::Output {
                -self
            }
        }
    };
    (neg $origtrait:ident, $newtrait:ident, $fun:ident, $ty:ty, $($gen:tt),+) => {
        impl<$($gen),*> $newtrait for $ty
        where $ty: $origtrait {
            #[cfg(not(feature = "specialization"))]
            type Output = <Self as $origtrait>::Output;

            fn $fun(self) -> Self::Output {
                -self
            }
        }
    };
    (abs $newtrait:ident, $fun:ident, $ty:ty,) => {
        impl $newtrait for $ty {
            fn $fun(self) -> Self {
                -self
            }
        }
    };
    (abs $newtrait:ident, $fun:ident, $ty:ty, $($gen:tt),+) => {
        impl<$($gen),*> $newtrait for $ty {
            fn $fun(self) -> Self {
                -self
            }
        }
    };
    (bin $op:tt, $origtrait:ident, $newtrait:ident, $fun:ident, $ty:ty,) => {
        impl<Rhs> $newtrait<Rhs> for $ty
        where $ty: $origtrait<Rhs> {
            #[cfg(not(feature = "specialization"))]
            type Output = <Self as $origtrait<Rhs>>::Output;

            fn $fun(self, rhs: Rhs) -> Self::Output {
                self $op rhs
            }
        }
    };
    (bin $op:tt, $origtrait:ident, $newtrait:ident, $fun:ident, $ty:ty, $($gen:tt),+) => {
        impl<$($gen),*, Rhs> $newtrait<Rhs> for $ty
        where $ty: $origtrait<Rhs> {
            #[cfg(not(feature = "specialization"))]
            type Output = <Self as $origtrait<Rhs>>::Output;

            fn $fun(self, rhs: Rhs) -> Self::Output {
                self $op rhs
            }
        }
    };
    (assign $op:tt, $origtrait:ident, $newtrait:ident, $fun:ident, $ty:ty,) => {
        impl<Rhs> $newtrait<Rhs> for $ty
        where $ty: $origtrait<Rhs> {
            fn $fun(&mut self, rhs: Rhs) {
                *self $op rhs;
            }
        }
    };
    (assign $op:tt, $origtrait:ident, $newtrait:ident, $fun:ident, $ty:ty, $($gen:tt),+) => {
        impl<$($gen),*, Rhs> $newtrait<Rhs> for $ty
        where $ty: $origtrait<Rhs> {
            fn $fun(&mut self, rhs: Rhs) {
                *self $op rhs;
            }
        }
    };
}

macro_rules! impls_generic {
    ($ty:ty; $($gen:tt),*; $op:tt $($ops:tt)*) => {
        impls_generic!($ty; $($gen),*; $($ops)*);
        impls_inner!(op $op, $ty, $($gen),*);
    };
    ($ty:ty; $($gen:tt),*; ) => {};
}

macro_rules! impls_plain {
    ($ty:ty; $op:tt $($ops:tt)*) => {
        impls_plain!($ty; $($ops)*);
        impls_inner!(op $op, $ty, );
    };
    ($ty:ty;) => {};
}

/// Add implementations of the respective traits for a type
///
/// You call it with your type, optionally `:` plus all lifetimes and types
/// your type is generic over, and a space-separated sequence of operations:
///
/// * add, add_assign
/// * sub, sub_assign
/// * mul, mul_assign
/// * div, div_assign
/// * rem, rem_assign
/// * shl, shl_assign
/// * shr, shr_assign
/// * neg
/// * all implements all operators
///
/// # Examples:
///
/// ```ignore
/// type Boring<'a, T>(&'a T);
///
/// impls!(Boring<'a, T> : 'a, T; add sub mul div);
#[macro_export]
macro_rules! impls {
    ($ty:ty : $($gen:tt),*; $($rest:tt)*) => {
        impls_generic!($ty; $($gen),*; $($rest)*);
    };
    ($ty:ty; $($rest:tt)*) => {
        impls_plain!($ty; $($rest)*);
    };
}

impls!(std::borrow::Cow<'a, str> : 'a; add add_assign);
impls!(String; add add_assign);
impls!(core::num::Wrapping<N> : N; all);
impls!(&'a core::num::Wrapping<N> : 'a, N; all);
#[cfg(feature = "wrapping_int_impl")]
mod wrapping_int_impls {
    impls!(core::num::Wrapping<i8>; abs);
    impls!(core::num::Wrapping<i16>; abs);
    impls!(core::num::Wrapping<i32>; abs);
    impls!(core::num::Wrapping<i64>; abs);
    impls!(core::num::Wrapping<i128>; abs);
    impls!(core::num::Wrapping<isize>; abs);

}
