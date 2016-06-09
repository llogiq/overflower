//! This defines some traits so we can replace ops with method calls of the respective traits
//! (provided they're in scope) without worrying about argument types (hopefully)
//!
//! The traits are:
//! * AddPanic, SubPanic, MulPanic, DivPanic, RemPanic, ShlPanic, ShrPanic, NegPanic
//! * AddWrap, SubWrap, Mulwrap, DivWrap, RemWrap, ShlWrap, ShrWrap, NegWrap
//! * AddSaturate, SubSaturate, MulSaturate
//!
//! The `*Panic` traits all panic on overflow, the `*Wrap` traits wrap around and the
//! `*Saturate` traits saturate.
//!
//! Note: This needs a nightly compiler because it uses the specialization feature.

#![feature(specialization)]
use std::ops::*;

macro_rules! panic_biself {
    ($trait_name:ident, $trait_panic:ident, $fn_name:ident, $fn_panic:ident, $checked_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_panic<RHS = Self> {
            type Output;
            fn $fn_panic(self, rhs: RHS) -> Self::Output;
        }

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
            fn $fn_panic(self, rhs: $ty) -> $ty {
                self.$checked_fn(rhs).expect("arithmetic overflow")
            }
        }
    }
}

panic_biself!(Add, AddPanic, add, add_panic, checked_add);
panic_biself!(Sub, SubPanic, sub, sub_panic, checked_sub);
panic_biself!(Mul, MulPanic, mul, mul_panic, checked_mul);
panic_biself!(Div, DivPanic, div, div_panic, checked_div);
panic_biself!(Rem, RemPanic, rem, rem_panic, checked_rem);

macro_rules! panic_assign_biself {
    ($trait_name:ident, $trait_panic:ident, $fn_name:ident, $fn_panic:ident, $checked_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_panic<RHS = Self> {
            fn $fn_panic(&mut self, rhs: RHS);
        }

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
                *self = self.$checked_fn(rhs).expect("arithmetic overflow");
            }
        }
    }
}

panic_assign_biself!(AddAssign, AddPanicAssign, add_assign, add_assign_panic, checked_add);
panic_assign_biself!(SubAssign, SubPanicAssign, sub_assign, sub_assign_panic, checked_sub);
panic_assign_biself!(MulAssign, MulPanicAssign, mul_assign, mul_assign_panic, checked_mul);
panic_assign_biself!(DivAssign, DivPanicAssign, div_assign, div_assign_panic, checked_div);
panic_assign_biself!(RemAssign, RemPanicAssign, rem_assign, rem_assign_panic, checked_rem);

macro_rules! wrap_biself {
    ($trait_name:ident, $trait_wrap:ident, $fn_name:ident, $fn_wrap:ident, $wrapped_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_wrap<RHS = Self> {
            type Output;
            fn $fn_wrap(self, rhs: RHS) -> Self::Output;
        }

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
            fn $fn_wrap(self, rhs: $ty) -> $ty {
                self.$wrapped_fn(rhs)
            }
        }
    }
}

wrap_biself!(Add, AddWrap, add, add_wrap, wrapping_add);
wrap_biself!(Sub, SubWrap, sub, sub_wrap, wrapping_sub);
wrap_biself!(Mul, MulWrap, mul, mul_wrap, wrapping_mul);
wrap_biself!(Div, DivWrap, div, div_wrap, wrapping_div);
wrap_biself!(Rem, RemWrap, rem, rem_wrap, wrapping_rem);

macro_rules! wrap_assign_biself {
    ($trait_name:ident, $trait_wrap:ident, $fn_name:ident, $fn_wrap:ident, $wrapped_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_wrap<RHS = Self> {
            fn $fn_wrap(&mut self, rhs: RHS);
        }

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

wrap_assign_biself!(AddAssign, AddWrapAssign, add_assign, add_assign_wrap, wrapping_add);
wrap_assign_biself!(SubAssign, SubWrapAssign, sub_assign, sub_assign_wrap, wrapping_sub);
wrap_assign_biself!(MulAssign, MulWrapAssign, mul_assign, mul_assign_wrap, wrapping_mul);
wrap_assign_biself!(DivAssign, DivWrapAssign, div_assign, div_assign_wrap, wrapping_div);
wrap_assign_biself!(RemAssign, RemWrapAssign, rem_assign, rem_assign_wrap, wrapping_rem);

macro_rules! saturate_biself {
    ($trait_name:ident, $trait_saturate:ident, $fn_name:ident, $fn_saturate:ident, $saturated_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_saturate<RHS = Self> {
            type Output;
            fn $fn_saturate(self, rhs: RHS) -> Self::Output;
        }

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
            fn $fn_saturate(self, rhs: $ty) -> $ty {
                self.$saturated_fn(rhs)
            }
        }
    }
}

saturate_biself!(Add, AddSaturate, add, add_saturate, saturating_add);
saturate_biself!(Sub, SubSaturate, sub, sub_saturate, saturating_sub);
saturate_biself!(Mul, MulSaturate, mul, mul_saturate, saturating_mul);

pub trait DivSaturate<Rhs=Self> {
    type Output;
    fn div_saturate(self, rhs: Rhs) -> Self::Output;
}

pub trait RemSaturate<RHS=Self> {
    type Output;
    fn rem_saturate(self, rhs: RHS) -> Self::Output;
}

macro_rules! saturate {
    ($ty:ty, $min:path, $max:path) => {
        #[allow(unused_comparisons)]
        impl DivSaturate for $ty {
            type Output = $ty;
            fn div_saturate(self, rhs: $ty) -> $ty {
                if rhs != 0 { self / rhs }
                else if self < 0 { $min }
                else if self == 0 { 0 }
                else { $max }
            }
        }
        
        impl RemSaturate for $ty {
            type Output = $ty;
            fn rem_saturate(self, rhs: $ty) -> $ty {
                self % rhs
            }
        }
    };
}

saturate!(u8,    std::u8::MIN,    std::u8::MAX);
saturate!(u16,   std::u16::MIN,   std::u16::MAX);
saturate!(u32,   std::u32::MIN,   std::u32::MAX);
saturate!(u64,   std::u64::MIN,   std::u64::MAX);
saturate!(usize, std::usize::MIN, std::usize::MAX);
saturate!(i8,    std::i8::MIN,    std::i8::MAX);
saturate!(i16,   std::i16::MIN,   std::i16::MAX);
saturate!(i32,   std::i32::MIN,   std::i32::MAX);
saturate!(i64,   std::i64::MIN,   std::i64::MAX);
saturate!(isize, std::isize::MIN, std::isize::MAX);

macro_rules! panic_shifts {
    (@$trait_name:ident, $trait_panic:ident, $fn_name:ident, $fn_panic:ident, $checked_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_panic<RHS=usize> {
            type Output;
            fn $fn_panic(self, rhs: RHS) -> Self::Output;
        }

        impl<T, R> $trait_panic<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_panic(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        panic_shifts!($trait_panic, $fn_panic, $checked_fn, u8);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, u16);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, u32);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, u64);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, usize);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, i8);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, i16);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, i32);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, i64);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, isize);
    };
    ($trait_panic:ident, $fn_panic:ident, $checked_fn:ident, $ty:ty) => {
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, u8);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, u16);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, u32);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, u64);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, usize);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, i8);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, i16);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, i32);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, i64);
        panic_shifts!($trait_panic, $fn_panic, $checked_fn, $ty, isize);
    };
    ($trait_panic:ident, $fn_panic:ident, $checked_fn:ident, $ty:ty, $rty:ty) => {
        impl $trait_panic<$rty> for $ty {
            fn $fn_panic(self, rhs: $rty) -> Self::Output {
                self.$checked_fn(rhs as u32).expect("Arithmetic overflow")
            }
        }
    }
}

panic_shifts!(@Shl, ShlPanic, shl, shl_panic, checked_shl);
panic_shifts!(@Shr, ShrPanic, shr, shr_panic, checked_shr);

macro_rules! wrap_shifts {
    (@$trait_name:ident, $trait_wrap:ident, $fn_name:ident, $fn_wrap:ident, $wrapping_fn:ident) => {
        #[doc(hidden)]
        pub trait $trait_wrap<RHS=usize> {
            type Output;
            fn $fn_wrap(self, rhs: RHS) -> Self::Output;
        }

        impl<T, R> $trait_wrap<R> for T where T: $trait_name<R> {
            type Output = <T as $trait_name<R>>::Output;
            default fn $fn_wrap(self, rhs: R) -> Self::Output {
                std::ops::$trait_name::$fn_name(self, rhs)
            }
        }

        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, u8);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, u16);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, u32);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, u64);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, usize);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, i8);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, i16);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, i32);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, i64);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, isize);
    };
    ($trait_wrap:ident, $fn_wrap:ident, $wrapping_fn:ident, $ty:ty) => {
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, u8);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, u16);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, u32);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, u64);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, usize);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, i8);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, i16);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, i32);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, i64);
        wrap_shifts!($trait_wrap, $fn_wrap, $wrapping_fn, $ty, isize);
    };
    ($trait_wrap:ident, $fn_wrap:ident, $wrapping_fn:ident, $ty:ty, $rty:ty) => {
        impl $trait_wrap<$rty> for $ty {
            fn $fn_wrap(self, rhs: $rty) -> Self::Output {
                self.$wrapping_fn(rhs as u32)
            }
        }
    }
}

wrap_shifts!(@Shl, ShlWrap, shl, shl_wrap, wrapping_shl);
wrap_shifts!(@Shr, ShrWrap, shr, shr_wrap, wrapping_shr);

#[doc(hidden)]
pub trait NegPanic {
    type Output;
    fn neg_panic(self) -> Self::Output;
}

impl<T> NegPanic for T where T: Neg {
    type Output = <T as Neg>::Output;
    default fn neg_panic(self) -> Self::Output {
        -self
    }
}

macro_rules! neg_panic {
    ($ty:ty) => {
        impl NegPanic for $ty {
            fn neg_panic(self) -> Self::Output {
                self.checked_neg().expect("arithmetic overflow")
            }
        }
    }
}

neg_panic!(i8);
neg_panic!(i16);
neg_panic!(i32);
neg_panic!(i64);
neg_panic!(isize);

#[doc(hidden)]
pub trait NegWrap {
    type Output;
    fn neg_wrap(self) -> Self::Output;
}

impl<T> NegWrap for T where T: Neg {
    type Output = <T as Neg>::Output;
    default fn neg_wrap(self) -> Self::Output {
        -self
    }
}

macro_rules! neg_wrap {
    ($ty:ty) => {
        impl NegWrap for $ty {
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

pub trait NegSaturate {
    fn neg_saturate(self) -> Self;
}


#[cfg(test)]
mod test {
    use super::{AddPanic, SubWrap, MulSaturate};
    
    #[test]
    fn test_add_panic_normal() {
        assert_eq!(1 + 2, 1.add_panic(2));
    }
    
    #[test]
    #[should_panic]
    fn test_add_panic_panics() {
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
}
