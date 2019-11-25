// macros for overflower helper traits & impls

macro_rules! doc {
    ($doc:expr, $($tt:tt)*) => { #[doc = $doc] $($tt)* };
}

macro_rules! op {
    // trait + tag machinery for binary + assign op
    (def2
        $t_op:ident, // overflower trait (e.g. `Add`)
        $t_assign:ident, // overflower assign trait (e.g. `AddAssign`)
        $t_op_std:ident,
        $t_assign_std:ident,
        $ovf_tag:ident, // overflower tag name (e.g. `OverflowerAddTag`)
        $ovf_tag_assign:ident, // overflower assign tag name
        $std_tag:ident, // std tag name
        $std_tag_assign:ident, // std assign tag name (e.g. `OverflowerAddAssign`
        $ovf_kind:ident, // overflower kind name (e.g. `OverflowerAddKind`)
        $ovf_kind_assign:ident, // overflower assign kind name
        $std_kind:ident,
        $std_kind_assign:ident, // std assign kind
        $tag_fn:ident, // overflower tag function name
        $tag_fn_assign:ident, // overflower assign tag function name
        $wrap_op:ident, // wrap op fn
        $panic_op:ident, // panic op fn
        $sat_op:ident, // saturating op fn
        $wrap_assign:ident, // wrap assign op fn
        $panic_assign:ident,
        $sat_assign:ident,
        $std_op:ident, // std op fn
        $std_assign:ident
    ) => {
        doc! { concat!("Overflow handing for ", stringify!($std_op)),
            pub trait $t_op<RHS = Self> {
                /// The output type of the given operations
                type Output;

                doc! { concat!("wrapping ", stringify!($std_op)),
                    fn $wrap_op(self, r: RHS) -> Self::Output;
                }

                doc! { concat!("checked ", stringify!($std_op)),
                    fn $panic_op(self, r: RHS) -> Self::Output;
                }

                doc! { concat!("saturating ", stringify!($std_op)),
                    fn $sat_op(self, r: RHS) -> Self::Output;
                }
            }
        }

        doc! { concat!("overflow handling for assigning ", stringify!($std_op)),
            pub trait $t_assign<RHS = Self> {
                doc! { concat!("wrapping assigining ", stringify!($std_op)),
                    fn $wrap_assign(&mut self, r: RHS);
                }
                doc! { concat!("checked assigining ", stringify!($std_op)),
                    fn $panic_assign(&mut self, r: RHS);
                }
                doc! { concat!("saturating assigining", stringify!($std_op)),
                    fn $sat_assign(&mut self, r: RHS);
                }
            }
        }

        op!(tag2 $std_tag, $tag_fn, $std_kind);
        op!(tag2 $ovf_tag, $tag_fn, $ovf_kind);
        op!(tag2 $std_tag_assign, $tag_fn_assign, $std_kind_assign);
        op!(tag2 $ovf_tag_assign, $tag_fn_assign, $ovf_kind_assign);
        impl<R, T> $std_kind<R> for &(&T, &R) where T: $t_op_std<R> {}
        impl<R, T> $std_kind_assign<R> for &(&T, &R) where T: $t_assign_std<R> {}
        impl<R, T> $ovf_kind<R> for (&T, &R) where T: $t_op<R> {}
        impl<R, T> $ovf_kind_assign<R> for (&T, &R) where T: $t_assign<R> {}
        op!(tag2impl $std_tag, $t_op_std, $wrap_op, $panic_op, $sat_op,
            $std_op, $std_op, $std_op);
        op!(tag2impl $ovf_tag, $t_op, $wrap_op, $panic_op, $sat_op,
            $wrap_op, $panic_op, $sat_op);
        op!(assigntagimpl $std_tag_assign, $t_assign_std, $wrap_assign,
            $panic_assign, $sat_assign, $std_assign, $std_assign, $std_assign);
        op!(assigntagimpl $ovf_tag_assign, $t_assign, $wrap_assign,
            $panic_assign, $sat_assign, $wrap_assign, $panic_assign, $sat_assign);
    };
    (trait1 
        $t_op:ident, $std_op:ident, $wrap_op:ident, $panic_op:ident,
        $sat_op:ident
    ) => {
        doc! { concat!("Overflow handing for ", stringify!($std_op)),
            pub trait $t_op {
                /// The output type of the given operations
                type Output;

                doc! { concat!("wrapping ", stringify!($std_op)),
                    fn $wrap_op(self) -> Self::Output;
                }

                doc! { concat!("checked ", stringify!($std_op)),
                    fn $panic_op(self) -> Self::Output;
                }

                doc! { concat!("saturating ", stringify!($std_op)),
                    fn $sat_op(self) -> Self::Output;
                }
            }
        }
    };
    (def1
        $t_op:ident, // overflower trait (e.g. `Add`)
        $t_op_std:ident,
        $ovf_tag:ident, // overflower tag name (e.g. `OverflowerAddTag`)
        $std_tag:ident, // std tag name
        $ovf_kind:ident, // overflower kind name (e.g. `OverflowerAddKind`)
        $std_kind:ident,
        $tag_fn:ident, // overflower tag function name
        $wrap_op:ident, // wrap op fn
        $panic_op:ident, // panic op fn
        $sat_op:ident, // saturating op fn
        $std_op:ident // std op fn
    ) => {
        op!(trait1 $t_op, $std_op, $wrap_op, $panic_op, $sat_op);
        op!(tag1 $std_tag, $tag_fn, $std_kind);
        op!(tag1 $ovf_tag, $tag_fn, $ovf_kind);
        impl<T> $std_kind for &T where T: $t_op_std {}
        impl<T> $ovf_kind for T where T: $t_op {}
        op!(tag1impl $std_tag, $t_op_std, $wrap_op, $panic_op, $sat_op,
            $std_op, $std_op, $std_op);
        op!(tag1impl $ovf_tag, $t_op, $wrap_op, $panic_op, $sat_op,
            $wrap_op, $panic_op, $sat_op);
    };
    (tag2 $tag:ident, $tag_fn:ident, $kind:ident) => {
        #[doc(hidden)]
        pub struct $tag;

        #[doc(hidden)]
        pub trait $kind<R> {
            #[doc(hidden)]
            #[inline(always)]
            fn $tag_fn(&self, _: &R) -> $tag { $tag }
        }
    };
    (tag1 $tag:ident, $tag_fn:ident, $kind:ident) => {
        #[doc(hidden)]
        pub struct $tag;

        #[doc(hidden)]
        pub trait $kind {
            #[doc(hidden)]
            #[inline(always)]
            fn $tag_fn(&self) -> $tag { $tag }
        }
    };
    (tag2impl $tag:ident, $t_op:ident, $wrap_op:ident, $op_panic:ident, $op_sat:ident,
        $wrap_fn:ident, $panic_fn:ident, $sat_fn:ident) => {
        impl $tag {
            #[doc(hidden)]
            #[inline(always)]
            pub fn $wrap_op<R, T: $t_op<R>>(self, t: T, r: R) -> <T as $t_op<R>>::Output {
                $t_op::$wrap_fn(t, r)
            }

            #[doc(hidden)]
            #[inline(always)]
            pub fn $op_panic<R, T: $t_op<R>>(self, t: T, r: R) -> <T as $t_op<R>>::Output {
                $t_op::$panic_fn(t, r)
            }

            #[doc(hidden)]
            #[inline(always)]
            pub fn $op_sat<R, T: $t_op<R>>(self, t: T, r: R) -> <T as $t_op<R>>::Output {
                $t_op::$sat_fn(t, r)
            }
        }
    };
    (assigntagimpl $tag:ident, $t_assign:ident, $wrap_op:ident, $op_panic:ident, $op_sat:ident,
        $wrap_fn:ident, $panic_fn:ident, $sat_fn:ident) => {
        impl $tag {
            #[doc(hidden)]
            #[inline(always)]
            pub fn $wrap_op<R, T: $t_assign<R>>(self, t: &mut T, r: R) {
                $t_assign::$wrap_fn(t, r)
            }

            #[doc(hidden)]
            #[inline(always)]
            pub fn $op_panic<R, T: $t_assign<R>>(self, t: &mut T, r: R) {
                $t_assign::$panic_fn(t, r)
            }

            #[doc(hidden)]
            #[inline(always)]
            pub fn $op_sat<R, T: $t_assign<R>>(self, t: &mut T, r: R) {
                $t_assign::$sat_fn(t, r)
            }
        }
    };
    (tag1impl $tag:ident, $t_op:ident, $wrap_op:ident, $op_panic:ident, $op_sat:ident,
        $wrap_fn:ident, $panic_fn:ident, $sat_fn:ident) => {
        impl $tag {
            #[doc(hidden)]
            #[inline(always)]
            pub fn $wrap_op<T: $t_op>(self, t: T) -> <T as $t_op>::Output {
                $t_op::$wrap_fn(t)
            }

            #[doc(hidden)]
            #[inline(always)]
            pub fn $op_panic<T: $t_op>(self, t: T) -> <T as $t_op>::Output {
                $t_op::$panic_fn(t)
            }

            #[doc(hidden)]
            #[inline(always)]
            pub fn $op_sat<T: $t_op>(self, t: T) -> <T as $t_op>::Output {
                $t_op::$sat_fn(t)
            }
        }
    };
    (impls2 $ty:ty) => { op!(impls2ty $ty); };
    (impls2 $ty:ty, $($rest:tt),*) => { op!(impls2ty $ty); op!(impls2 $($rest),*); };
    (impls1 $ty:ty) => { op!(impls1ty $ty); };
    (impls1 $ty:ty, $($rest:tt),*) => { op!(impls1ty $ty); op!(impls1 $($rest),*); };
    (impls2ty $ty:ty) => {
        impl SignedMax for $ty {
            fn signed_max(self) -> Self {
                if Self::min_value().count_ones() > 0 {
                    Self::max_value() ^ (self >> Self::max_value().count_ones())
                } else {
                    Self::max_value()
                }
            }
        }
        op!(impls2code $ty, $ty, self, r,
            OverflowerAdd, add_wrap, add_panic, add_saturate,
            OverflowerAddAssign, add_assign_wrap, add_assign_panic, add_assign_saturate,
            self.wrapping_add(r), self.checked_add(r).expect("arithmetic overflow"), 
            self.saturating_add(r));
        op!(impls2code $ty, $ty, self, r,
            OverflowerSub, sub_wrap, sub_panic, sub_saturate,
            OverflowerSubAssign, sub_assign_wrap, sub_assign_panic, sub_assign_saturate,
            self.wrapping_sub(r), self.checked_sub(r).expect("arithmetic overflow"), 
            self.saturating_sub(r));
        op!(impls2code $ty, $ty, self, r,
            OverflowerMul, mul_wrap, mul_panic, mul_saturate,
            OverflowerMulAssign, mul_assign_wrap, mul_assign_panic, mul_assign_saturate,
            self.wrapping_mul(r), self.checked_mul(r).expect("arithmetic overflow"), 
            self.saturating_mul(r));
        op!(impls2code $ty, $ty, self, r,
            OverflowerDiv, div_wrap, div_panic, div_saturate,
            OverflowerDivAssign, div_assign_wrap, div_assign_panic, div_assign_saturate,
            self.wrapping_div(r), self.checked_div(r).expect("arithmetic overflow"), 
            if r == 0 {
                if self == 0 { 0 } else { self.signed_max() }
            } else {
                self.wrapping_div(r)
            });
        op!(impls2code $ty, $ty, self, r,
            OverflowerRem, rem_wrap, rem_panic, rem_saturate,
            OverflowerRemAssign, rem_assign_wrap, rem_assign_panic, rem_assign_saturate,
            self.wrapping_rem(r), self.checked_rem(r).expect("arithmetic overflow"), 
            self.checked_rem(r).unwrap_or(0));
        op!(impls2shift $ty, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
    };
    (impls2shift $ty:ty, $rty:ty) => { op!(impls2shifty $ty, $rty); };
    (impls2shift $ty:ty, $rty:ty, $($rest:tt),*) => { 
        op!(impls2shifty $ty, $rty);
        op!(impls2shift $ty, $($rest),*);
    };
    (impls2shifty $ty:ty, $rty:ty) => {
        op!(impls2code $ty, $rty, self, r,
            OverflowerShl, shl_wrap, shl_panic, shl_saturate,
            OverflowerShlAssign, shl_assign_wrap, shl_assign_panic, shl_assign_saturate,
            self.wrapping_shl(r as u32), self.checked_shl(r as u32).expect("arithmetic overflow"), 
            self.checked_shl(r as u32).unwrap_or(0));
        op!(impls2code $ty, $rty, self, r,
            OverflowerShr, shr_wrap, shr_panic, shr_saturate,
            OverflowerShrAssign, shr_assign_wrap, shr_assign_panic, shr_assign_saturate,
            self.wrapping_shr(r as u32), self.checked_shr(r as u32).expect("arithmetic overflow"), 
            self.checked_shr(r as u32).unwrap_or(0));
    };
    (impls2code
        $ty:ty, // self type
        $rty:ty, // rhs type
        $s:ident, 
        $r:ident, // rhs identifier used in {wrap, panic, sat}_expr
        $t_op:ident,
        $wrap_op:ident, // wrap op fn
        $panic_op:ident, // panic op fn
        $sat_op:ident, // saturating op fn
        $t_assign:ident,
        $wrap_assign:ident, // wrap assign op fn
        $panic_assign:ident,
        $sat_assign:ident,
        $wrap_expr:expr, // implementation
        $panic_expr:expr,
        $sat_expr:expr
    ) => {
        impl $t_op<$rty> for $ty {
            type Output = $ty;
            #[inline(always)]
            fn $wrap_op($s, $r: $rty) -> Self::Output { $wrap_expr }
            #[inline(always)]
            fn $panic_op($s, $r: $rty) -> Self::Output { $panic_expr }
            #[inline(always)]
            fn $sat_op($s, $r: $rty) -> Self::Output { $sat_expr }
        }
                
        impl<'a> $t_op<$rty> for &'a $ty {
            type Output = <$ty as $t_op<$rty>>::Output;
            #[inline(always)]
            fn $wrap_op(self, r: $rty) -> Self::Output { (*self).$wrap_op(r) }
            #[inline(always)]
            fn $panic_op(self, r: $rty) -> Self::Output { (*self).$panic_op(r) }
            #[inline(always)]
            fn $sat_op(self, r: $rty) -> Self::Output { (*self).$sat_op(r) }
        }

        impl<'a> $t_op<&'a $rty> for $ty {
            type Output = <$ty as $t_op<$rty>>::Output;
            #[inline(always)]
            fn $wrap_op(self, r: &$rty) -> Self::Output { self.$wrap_op(*r) }
            #[inline(always)]
            fn $panic_op(self, r: &$rty) -> Self::Output { self.$panic_op(*r) }
            #[inline(always)]
            fn $sat_op(self, r: &$rty) -> Self::Output { self.$sat_op(*r) }
        }

        impl<'a> $t_op<&'a $rty> for &$ty {
            type Output = <$ty as $t_op<$rty>>::Output;
            #[inline(always)]
            fn $wrap_op(self, r: &$rty) -> Self::Output { (*self).$wrap_op(*r) }
            #[inline(always)]
            fn $panic_op(self, r: &$rty) -> Self::Output { (*self).$panic_op(*r) }
            #[inline(always)]
            fn $sat_op(self, r: &$rty) -> Self::Output { (*self).$sat_op(*r) }
        }

        impl $t_assign<$rty> for $ty {
            #[inline(always)]
            fn $wrap_assign(&mut self, r: $rty) { *self = self.$wrap_op(r); }
            #[inline(always)]
            fn $panic_assign(&mut self, r: $rty) { *self = self.$panic_op(r); }
            #[inline(always)]
            fn $sat_assign(&mut self, r: $rty) { *self = self.$sat_op(r); }
        }
    };
    (impls1ty $ty:ty) => { 
        op!(impls1code $ty, self, OverflowerNeg, neg_wrap, neg_panic, neg_saturate,
            self.wrapping_neg(), self.checked_neg().expect("arithmetic overflow"),
            (0 as Self).saturating_sub(self));
        op!(impls1code $ty, self, OverflowerAbs, abs_wrap, abs_panic, abs_saturate,
            self.wrapping_abs(), {
                if self == Self::min_value() {
                    panic!("arithmetic overflow");
                }
                self.wrapping_abs()
            }, if self > Self::min_value() {
                self.wrapping_abs()
            } else {
                Self::max_value()
            });
    };
    (impls1code $ty:ty, $s:ident, $t_op:ident, 
            $wrap_op:ident, $panic_op:ident, $sat_op:ident,
            $wrap_expr:expr, $panic_expr:expr, $sat_expr:expr) => {
        impl $t_op for $ty {
            type Output = Self;
            #[inline(always)]
            fn $wrap_op($s) -> Self { $wrap_expr }
            #[inline(always)]
            fn $panic_op($s) -> Self { $panic_expr }
            #[inline(always)]
            fn $sat_op($s) -> Self { $sat_expr }
        }
        
        impl<'a> $t_op for &'a $ty {
            type Output = <$ty as $t_op>::Output;
            #[inline(always)]
            fn $wrap_op(self) -> Self::Output { (*self).$wrap_op() }
            #[inline(always)]
            fn $panic_op(self) -> Self::Output { (*self).$panic_op() }
            #[inline(always)]
            fn $sat_op(self) -> Self::Output { (*self).$sat_op() }
        }
    };
}
