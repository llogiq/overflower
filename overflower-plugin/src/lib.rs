#![feature(proc_macro_hygiene)]

extern crate proc_macro;
extern crate quote;
extern crate syn;

use self::proc_macro::TokenStream;
use quote::quote;
use syn::fold::{self, Fold};
use syn::parse::{Parse, ParseStream, Result};
use syn::*;

// This is a helper to allow us to parse attributes
struct OverflowerAttr(Vec<Attribute>);

impl Parse for OverflowerAttr {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(OverflowerAttr(input.call(Attribute::parse_outer)?))
    }
}

#[derive(Copy, Clone)]
enum Overflower {
    Wrap,
    Panic,
    Saturate,
    Default,
}

impl Parse for Overflower {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident = input.parse::<Ident>()?;
        if ident == "wrap" {
            Ok(Overflower::Wrap)
        } else if ident == "panic" {
            Ok(Overflower::Panic)
        } else if ident == "saturate" {
            Ok(Overflower::Saturate)
        } else if ident == "default" {
            Ok(Overflower::Default)
        } else {
            panic!("Usage: overflow(wrap|panic|saturate|default)");
        }
    }
}

fn ident(s: &'_ str) -> Ident {
    syn::parse_str(s).unwrap()
}

fn map_expr_box<F: FnOnce(Expr) -> Expr>(b: &mut Box<Expr>, f: F) {
    *(b.as_mut()) = f(std::mem::replace(
        b.as_mut(),
        Expr::Verbatim(Default::default()),
    ));
}

impl Overflower {
    fn tag(&self) -> &'static str {
        match *self {
            Overflower::Wrap => "wrap",
            Overflower::Panic => "panic",
            Overflower::Saturate => "saturate",
            Overflower::Default => "default",
        }
    }

    fn is_overflow(&self, attrs: &[Attribute]) -> bool {
        if let Overflower::Default = *self {
            return true;
        }
        attrs
            .iter()
            .any(|a| a.path.segments.iter().next().unwrap().ident == "overflow")
    }

    fn make_overflow_unop(&mut self, m: &str, arg: Box<Expr>) -> Expr {
        // #[overflow(wrap)] -a →
        // { let x = a; (&x).overflower_neg_tag().neg_wrap(x) }
        let x_ident = ident("__overflower_x__");
        let tag_fn: Ident = ident(&format!("overflower_{}_tag", m));
        let op_fn: Ident = ident(&format!("{}_{}", m, self.tag()));
        parse_quote!({
            use overflower::*;
            let #x_ident = #arg;
            (&#x_ident).#tag_fn().#op_fn(#x_ident)
        })
    }

    fn make_overflow_binop(&mut self, m: &str, left: Box<Expr>, right: Box<Expr>) -> Expr {
        // #[overflow(wrap)] a + b →
        // { let (x, y) = (a, b); (&x).overflower_add_tag(&y).add_wrap(x, y) }
        let x_ident = ident("__overflower_x__");
        let y_ident = ident("__overflower_y__");
        let tag_fn: Ident = ident(&format!("overflower_{}_tag", m));
        let op_fn: Ident = ident(&format!("{}_{}", m, self.tag()));
        parse_quote!({
            use overflower::*;
            let (#x_ident, #y_ident) = (#left, #right);
            (&(&#x_ident, &#y_ident)).#tag_fn(&#y_ident).#op_fn(#x_ident, #y_ident)
        })
    }

    fn make_overflow_assignop(&mut self, m: &str, left: Box<Expr>, right: Box<Expr>) -> Expr {
        // #[overflow(wrap)] a += b →
        // { let (x, y) = (&mut a, b); (&*x).overflower_add_assign_tag(&y).add_assign_wrap(x, y) }
        let x_ident = ident("__overflower_x__");
        let y_ident = ident("__overflower_y__");
        let tag_fn: Ident = ident(&format!("overflower_{}_tag", m));
        let op_fn: Ident = ident(&format!("{}_{}", m, self.tag()));
        parse_quote!({
            use overflower::*;
            let (#x_ident, #y_ident) = (&mut #left, #right);
            (&(&*#x_ident, &#y_ident)).#tag_fn(&#y_ident).#op_fn(#x_ident, #y_ident)
        })
    }

    fn make_unary(&mut self, u: ExprUnary) -> Expr {
        let mut u = u;
        if let syn::UnOp::Neg(_) = u.op {
            if let syn::Expr::Lit(_) = *u.expr {
                // we don't modify consts
            } else if !self.is_overflow(&u.attrs) {
                map_expr_box(&mut u.expr, |f| self.fold_expr(f));
                return self.make_overflow_unop("neg", u.expr);
            }
        }
        map_expr_box(&mut u.expr, |f| self.fold_expr(f));
        Expr::Unary(ExprUnary {
            op: u.op,
            attrs: u.attrs,
            expr: u.expr,
        })
    }

    fn make_assign_op(&mut self, a: ExprAssignOp) -> Expr {
        if self.is_overflow(&a.attrs) {
            return Expr::AssignOp(a);
        }
        let ExprAssignOp {
            attrs,
            mut left,
            op,
            mut right,
        } = a;
        map_expr_box(&mut left, |l| self.fold_expr(l));
        map_expr_box(&mut right, |r| self.fold_expr(r));
        match op {
            syn::BinOp::AddEq(_) => self.make_overflow_assignop("add_assign", left, right),
            syn::BinOp::SubEq(_) => self.make_overflow_assignop("sub_assign", left, right),
            syn::BinOp::MulEq(_) => self.make_overflow_assignop("mul_assign", left, right),
            syn::BinOp::DivEq(_) => self.make_overflow_assignop("div_assign", left, right),
            syn::BinOp::RemEq(_) => self.make_overflow_assignop("rem_assign", left, right),
            syn::BinOp::ShlEq(_) => self.make_overflow_assignop("shl_assign", left, right),
            syn::BinOp::ShrEq(_) => self.make_overflow_assignop("shr_assign", left, right),
            op => Expr::AssignOp(ExprAssignOp {
                attrs,
                left,
                op,
                right,
            }),
        }
    }

    fn make_binary(&mut self, b: ExprBinary) -> Expr {
        if self.is_overflow(&b.attrs) {
            return Expr::Binary(b);
        }
        let ExprBinary {
            attrs,
            mut left,
            op,
            mut right,
        } = b;
        map_expr_box(&mut left, |e| self.fold_expr(e));
        map_expr_box(&mut right, |e| self.fold_expr(e));
        match op {
            syn::BinOp::Add(_) => self.make_overflow_binop("add", left, right),
            syn::BinOp::Sub(_) => self.make_overflow_binop("sub", left, right),
            syn::BinOp::Mul(_) => self.make_overflow_binop("mul", left, right),
            syn::BinOp::Div(_) => self.make_overflow_binop("div", left, right),
            syn::BinOp::Rem(_) => self.make_overflow_binop("rem", left, right),
            syn::BinOp::Shl(_) => self.make_overflow_binop("shl", left, right),
            syn::BinOp::Shr(_) => self.make_overflow_binop("shr", left, right),
            op => Expr::Binary(ExprBinary {
                attrs,
                left,
                op,
                right,
            }),
        }
    }

    fn make_call(&mut self, mut c: ExprCall) -> Expr {
        if self.is_overflow(&c.attrs) {
            return Expr::Call(c);
        }
        let is_abs = if let syn::Expr::Path(ref p) = *c.func {
            let segments = &p.path.segments;
            static FACADE: [&str; 2] = ["std", "core"];
            static TYPES: [&str; 6] = ["i8", "i16", "i32", "i64", "i128", "isize"];
            static FUNCTION: [&str; 1] = ["abs"];
            static ABS_MATCHERS: [&[&str]; 3] = [&FACADE, &TYPES, &FUNCTION];

            segments
                .iter()
                .zip(&ABS_MATCHERS[3 - segments.len()..])
                .all(|(seg, m)| seg.arguments.is_empty() && m.iter().any(|s| seg.ident == s))
        } else {
            false
        };
        if is_abs {
            let func = match *self {
                Overflower::Wrap => "OverflowerAbs::abs_wrap",
                Overflower::Panic => "OverflowerAbs::abs_panic",
                Overflower::Saturate => "OverflowerAbs::abs_saturate",
                Overflower::Default => return Expr::Call(c),
            };
            map_expr_box(&mut c.func, |_| syn::parse_str::<Expr>(func).unwrap());
        }
        Expr::Call(c)
    }

    fn make_macro(&mut self, m: ExprMacro) -> Expr {
        if self.is_overflow(&m.attrs) {
            return Expr::Macro(m);
        }
        let mut m = m;
        m.attrs.extend(
            syn::parse_str::<OverflowerAttr>(match *self {
                Overflower::Wrap => "#[overflow(wrap)]",
                Overflower::Panic => "#[overflow(panic)]",
                Overflower::Saturate => "#[overflow(saturate)]",
                Overflower::Default => "#[overflow(default)]",
            })
            .unwrap()
            .0,
        );
        Expr::Macro(m)
    }
}

impl Fold for Overflower {
    fn fold_impl_item_method(&mut self, i: ImplItemMethod) -> ImplItemMethod {
        if self.is_overflow(&i.attrs) {
            return i;
        }
        fold::fold_impl_item_method(self, i)
    }

    fn fold_item_fn(&mut self, i: ItemFn) -> ItemFn {
        if self.is_overflow(&i.attrs) {
            return i;
        }
        fold::fold_item_fn(self, i)
    }

    fn fold_item_impl(&mut self, i: ItemImpl) -> ItemImpl {
        if self.is_overflow(&i.attrs) {
            return i;
        }
        fold::fold_item_impl(self, i)
    }

    fn fold_item_mod(&mut self, i: ItemMod) -> ItemMod {
        if self.is_overflow(&i.attrs) {
            return i;
        }
        fold::fold_item_mod(self, i)
    }

    fn fold_item_trait(&mut self, i: ItemTrait) -> ItemTrait {
        if self.is_overflow(&i.attrs) {
            return i;
        }
        fold::fold_item_trait(self, i)
    }

    fn fold_trait_item_method(&mut self, i: TraitItemMethod) -> TraitItemMethod {
        if self.is_overflow(&i.attrs) {
            return i;
        }
        fold::fold_trait_item_method(self, i)
    }

    fn fold_expr(&mut self, e: Expr) -> Expr {
        macro_rules! foldexpr {
            ($s:expr, $ty:path, $t:ident, $f:path) => {
                $ty(if self.is_overflow(&$t.attrs) {
                    $t
                } else {
                    $f($s, $t)
                })
            };
        }
        match e {
            Expr::Box(b) => foldexpr!(self, Expr::Box, b, fold::fold_expr_box),
            Expr::Array(a) => foldexpr!(self, Expr::Array, a, fold::fold_expr_array),
            Expr::Call(c) => self.make_call(c),
            Expr::MethodCall(c) => {
                foldexpr!(self, Expr::MethodCall, c, fold::fold_expr_method_call)
            }
            Expr::Tuple(t) => foldexpr!(self, Expr::Tuple, t, fold::fold_expr_tuple),
            Expr::Binary(b) => self.make_binary(b),
            Expr::Unary(u) => self.make_unary(u),
            Expr::Cast(c) => foldexpr!(self, Expr::Cast, c, fold::fold_expr_cast),
            Expr::Type(t) => foldexpr!(self, Expr::Type, t, fold::fold_expr_type),
            Expr::Let(l) => foldexpr!(self, Expr::Let, l, fold::fold_expr_let),
            Expr::If(i) => foldexpr!(self, Expr::If, i, fold::fold_expr_if),
            Expr::While(w) => foldexpr!(self, Expr::While, w, fold::fold_expr_while),
            Expr::ForLoop(f) => foldexpr!(self, Expr::ForLoop, f, fold::fold_expr_for_loop),
            Expr::Loop(l) => foldexpr!(self, Expr::Loop, l, fold::fold_expr_loop),
            Expr::Match(m) => foldexpr!(self, Expr::Match, m, fold::fold_expr_match),
            Expr::Closure(c) => foldexpr!(self, Expr::Closure, c, fold::fold_expr_closure),
            Expr::Unsafe(u) => foldexpr!(self, Expr::Unsafe, u, fold::fold_expr_unsafe),
            Expr::Block(b) => foldexpr!(self, Expr::Block, b, fold::fold_expr_block),
            Expr::Assign(a) => foldexpr!(self, Expr::Assign, a, fold::fold_expr_assign),
            Expr::AssignOp(o) => self.make_assign_op(o),
            Expr::Field(f) => foldexpr!(self, Expr::Field, f, fold::fold_expr_field),
            Expr::Index(i) => foldexpr!(self, Expr::Index, i, fold::fold_expr_index),
            Expr::Range(r) => foldexpr!(self, Expr::Range, r, fold::fold_expr_range),
            Expr::Path(p) => foldexpr!(self, Expr::Path, p, fold::fold_expr_path),
            Expr::Reference(r) => foldexpr!(self, Expr::Reference, r, fold::fold_expr_reference),
            Expr::Break(b) => foldexpr!(self, Expr::Break, b, fold::fold_expr_break),
            Expr::Return(r) => foldexpr!(self, Expr::Return, r, fold::fold_expr_return),
            Expr::Macro(m) => self.make_macro(m),
            Expr::Struct(s) => foldexpr!(self, Expr::Struct, s, fold::fold_expr_struct),
            Expr::Repeat(r) => foldexpr!(self, Expr::Repeat, r, fold::fold_expr_repeat),
            Expr::Paren(p) => foldexpr!(self, Expr::Paren, p, fold::fold_expr_paren),
            Expr::Try(t) => foldexpr!(self, Expr::Try, t, fold::fold_expr_try),
            Expr::Async(a) => foldexpr!(self, Expr::Async, a, fold::fold_expr_async),
            Expr::TryBlock(t) => foldexpr!(self, Expr::TryBlock, t, fold::fold_expr_try_block),
            Expr::Yield(y) => foldexpr!(self, Expr::Yield, y, fold::fold_expr_yield),
            x => x,
        }
    }
}

/// Mark a module or function to control overflow behavior within
///
/// This takes one argument, which may be one of (`wrap`, `panic`, `saturate`
/// or `default`. This changes all arithmetic and shift operations:
///
/// * `wrap` makes all operations wrapping (silently ignoring overflow)
/// * `panic` panics on overflow
/// * `saturate` makes all operations saturating
/// * `default` restores default behavior (which can be useful to carve out
/// items from a larger scope with defined overflow behavior)
///
/// By default, overflow will panic in debug mode and wrap in release mode.
/// The macro has no type detection, so it cannot dispatch `abs` calls
/// automatically. You must call the method using unified function call syntax
/// specifying the actual type so overflower can pick it up.
///
/// # Panics
///
/// If you declare `#[overflow(panic)]`, arithmetic operations and shift will
/// panic on overflow.
///
/// # Examples
///
/// ```ignore
/// use overflower::overflow;
///
/// #[overflow(saturate)]
/// fn saturated() {
///     assert_eq!(23768, i16::abs(-32768));
/// }
///
/// #[overflow(wrap)]
/// fn main() {
///     assert_eq!(254_u8, 255 + 255);
///     saturated();
/// }
/// ```
#[proc_macro_attribute]
pub fn overflow(attrs: TokenStream, code: TokenStream) -> TokenStream {
    let input = parse_macro_input!(code as Item);
    let mut overflow = parse_macro_input!(attrs as Overflower);
    let item = fold::fold_item(&mut overflow, input);
    TokenStream::from(quote!(#item))
}
