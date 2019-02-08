extern crate proc_macro;
extern crate syn;
extern crate quote;

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

impl Overflower {
    fn is_overflow(&self, attrs: &[Attribute]) -> bool {
        if let Overflower::Default = *self { return true; }
        attrs.iter().any(|a| a.path.segments.iter()
                .next().unwrap().ident == "overflow")
    }

    fn method_path(&self, method: &str) -> syn::Path {
        let mo = match *self {
            Overflower::Wrap => "Wrap",
            Overflower::Panic => "Panic",
            Overflower::Saturate => "Saturate",
            Overflower::Default => "Default"
        };
        let crate_name = syn::parse_str::<Ident>("overflower_support").unwrap();
        let trait_name = syn::parse_str::<Ident>(&(method.split("_").flat_map(|s| {
            let mut me = s.chars();
            me.next().unwrap().to_uppercase().chain(me)
        }).collect::<String>() + mo)).unwrap();
        let method_name = syn::parse_str::<Ident>(&format!("{}_{}",
            method, &mo.to_lowercase())).unwrap();
        parse_quote!(#crate_name :: #trait_name :: #method_name)
    }

    fn make_method(&self, m: &str, args: Vec<Expr>) -> Expr {
        let method_path = Expr::Path(syn::ExprPath {
            attrs: vec![],
            qself: None,
            path: self.method_path(m)
        });
        parse_quote!(#method_path ( #(#args),* ))
    }

    fn make_unary(&mut self, u: ExprUnary) -> Expr {
        if let syn::UnOp::Neg(_) = u.op {
            Expr::Unary(u)
        } else if self.is_overflow(&u.attrs) {
            Expr::Unary(u)
        } else {
            self.make_method("neg", vec![*u.expr])
        }
    }

    fn make_assign_op(&mut self, a: ExprAssignOp) -> Expr {
        if self.is_overflow(&a.attrs) {
            return Expr::AssignOp(a);
        }
        let ExprAssignOp {
            attrs,
            left,
            op,
            right,
        } = a;
        let mut args = vec![Expr::Reference(ExprReference {
                attrs: vec![],
                and_token: Default::default(),
                mutability: Some(Default::default()),
                expr: Box::new(self.fold_expr(*left))
            }), self.fold_expr(*right)];
        match op {
            syn::BinOp::AddEq(_) => self.make_method("add_assign", args),
            syn::BinOp::SubEq(_) => self.make_method("sub_assign", args),
            syn::BinOp::MulEq(_) => self.make_method("mul_assign", args),
            syn::BinOp::DivEq(_) => self.make_method("div_assign", args),
            syn::BinOp::RemEq(_) => self.make_method("rem_assign", args),
            syn::BinOp::ShlEq(_) => self.make_method("shl_assign", args),
            syn::BinOp::ShrEq(_) => self.make_method("shr_assign", args),
            op => {
                let (r, l) = (args.pop().unwrap(), args.pop().unwrap());
                let e = if let Expr::Reference(ExprReference { expr, .. }) = l {
                    expr
                } else {
                    unreachable!();
                };
                Expr::AssignOp(ExprAssignOp {
                    attrs,
                    left: e,
                    op,
                    right: Box::new(r),
                })
            }
        }

    }

    fn make_binary(&mut self, b: ExprBinary) -> Expr {
        if self.is_overflow(&b.attrs) {
            return Expr::Binary(b);
        }
        let ExprBinary {
            attrs,
            left,
            op,
            right,
        } = b;
        let mut args = vec![self.fold_expr(*left), self.fold_expr(*right)];
        match op {
            syn::BinOp::Add(_) => self.make_method("add", args),
            syn::BinOp::Sub(_) => self.make_method("sub", args),
            syn::BinOp::Mul(_) => self.make_method("mul", args),
            syn::BinOp::Div(_) => self.make_method("div", args),
            syn::BinOp::Rem(_) => self.make_method("rem", args),
            syn::BinOp::Shl(_) => self.make_method("shl", args),
            syn::BinOp::Shr(_) => self.make_method("shr", args),
            op => {
                let (r, l) = (args.pop().unwrap(), args.pop().unwrap());
                Expr::Binary(ExprBinary {
                    attrs,
                    left: Box::new(l),
                    op,
                    right: Box::new(r),
                })
            }
        }
    }

    fn make_call(&mut self, mut c: ExprCall) -> Expr {
        if self.is_overflow(&c.attrs) {
            return Expr::Call(c);
        }
        let is_abs = if let syn::Expr::Path(ref p) = *c.func {
            let segments = &p.path.segments;
            static FACADE : [&str; 2] = ["std", "core"];
            static TYPES : [&str; 6] = ["i8", "i16", "i32", "i64", "i128",
                "isize"];
            static FUNCTION : [&str; 1] = ["abs"];
            static ABS_MATCHERS : [&[&str]; 3] = [&FACADE, &TYPES, &FUNCTION];

            if segments.iter().zip(&ABS_MATCHERS[3 - segments.len()..]).all(
                |(seg, m)| seg.arguments.is_empty() && m.iter().any(
                    |s| seg.ident == s)) {
                true
            } else {
                false
            }
        } else {
            false
        };
        if is_abs {
            let func = match *self {
                Overflower::Wrap => "::overflower_support::AbsWrap::abs_wrap",
                Overflower::Panic => "::overflower_support::AbsPanic::abs_panic",
                Overflower::Saturate => "::overflower_support::AbsSaturate::abs_saturate",
                Overflower::Default => return Expr::Call(c),
            };
            c.func = Box::new(syn::parse_str::<Expr>(func).unwrap());
        }
        Expr::Call(c)
    }

    fn make_macro(&mut self, m: ExprMacro) -> Expr {
        if self.is_overflow(&m.attrs) {
            return Expr::Macro(m);
        }
        let mut m = m;
        m.attrs.extend(syn::parse_str::<OverflowerAttr>(match *self {
            Overflower::Wrap => "#[overflow(wrap)]",
            Overflower::Panic => "#[overflow(panic)]",
            Overflower::Saturate => "#[overflow(saturate)]",
            Overflower::Default => "#[overflow(default)]"
        }).unwrap().0);
        Expr::Macro(m)
    }
}

impl Fold for Overflower {
    fn fold_impl_item_method(&mut self, i: ImplItemMethod) -> ImplItemMethod {
        if self.is_overflow(&i.attrs) { return i; }
        fold::fold_impl_item_method(self, i)
    }

    fn fold_item_fn(&mut self, i: ItemFn) -> ItemFn {
        if self.is_overflow(&i.attrs) { return i; }
        fold::fold_item_fn(self, i)
    }

    fn fold_item_impl(&mut self, i: ItemImpl) -> ItemImpl {
        if self.is_overflow(&i.attrs) { return i; }
        fold::fold_item_impl(self, i)
    }

    fn fold_item_mod(&mut self, i: ItemMod) -> ItemMod {
        if self.is_overflow(&i.attrs) { return i; }
        fold::fold_item_mod(self, i)
    }

    fn fold_item_trait(&mut self, i: ItemTrait) -> ItemTrait {
        if self.is_overflow(&i.attrs) { return i; }
        fold::fold_item_trait(self, i)
    }

    fn fold_trait_item_method(&mut self, i: TraitItemMethod) -> TraitItemMethod {
        if self.is_overflow(&i.attrs) { return i; }
        fold::fold_trait_item_method(self, i)
    }

    fn fold_expr(&mut self, e: Expr) -> Expr {
        macro_rules! foldexpr {
            ($s:expr, $ty:path, $t:ident, $f:path) => {
                $ty(if self.is_overflow(& $t . attrs) {
                    $t
                } else {
                    $f($s, $t)
                })
            }
        }
        match e {
            Expr::Box(b) => foldexpr!(self, Expr::Box, b, fold::fold_expr_box),
            Expr::InPlace(i) => foldexpr!(self, Expr::InPlace, i, fold::fold_expr_in_place),
            Expr::Array(a) => foldexpr!(self, Expr::Array, a, fold::fold_expr_array),
            Expr::Call(c) => self.make_call(c),
            Expr::MethodCall(c) => foldexpr!(self, Expr::MethodCall, c, fold::fold_expr_method_call),
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

#[proc_macro_attribute]
pub fn overflow(attrs: TokenStream, code: TokenStream) -> TokenStream {
    let input = parse_macro_input!(code as Item);
    let mut overflow = parse_macro_input!(attrs as Overflower);
    let item = fold::fold_item(&mut overflow, input);
    TokenStream::from(quote!(#item))
}
