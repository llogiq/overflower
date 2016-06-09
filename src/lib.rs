#![feature(plugin_registrar, quote, rustc_private)]

extern crate rustc_plugin;
extern crate syntax;

use std::fmt::{self, Display, Formatter};

use rustc_plugin::registry::Registry; 
use syntax::codemap::{DUMMY_SP, Span, Spanned};
use syntax::ast::{BinOpKind, Expr, ExprKind, Item, Mac, MetaItem, MetaItemKind, UnOp};
use syntax::ext::base::{Annotatable, ExtCtxt, SyntaxExtension};
use syntax::ext::build::AstBuilder;
use syntax::ext::expand::expand_expr;
use syntax::fold::{self, Folder};
use syntax::parse::token;
use syntax::ptr::P;

#[derive(PartialEq, Eq)]
enum Mode {
    Wrap,
    Panic,
    Saturate,
    DontCare
}

impl Display for Mode {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        fmt.write_str(match *self {
            Mode::Wrap => "wrap",
            Mode::Panic => "panic",
            Mode::Saturate => "saturate",
            Mode::DontCare => "default"
        })
    }
}

struct Overflower<'a, 'cx: 'a> {
    mode: Mode,
    cx: &'a mut ExtCtxt<'cx>,
}

impl<'a, 'cx> Folder for Overflower<'a, 'cx> {
    fn fold_expr(&mut self, expr: P<Expr>) -> P<Expr> {
        if self.mode == Mode::DontCare { return expr; }
        if let ExprKind::Mac(_) = expr.node {
            let expanded = expand_expr(expr.unwrap(), &mut self.cx.expander());
            return self.fold_expr(expanded);
        }
        match expr.unwrap() {
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Add, .. }, l, r), .. } => {
                tag_method(self, "add", l, vec![r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Sub, .. }, l, r), .. } => {
                tag_method(self, "sub", l, vec![r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Mul, .. }, l, r), .. } => {
                tag_method(self, "mul", l, vec![r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Div, .. }, l, r), .. } => {
                tag_method(self, "div", l, vec![r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Rem, .. }, l, r), .. } => {
                tag_method(self, "rem", l, vec![r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Shl, .. }, l, r), .. } => {
                tag_method(self, "shl", l, vec![r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Shr, .. }, l, r), .. } => {
                tag_method(self, "shr", l, vec![r])
            }
            Expr { node: ExprKind::Unary(UnOp::Neg, arg), .. } => {
                tag_method(self, "neg", arg, vec![])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Add, .. }, l, r), .. } => {
                tag_method(self, "add_assign", l, vec![r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Sub, .. }, l, r), .. } => {
                tag_method(self, "sub_assign", l, vec![r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Mul, .. }, l, r), .. } => {
                tag_method(self, "mul_assign", l, vec![r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Div, .. }, l, r), .. } => {
                tag_method(self, "div_assign", l, vec![r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Rem, .. }, l, r), .. } => {
                tag_method(self, "rem_assign", l, vec![r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Shl, .. }, l, r), .. } => {
                tag_method(self, "shl_assign", l, vec![r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Shr, .. }, l, r), .. } => {
                tag_method(self, "shr_assign", l, vec![r])
            }
            e => P(fold::noop_fold_expr(e, self)),
        }
    }
    
    fn fold_mac(&mut self, mac: Mac) -> Mac {
        fold::noop_fold_mac(mac, self)
    }    
}

fn tag_method(o: &mut Overflower, name: &str, receiver: P<Expr>, args: Vec<P<Expr>>) -> P<Expr> {
    let rec = receiver.map(|r| fold::noop_fold_expr(r, o));
    let fn_name = o.cx.ident_of(&format!("{}_{}", name, o.mode));
    let args_expanded = args.into_iter().map(|a| a.map(|e| fold::noop_fold_expr(e, o))).collect();
    o.cx.expr_method_call(DUMMY_SP, rec, fn_name, args_expanded)
}

fn get_mode(mi: &MetaItem) -> Result<Mode, (Span, &'static str)> {
    if let MetaItemKind::List(ref s, ref l) = mi.node {
        assert!(s == "overflow");
        if l.len() != 1 {
            Err((mi.span, "Expected exactly one argument to `#[overflow(_)]`"))
        } else {
            if let MetaItemKind::Word(ref w) = l[0].node {
                if w == "wrap" {
                    Ok(Mode::Wrap)
                } else if w == "panic" {
                    Ok(Mode::Panic)
                } else if w == "saturate" {
                    Ok(Mode::Saturate)
                } else if w == "default" {
                    Ok(Mode::DontCare)
                } else {
                    Err((l[0].span, "Unknown overflow, expected wrap, panic or saturate"))
                }
            } else {
                Err((mi.span, "Expected a word argument to `#[overflow(_)]`"))
            }
        }
    } else {
        Err((mi.span, "Expected an argument to `#[overflow(_)]`"))
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(token::intern("overflow"),
        SyntaxExtension::MultiModifier(Box::new(|cx: &mut ExtCtxt, _span: Span, mi: &MetaItem,
              a: Annotatable| {
        let mode = get_mode(mi).unwrap_or_else(|(espan, e)| {
            cx.span_err(espan, e);
            Mode::DontCare
        });
        let mut o = &mut Overflower {
            mode: mode,
            cx: cx,
        };
        match a {
            Annotatable::Item(i) => Annotatable::Item(
                o.fold_item(i).expect_one("expected exactly one item")),
            Annotatable::TraitItem(i) => Annotatable::TraitItem(
                i.map(|i| o.fold_trait_item(i).expect_one("expected exactly one item"))),
            Annotatable::ImplItem(i) => Annotatable::ImplItem(
                i.map(|i| o.fold_impl_item(i).expect_one("expected exactly one item"))),
        }
    })));
}
