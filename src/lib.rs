#![feature(plugin_registrar, quote, rustc_private)]

extern crate rustc_plugin;
extern crate syntax;

use std::fmt::{self, Display, Formatter};

use rustc_plugin::registry::Registry;
use syntax::codemap::{DUMMY_SP, Span, Spanned};
use syntax::ast::{BinOpKind, Block, Expr, ExprKind, Item, ItemKind, Mac, 
                  MetaItem, MetaItemKind, Stmt, StmtKind, UnOp};
use syntax::ext::base::{Annotatable, ExtCtxt, SyntaxExtension};
use syntax::ext::build::AstBuilder;
use syntax::ext::expand::{expand_block, expand_expr, expand_item};
use syntax::fold::{self, Folder};
use syntax::parse::token;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;

#[derive(PartialEq, Eq, Clone, Copy)]
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

fn get_trait_name(mode: Mode, method: &str) -> String {
    let mut me = method.chars();
    let mo = match mode {
            Mode::Wrap => "Wrap",
            Mode::Panic => "Panic",
            Mode::Saturate => "Saturate",
            Mode::DontCare => "Default"
    };
    me.next().unwrap().to_uppercase().chain(me).chain(mo.chars()).collect()
}

struct Overflower<'a, 'cx: 'a> {
    mode: Mode,
    cx: &'a mut ExtCtxt<'cx>,
}

fn is_stmt_macro(stmt: &Stmt) -> bool {
    if let StmtKind::Mac(..) = stmt.node { true } else { false }
}

impl<'a, 'cx> Folder for Overflower<'a, 'cx> {
    fn fold_item(&mut self, item: P<Item>) -> SmallVector<P<Item>> {
        if let ItemKind::Mac(_) = item.node {
            let expanded = expand_item(item, &mut self.cx.expander());
            expanded.into_iter()
                    .flat_map(|i| self.fold_item(i).into_iter())
                    .collect()
        } else {
            fold::noop_fold_item(item, self)
        }
    }

    fn fold_block(&mut self, block: P<Block>) -> P<Block> {
        if block.stmts.iter().any(is_stmt_macro) {
            let expanded = expand_block(block, &mut self.cx.expander());
            fold::noop_fold_block(expanded, self)
        } else {
            fold::noop_fold_block(block, self)
        }
    }

    fn fold_expr(&mut self, expr: P<Expr>) -> P<Expr> {
        self.cx.span_warn(expr.span, &format!("fold {:?}", &expr));
        if self.mode == Mode::DontCare { return expr; }
        if let ExprKind::Mac(_) = expr.node {
            let expanded = expand_expr(expr.unwrap(), &mut self.cx.expander());
            return self.fold_expr(expanded);
        }
        match expr.unwrap() {
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Add, .. }, l, r), .. } => {
                tag_method(self, "add", vec![l, r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Sub, .. }, l, r), .. } => {
                tag_method(self, "sub", vec![l, r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Mul, .. }, l, r), .. } => {
                tag_method(self, "mul", vec![l, r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Div, .. }, l, r), .. } => {
                tag_method(self, "div", vec![l, r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Rem, .. }, l, r), .. } => {
                tag_method(self, "rem", vec![l, r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Shl, .. }, l, r), .. } => {
                tag_method(self, "shl", vec![l, r])
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Shr, .. }, l, r), .. } => {
                tag_method(self, "shr", vec![l, r])
            }
            Expr { node: ExprKind::Unary(UnOp::Neg, arg), .. } => {
                tag_method(self, "neg", vec![arg])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Add, .. }, l, r), .. } => {
                tag_method(self, "add_assign", vec![l, r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Sub, .. }, l, r), .. } => {
                tag_method(self, "sub_assign", vec![l, r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Mul, .. }, l, r), .. } => {
                tag_method(self, "mul_assign", vec![l, r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Div, .. }, l, r), .. } => {
                tag_method(self, "div_assign", vec![l, r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Rem, .. }, l, r), .. } => {
                tag_method(self, "rem_assign", vec![l, r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Shl, .. }, l, r), .. } => {
                tag_method(self, "shl_assign", vec![l, r])
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Shr, .. }, l, r), .. } => {
                tag_method(self, "shr_assign", vec![l, r])
            }
            e => P(fold::noop_fold_expr(e, self)),
        }
    }

    fn fold_mac(&mut self, mac: Mac) -> Mac {
        mac
    }
}

fn tag_method(o: &mut Overflower, name: &str, args: Vec<P<Expr>>) -> P<Expr> {
    let crate_name = o.cx.ident_of("overflower_support");
    let trait_name = o.cx.ident_of(&get_trait_name(o.mode, name));
    let fn_name = o.cx.ident_of(&format!("{}_{}", name, o.mode));
    let path = o.cx.path(DUMMY_SP, vec![crate_name, trait_name, fn_name]);
    let epath = o.cx.expr_path(path);
    let args_expanded = o.fold_exprs(args);
    o.cx.expr_call(DUMMY_SP, epath, args_expanded)
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
