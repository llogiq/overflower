#![feature(plugin_registrar, quote, rustc_private)]

extern crate rustc_plugin;
extern crate syntax;

use std::fmt::{self, Display, Formatter};

use rustc_plugin::registry::Registry;
use syntax::codemap::{BytePos, Span, Spanned};
use syntax::ast::{BinOpKind, Block, Expr, ExprKind, Item, ItemKind, Lit,
                  LitKind, Mac, MetaItem, MetaItemKind, NestedMetaItemKind,
                  Path, PathSegment, Stmt, StmtKind, UnOp};
use syntax::ext::base::{Annotatable, ExtCtxt, SyntaxExtension};
use syntax::ext::build::AstBuilder;
use syntax::fold::{self, Folder};
use syntax::symbol::Symbol;
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
            let expanded = self.cx.expander().fold_item(item);
            expanded.into_iter()
                    .flat_map(|i| self.fold_item(i).into_iter())
                    .collect()
        } else {
            fold::noop_fold_item(item, self)
        }
    }

    fn fold_block(&mut self, block: P<Block>) -> P<Block> {
        if block.stmts.iter().any(is_stmt_macro) {
            let expanded = self.cx.expander().fold_block(block);
            fold::noop_fold_block(expanded, self)
        } else {
            fold::noop_fold_block(block, self)
        }
    }

    fn fold_expr(&mut self, expr: P<Expr>) -> P<Expr> {
        if self.mode == Mode::DontCare { return expr; }
        match expr.unwrap() {
            e@Expr { node: ExprKind::Mac(_), .. } => {
                let expanded = self.cx.expander().fold_expr(P(e));
                self.fold_expr(expanded)
            }
            Expr { id, node: ExprKind::Call(path, args), span, attrs } => {
                if args.len() == 1 {
                    let pspan = path.span;
                    if let ExprKind::Path(_, ref p) = path.node {
                        if is_abs(p) {
                            return tag_method(self, "abs", args, span, pspan);
                        }
                    }
                }
                P(fold::noop_fold_expr(Expr { id: id, node: ExprKind::Call(path, args),
                        span: span, attrs: attrs }, self))
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Add, span: op }, l, r), span, .. } => {
                tag_method(self, "add", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Sub, span: op }, l, r), span, .. } => {
                tag_method(self, "sub", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Mul, span: op }, l, r), span, .. } => {
                tag_method(self, "mul", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Div, span: op }, l, r), span, .. } => {
                tag_method(self, "div", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Rem, span: op }, l, r), span, .. } => {
                tag_method(self, "rem", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Shl, span: op }, l, r), span, .. } => {
                tag_method(self, "shl", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Binary( Spanned { node: BinOpKind::Shr, span: op }, l, r), span, .. } => {
                tag_method(self, "shr", vec![l, r], span, op)
            }
            Expr { node: ExprKind::Unary(UnOp::Neg, arg), span, .. } => {
                // yes, this span handling is ugly, but we don't have op spans on unary minus
                tag_method(self, "neg", vec![arg], span, Span { hi: span.lo + BytePos(1), ..span })
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Add, span: op }, l, r), span, .. } => {
                tag_method(self, "add_assign", vec![l, r], span, op)
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Sub, span: op }, l, r), span, .. } => {
                tag_method(self, "sub_assign", vec![l, r], span, op)
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Mul, span: op }, l, r), span, .. } => {
                tag_method(self, "mul_assign", vec![l, r], span, op)
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Div, span: op }, l, r), span, .. } => {
                tag_method(self, "div_assign", vec![l, r], span, op)
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Rem, span: op }, l, r), span, .. } => {
                tag_method(self, "rem_assign", vec![l, r], span, op)
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Shl, span: op }, l, r), span, .. } => {
                tag_method(self, "shl_assign", vec![l, r], span, op)
            }
            Expr { node: ExprKind::AssignOp( Spanned { node: BinOpKind::Shr, span: op }, l, r), span, .. } => {
                tag_method(self, "shr_assign", vec![l, r], span, op)
            }
            e => P(fold::noop_fold_expr(e, self)),
        }
    }

    fn fold_mac(&mut self, mac: Mac) -> Mac {
        mac
    }
}

fn tag_method(o: &mut Overflower, name: &str, args: Vec<P<Expr>>, outer: Span, op: Span) -> P<Expr> {
    let crate_name = o.cx.ident_of("overflower_support");
    let trait_name = o.cx.ident_of(&get_trait_name(o.mode, name));
    let fn_name = o.cx.ident_of(&format!("{}_{}", name, o.mode));
    let pspan = marked(o, op);
    let path = o.cx.path(pspan, vec![crate_name, trait_name, fn_name]);
    let epath = o.cx.expr_path(path);
    let args_expanded = o.fold_exprs(args);
    let span = marked(o, outer);
    o.cx.expr_call(span, epath, args_expanded)
}

fn marked(o: &mut Overflower, span: Span) -> Span {
    Span { expn_id: o.cx.backtrace(), ..span }
}

fn is_abs(p: &Path) -> bool {
    fn any_of(s: &PathSegment, options: &[&str]) -> bool {
        let name : &str = &*s.identifier.name.as_str();
        options.iter().any(|o| o == &name)
    }
    let segs = &p.segments;
    p.global && segs.len() == 3 && any_of(&segs[0], &["std", "core"]) &&
        any_of(&segs[1], &["u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64",
            "usize", "isize"]) && any_of(&segs[2], &["abs"])
}

fn parse_mode_str(w: &Symbol, span: Span)
        -> Result<Mode, (Span, &'static str)> {
    let w : &str = &*w.as_str();
    if w == "wrap" {
        Ok(Mode::Wrap)
    } else if w == "panic" {
        Ok(Mode::Panic)
    } else if w == "saturate" {
        Ok(Mode::Saturate)
    } else if w == "default" {
        Ok(Mode::DontCare)
    } else {
        Err((span, "Unknown overflow, expected wrap, panic or saturate"))
    }
}

fn parse_mode_lit(lit: &Lit, span: Span) -> Result<Mode, (Span, &'static str)> {
    if let LitKind::Str(ref i, _) = lit.node {
        parse_mode_str(i, span)
    } else {
        return Err((span, "overflow argument must be a string literal"))
    }
}

fn get_mode(mi: &MetaItem) -> Result<Mode, (Span, &'static str)> {
    match mi.node {
        MetaItemKind::NameValue(ref l) => {
            assert!(mi.name == "overflow");
            parse_mode_lit(l, mi.span)
        }
        MetaItemKind::List(ref list) => {
            assert!(mi.name == "overflow");
            if list.len() != 1 {
                return Err((mi.span, "Expected exactly one argument to `#[overflow(_)]`"))
            }
            match list[0].node {
                NestedMetaItemKind::Literal(ref l) => parse_mode_lit(l, mi.span),
                NestedMetaItemKind::MetaItem(ref i) => {
                    if let MetaItemKind::Word = i.node {
                        parse_mode_str(&i.name, mi.span)
                    } else {
                        Err((mi.span, "overflower does not do nested attributes"))
                    }
                }
            }
        }
        _ => Err((mi.span, "Expected an argument to `#[overflow(_)]`"))
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(Symbol::intern("overflow"),
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
