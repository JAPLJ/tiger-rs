// Abstract Syntax + Parser

use std::fmt;

use chumsky::{input::SpannedInput, prelude::*};
use lasso::{Rodeo, Spur};

use crate::{
    lex::{Span, Token},
    typing::Type,
};

pub type Symbol = Spur;
pub type Spanned<T> = (T, Span);

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Eq => "=",
            BinOp::Neq => "<>",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
        };
        write!(f, "{}", op)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    Simple(Symbol),
    Subscript(Box<Spanned<Self>>, Spanned<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(Box<Var>),
    Nil,
    Int(i64),
    Str(String),
    Call(Symbol, Vec<Spanned<Self>>),
    BinOp(Box<Spanned<Self>>, BinOp, Box<Spanned<Self>>),
    Seq(Vec<Spanned<Self>>),
    Assign(Box<Spanned<Var>>, Box<Spanned<Self>>),
    If(
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
        Option<Box<Spanned<Self>>>,
    ),
    While(Box<Spanned<Self>>, Box<Spanned<Self>>),
    For(
        Symbol,
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
    ),
    Break,
    Let(Vec<Spanned<Decl>>, Box<Spanned<Self>>),
    Array(
        // type, size, init
        Type,
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
    ),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Func(Vec<Spanned<Func>>),
    Var(
        // name, type, init
        Symbol,
        Option<Spanned<Type>>,
        Box<Spanned<Expr>>,
    ),
    Type(Vec<(Symbol, Spanned<Type>)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Func {
    pub id: Symbol,
    pub args: Vec<(Symbol, Type)>,
    pub result: Option<Type>,
    pub body: Spanned<Expr>,
}

pub type ParserInput<'src> = SpannedInput<Token<'src>, Span, &'src [(Token<'src>, Span)]>;

pub fn parser<'src>() -> impl Parser<
    'src,
    ParserInput<'src>,
    Spanned<Expr>,
    extra::Full<Rich<'src, Token<'src>, Span>, Rodeo, ()>,
> + Clone {
    recursive(|expr| {
        let ident = select! { Token::Ident(x) => x }.map_with(|x, e| {
            let r: &mut Rodeo = e.state();
            r.get_or_intern(x)
        });

        let decls = {
            let ty = just(&[Token::Array, Token::Of])
                .ignored()
                .or_not()
                .then(ident)
                .map(|(arr, t)| {
                    if arr.is_some() {
                        Type::Array(Box::new(Type::Name(t, None)))
                    } else {
                        Type::Name(t, None)
                    }
                });

            let tyfields = ident
                .then_ignore(just(Token::Ctrl(":")))
                .then(ident.map(|t| Type::Name(t, None)))
                .separated_by(just(Token::Ctrl(",")))
                .collect();

            let tydec = just(Token::Type)
                .ignore_then(ident)
                .then_ignore(just(Token::Op("=")))
                .then(ty.map_with(|t, e| (t, e.span())))
                .repeated()
                .at_least(1)
                .collect()
                .map_with(|ds, e| (Decl::Type(ds), e.span()))
                .boxed();

            let vardec = just(Token::Var)
                .ignore_then(ident)
                .then(
                    just(Token::Ctrl(":"))
                        .ignore_then(ident)
                        .map_with(|t, e| (Type::Name(t, None), e.span()))
                        .or_not(),
                )
                .then_ignore(just(Token::Ctrl(":=")))
                .then(expr.clone())
                .map_with(|((id, ty), init), e| (Decl::Var(id, ty, Box::new(init)), e.span()))
                .boxed();

            let fundec = just(Token::Function)
                .ignore_then(ident)
                .then(tyfields.delimited_by(just(Token::Ctrl("(")), just(Token::Ctrl(")"))))
                .then(
                    just(Token::Ctrl(":"))
                        .ignore_then(ident.map(|t| Type::Name(t, None)))
                        .or_not(),
                )
                .then_ignore(just(Token::Op("=")))
                .then(expr.clone())
                .map_with(|(((id, args), ty), body), e| {
                    (
                        Func {
                            id,
                            args,
                            result: ty,
                            body,
                        },
                        e.span(),
                    )
                })
                .repeated()
                .at_least(1)
                .collect()
                .map_with(|ds, e| (Decl::Func(ds), e.span()))
                .boxed();

            tydec
                .or(vardec)
                .or(fundec)
                .repeated()
                .collect::<Vec<_>>()
                .boxed()
        };

        let val = select! {
            Token::Nil => Expr::Nil,
            Token::Int(x) => Expr::Int(x),
            Token::Str(s) => Expr::Str(s),
        };

        let lvalue = ident
            .map_with(|x, e| (Var::Simple(x), e.span()))
            .foldl_with(
                expr.clone()
                    .delimited_by(just(Token::Ctrl("[")), just(Token::Ctrl("]")))
                    .repeated(),
                |lv: Spanned<Var>, e, _| {
                    let span = lv.1.union(e.1);
                    (Var::Subscript(Box::new(lv), e), span)
                },
            );

        let seq = expr
            .clone()
            .separated_by(just(Token::Ctrl(";")))
            .collect()
            .delimited_by(just(Token::Ctrl("{")), just(Token::Ctrl("}")))
            .map(|es| Expr::Seq(es));

        let assign = lvalue
            .clone()
            .then_ignore(just(Token::Ctrl(":=")))
            .then(expr.clone())
            .map(|(lv, expr)| Expr::Assign(Box::new(lv), Box::new(expr)));

        let array = ident
            .then(
                expr.clone()
                    .delimited_by(just(Token::Ctrl("[")), just(Token::Ctrl("]"))),
            )
            .then_ignore(just(Token::Of))
            .then(expr.clone())
            .map(|((ty, size), init)| {
                Expr::Array(Type::Name(ty, None), Box::new(size), Box::new(init))
            });

        let if_ = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Then))
            .then(expr.clone())
            .then(just(Token::Else).ignore_then(expr.clone()).or_not())
            .map(|((cond, then_e), else_e)| {
                Expr::If(Box::new(cond), Box::new(then_e), else_e.map(Box::new))
            });

        let while_ = just(Token::While)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Do))
            .then(expr.clone())
            .map(|(e1, e2)| Expr::While(Box::new(e1), Box::new(e2)));

        let for_ = just(Token::For)
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl(":=")))
            .then(expr.clone())
            .then_ignore(just(Token::To))
            .then(expr.clone())
            .then_ignore(just(Token::Do))
            .then(expr.clone())
            .map(|(((id, e1), e2), e3)| Expr::For(id, Box::new(e1), Box::new(e2), Box::new(e3)));

        let break_ = just(Token::Break).map(|_| Expr::Break);

        let let_ = just(Token::Let)
            .ignore_then(decls)
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .then_ignore(just(Token::End))
            .map(|(ds, e)| Expr::Let(ds, Box::new(e)));

        let atom = choice((
            val,
            assign,
            array,
            lvalue.map(|(lv, _)| Expr::Var(Box::new(lv))),
            if_,
            while_,
            for_,
            seq,
            break_,
            let_,
        ))
        .map_with(|expr, e| (expr, e.span()))
        .or(expr
            .clone()
            .delimited_by(just(Token::Ctrl("(")), just(Token::Ctrl(")"))))
        .boxed();

        let call = ident
            .then(
                expr.clone()
                    .separated_by(just(Token::Ctrl(",")))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::Ctrl("(")), just(Token::Ctrl(")"))),
            )
            .map_with(|(id, args), e| (Expr::Call(id, args), e.span()))
            .or(atom);

        let prod = {
            let op = just(Token::Op("*"))
                .to(BinOp::Mul)
                .or(just(Token::Op("/")).to(BinOp::Div));
            call.clone()
                .foldl_with(op.then(call).repeated(), |a, (op, b), e| {
                    (Expr::BinOp(Box::new(a), op, Box::new(b)), e.span())
                })
                .boxed()
        };

        let sum = {
            let op = just(Token::Op("+"))
                .to(BinOp::Add)
                .or(just(Token::Op("-")).to(BinOp::Sub));
            prod.clone()
                .foldl_with(op.then(prod).repeated(), |a, (op, b), e| {
                    (Expr::BinOp(Box::new(a), op, Box::new(b)), e.span())
                })
        };

        let cmp = {
            let op = choice((
                just(Token::Op("=")).to(BinOp::Eq),
                just(Token::Op("<>")).to(BinOp::Neq),
                just(Token::Op("<")).to(BinOp::Lt),
                just(Token::Op("<=")).to(BinOp::Le),
                just(Token::Op(">")).to(BinOp::Gt),
                just(Token::Op(">=")).to(BinOp::Ge),
            ));
            sum.clone()
                .foldl_with(op.then(sum).repeated(), |a, (op, b), e| {
                    (Expr::BinOp(Box::new(a), op, Box::new(b)), e.span())
                })
                .boxed()
        };

        let land = {
            let op = just(Token::Op("&"));
            cmp.clone()
                .foldl_with(op.ignore_then(cmp).repeated(), |a, b, e| {
                    (
                        Expr::If(
                            Box::new(a),
                            Box::new(b),
                            Some(Box::new((Expr::Int(0), e.span()))),
                        ),
                        e.span(),
                    )
                })
        };

        let lor = {
            let op = just(Token::Op("|"));
            land.clone()
                .foldl_with(op.ignore_then(land).repeated(), |a, b, e| {
                    (
                        Expr::If(
                            Box::new(a),
                            Box::new((Expr::Int(1), e.span())),
                            Some(Box::new(b)),
                        ),
                        e.span(),
                    )
                })
        };

        lor
    })
}

#[cfg(test)]
mod tests {
    use super::{BinOp, Decl, Expr, Var};
    use crate::parse;
    use crate::test_util::tokenize_ok;
    use assert_matches::assert_matches;
    use chumsky::prelude::*;

    #[test]
    fn parse_decls() {
        let toks = tokenize_ok(
            r#"
let
    type t1 = int
    type t2 = array of t1
    var x := 0
    var y: str := "s"
    function f(v: int): int = v
in
    x
end
        "#,
        );
        let (expr, symt, errs) = parse!(toks);
        assert!(errs.is_empty(), "{:?}", errs);
        let symt = symt.unwrap();
        assert_matches!(expr, Some((e, _)) => {
            assert_matches!(e, Expr::Let(decls, e) => {
                assert_matches!(decls.as_slice(), [
                    (Decl::Type(ts), _),
                    (Decl::Var(x, None, _), _),
                    (Decl::Var(y, Some(_), _), _),
                    (Decl::Func(fs), _),
                ] => {
                    assert_eq!(ts.len(), 2);
                    assert_eq!(Some(*x), symt.get("x"));
                    assert_eq!(Some(*y), symt.get("y"));
                    assert_eq!(fs.len(), 1);
                });
                assert_matches!(e.as_ref(), (Expr::Var(v), _) => {
                    assert_matches!(v.as_ref(), Var::Simple(_x))
                });
            });
        });
    }

    #[test]
    fn parse_binop() {
        let toks = tokenize_ok("a / b | c + d < e & f - g * h");
        let (expr, _, errs) = parse!(toks);
        assert!(errs.is_empty(), "{:?}", errs);
        assert_matches!(expr, Some((e, _)) => {
            assert_matches!(e, Expr::If(l, _, Some(r)) => {
                assert_matches!(l.as_ref(), (Expr::BinOp(_, BinOp::Div, _), _));
                assert_matches!(r.as_ref(), (Expr::If(l, r, Some(_)), _) => {
                    assert_matches!(l.as_ref(), (Expr::BinOp(l, BinOp::Lt, _), _) => {
                        assert_matches!(l.as_ref(), (Expr::BinOp(_, BinOp::Add, _), _));
                    });
                    assert_matches!(r.as_ref(), (Expr::BinOp(_, BinOp::Sub, r), _) => {
                        assert_matches!(r.as_ref(), (Expr::BinOp(_, BinOp::Mul, _), _));
                    });
                });
            });
        });
    }
}
