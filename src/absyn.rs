use chumsky::{input::SpannedInput, prelude::*};

use crate::lex::{Span, Token};

pub type Spanned<T> = (T, Span);

#[derive(Debug, Clone, PartialEq)]
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
    LAnd,
    LOr,
}

#[derive(Debug, PartialEq)]
pub enum Var<'src> {
    Simple(&'src str),
    Subscript(Box<Self>, Spanned<Expr<'src>>),
}

#[derive(Debug, PartialEq)]
pub enum Expr<'src> {
    Var(Box<Var<'src>>),
    Nil,
    Int(i64),
    Str(String),
    Call(&'src str, Vec<Spanned<Self>>),
    BinOp(Box<Spanned<Self>>, BinOp, Box<Spanned<Self>>),
    Seq(Vec<Spanned<Self>>),
    Assign(Box<Spanned<Var<'src>>>, Box<Spanned<Self>>),
    If(
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
        Option<Box<Spanned<Self>>>,
    ),
    While(Box<Spanned<Self>>, Box<Spanned<Self>>),
    For(
        &'src str,
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
    ),
    Break,
    Let(Vec<Decl<'src>>, Box<Spanned<Self>>),
    Array(
        // type, size, init
        &'src str,
        Box<Spanned<Self>>,
        Box<Spanned<Self>>,
    ),
}

#[derive(Debug, PartialEq)]
pub enum Decl<'src> {
    Func(Vec<Spanned<Func<'src>>>),
    Var(
        // name, type, init
        &'src str,
        Option<Spanned<&'src str>>,
        Box<Spanned<Expr<'src>>>,
    ),
    Type(Vec<(&'src str, Spanned<Type<'src>>)>),
}

#[derive(Debug, PartialEq)]
pub enum Type<'src> {
    Name(&'src str),
    Array(&'src str),
}

#[derive(Debug, PartialEq)]
pub struct Func<'src> {
    pub name: &'src str,
    pub args: Vec<(&'src str, &'src str)>,
    pub result: Option<&'src str>,
    pub body: Spanned<Expr<'src>>,
}

pub type ParserInput<'toks, 'src> = SpannedInput<Token<'src>, Span, &'toks [(Token<'src>, Span)]>;

pub fn parser<'toks, 'src: 'toks>() -> impl Parser<
    'toks,
    ParserInput<'toks, 'src>,
    Spanned<Expr<'src>>,
    extra::Err<Rich<'toks, Token<'src>, Span>>,
> + Clone {
    recursive(|expr| {
        let ident = select! { Token::Ident(x) => x };

        let decls = {
            let ty = just(&[Token::Array, Token::Of])
                .ignored()
                .or_not()
                .then(ident)
                .map(|(arr, t)| {
                    if arr.is_some() {
                        Type::Array(t)
                    } else {
                        Type::Name(t)
                    }
                });

            let tyfields = ident
                .then_ignore(just(Token::Ctrl(":")))
                .then(ident)
                .separated_by(just(Token::Ctrl(",")))
                .collect();

            let tydec = just(Token::Type)
                .ignore_then(ident)
                .then_ignore(just(Token::Op("=")))
                .then(ty.map_with(|t, e| (t, e.span())))
                .repeated()
                .at_least(1)
                .collect()
                .map(Decl::Type)
                .boxed();

            let vardec = just(Token::Var)
                .ignore_then(ident)
                .then(
                    just(Token::Ctrl(":"))
                        .ignore_then(ident)
                        .map_with(|t, e| (t, e.span()))
                        .or_not(),
                )
                .then_ignore(just(Token::Ctrl(":=")))
                .then(expr.clone())
                .map(|((id, ty), init)| Decl::Var(id, ty, Box::new(init)))
                .boxed();

            let fundec = just(Token::Function)
                .ignore_then(ident)
                .then(tyfields.delimited_by(just(Token::Ctrl("(")), just(Token::Ctrl(")"))))
                .then(just(Token::Ctrl(":")).ignore_then(ident).or_not())
                .then_ignore(just(Token::Op("=")))
                .then(expr.clone())
                .map_with(|(((id, args), ty), body), e| {
                    (
                        Func {
                            name: id,
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
                .map(Decl::Func)
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

        let lvalue = ident.map(Var::Simple).foldl_with(
            expr.clone()
                .delimited_by(just(Token::Ctrl("[")), just(Token::Ctrl("]")))
                .repeated(),
            |lv, e, _| Var::Subscript(Box::new(lv), e),
        );

        let seq = expr
            .clone()
            .separated_by(just(Token::Ctrl(";")))
            .collect()
            .delimited_by(just(Token::Ctrl("{")), just(Token::Ctrl("}")))
            .map(|es| Expr::Seq(es));

        let assign = lvalue
            .clone()
            .map_with(|lv, e| (lv, e.span()))
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
            .map(|((ty, size), init)| Expr::Array(ty, Box::new(size), Box::new(init)));

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
            lvalue.map(|lv| Expr::Var(Box::new(lv))),
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
            let op = just(Token::Op("&")).to(BinOp::LAnd);
            cmp.clone()
                .foldl_with(op.then(cmp).repeated(), |a, (op, b), e| {
                    (Expr::BinOp(Box::new(a), op, Box::new(b)), e.span())
                })
        };

        let lor = {
            let op = just(Token::Op("|")).to(BinOp::LOr);
            land.clone()
                .foldl_with(op.then(land).repeated(), |a, (op, b), e| {
                    (Expr::BinOp(Box::new(a), op, Box::new(b)), e.span())
                })
        };

        lor
    })
}
