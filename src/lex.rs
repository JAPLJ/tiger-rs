// Lexer

use std::fmt;

use chumsky::prelude::*;

pub type Span = SimpleSpan<usize>;

#[derive(Clone, Debug, PartialEq)]
pub enum Token<'src> {
    Nil,
    Int(i64),
    Str(String), // escape sequences
    Op(&'src str),
    Ctrl(&'src str),
    Ident(&'src str),
    Type,
    Array,
    Of,
    Var,
    Function,
    Let,
    In,
    End,
    If,
    Then,
    Else,
    While,
    Do,
    For,
    To,
    Break,
}

impl<'src> fmt::Display for Token<'src> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Nil => write!(f, "nil"),
            Token::Int(x) => write!(f, "{}", x),
            Token::Str(x) => write!(f, "{}", x),
            Token::Op(x) => write!(f, "{}", x),
            Token::Ctrl(x) => write!(f, "{}", x),
            Token::Ident(x) => write!(f, "{}", x),
            Token::Type => write!(f, "type"),
            Token::Array => write!(f, "array"),
            Token::Of => write!(f, "of"),
            Token::Var => write!(f, "var"),
            Token::Function => write!(f, "function"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::End => write!(f, "end"),
            Token::If => write!(f, "if"),
            Token::Then => write!(f, "then"),
            Token::Else => write!(f, "else"),
            Token::While => write!(f, "while"),
            Token::Do => write!(f, "do"),
            Token::For => write!(f, "for"),
            Token::To => write!(f, "to"),
            Token::Break => write!(f, "break"),
        }
    }
}

pub fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<(Token<'src>, Span)>, extra::Err<Rich<'src, char, Span>>> {
    let int = just('-')
        .or_not()
        .then(text::int(10).from_str::<i64>())
        .map(|(neg, v)| {
            let v = v.unwrap();
            Token::Int(neg.map_or_else(|| v, |_| -v))
        });

    let escape = just('\\').ignore_then(choice((
        just('\\'),
        just('"'),
        just('n').to('\n'),
        just('t').to('\t'),
    )));

    let string = none_of("\\\"")
        .or(escape)
        .repeated()
        .collect::<String>()
        .map(Token::Str)
        .delimited_by(just('"'), just('"'));

    let op = choice((
        just("+"),
        just("-"),
        just("*"),
        just("/"),
        just("|"),
        just("&"),
        just("="),
        just("<>"),
        just("<="),
        just(">="),
        just("<"),
        just(">"),
    ))
    .to_slice()
    .map(Token::Op);

    let ctrl = choice((
        just(":="),
        just(":"),
        just("("),
        just(")"),
        just("{"),
        just("}"),
        just("["),
        just("]"),
        just(";"),
        just(","),
    ))
    .to_slice()
    .map(Token::Ctrl);

    let ident = text::ascii::ident().map(|ident| match ident {
        "type" => Token::Type,
        "array" => Token::Array,
        "of" => Token::Of,
        "var" => Token::Var,
        "function" => Token::Function,
        "let" => Token::Let,
        "in" => Token::In,
        "end" => Token::End,
        "if" => Token::If,
        "then" => Token::Then,
        "else" => Token::Else,
        "while" => Token::While,
        "do" => Token::Do,
        "for" => Token::For,
        "to" => Token::To,
        "break" => Token::Break,
        _ => Token::Ident(ident),
    });

    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .ignored()
        .padded();

    let token = int.or(string).or(op).or(ctrl).or(ident);

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{lexer, Token};
    use chumsky::prelude::*;

    fn tokenize_ok<'a>(s: &'a str) -> Vec<Token<'a>> {
        let (toks, errs) = lexer().parse(s).into_output_errors();
        assert!(errs.is_empty(), "{:?}", errs);
        assert!(toks.is_some());
        toks.unwrap().iter().map(|(t, _)| t.clone()).collect()
    }

    #[test]
    fn lex_int() {
        let toks = tokenize_ok("123 456 -50");
        assert_eq!(
            toks,
            vec![Token::Int(123), Token::Int(456), Token::Int(-50)]
        );
    }

    #[test]
    fn lex_str() {
        let toks = tokenize_ok(r#""" "abc" "a\nb\tc" "\\\"z\"""#);
        assert_eq!(
            toks,
            vec![
                Token::Str("".to_owned()),
                Token::Str("abc".to_owned()),
                Token::Str("a\nb\tc".to_owned()),
                Token::Str(r#"\"z""#.to_owned()),
            ]
        )
    }

    #[test]
    fn lex_op() {
        let toks = tokenize_ok("+-*<><=< =");
        assert_eq!(
            toks,
            vec![
                Token::Op("+"),
                Token::Op("-"),
                Token::Op("*"),
                Token::Op("<>"),
                Token::Op("<="),
                Token::Op("<"),
                Token::Op("="),
            ]
        );
    }

    #[test]
    fn lex_ctrl() {
        let toks = tokenize_ok("::=:();");
        assert_eq!(
            toks,
            vec![
                Token::Ctrl(":"),
                Token::Ctrl(":="),
                Token::Ctrl(":"),
                Token::Ctrl("("),
                Token::Ctrl(")"),
                Token::Ctrl(";")
            ]
        )
    }

    #[test]
    fn lex_ident() {
        let toks = tokenize_ok("x if if0 type type_");
        assert_eq!(
            toks,
            vec![
                Token::Ident("x"),
                Token::If,
                Token::Ident("if0"),
                Token::Type,
                Token::Ident("type_")
            ]
        )
    }

    #[test]
    fn with_comment() {
        let s = r#"
            x // comment
            "//" // "//"
        "#;
        let toks = tokenize_ok(s);
        assert_eq!(toks, vec![Token::Ident("x"), Token::Str("//".to_owned())])
    }
}
