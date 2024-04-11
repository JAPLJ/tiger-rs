use crate::{
    absyn::Spanned,
    lex::{lexer, Token},
};

use chumsky::prelude::*;

pub fn tokenize_ok<'a>(s: &'a str) -> Vec<Spanned<Token<'a>>> {
    let (toks, errs) = lexer().parse(s).into_output_errors();
    assert!(errs.is_empty(), "{:?}", errs);
    assert!(toks.is_some());
    toks.unwrap()
}

#[macro_export]
macro_rules! parse {
    ($toks:expr) => {{
        let mut symt = lasso::Rodeo::new();
        let (ast, errs) = crate::absyn::parser()
            .map_with(|ast, e| (ast, e.span()))
            .parse_with_state($toks.as_slice().spanned((1..1).into()), &mut symt)
            .into_output_errors();
        if let Some((expr, _)) = ast {
            (Some(expr), Some(symt), errs)
        } else {
            (None, None, errs)
        }
    }};
}
