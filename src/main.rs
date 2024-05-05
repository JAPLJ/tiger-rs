use std::{env, fs};

use anyhow::{bail, Result};
use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::*;
use inkwell::context::Context;
use lasso::Rodeo;
use tiger::{
    absyn::parser,
    alpha::alpha,
    ir::gen_ir,
    lex::lexer,
    lift::lambda_lift,
    semant::trans_exp,
    symtable::SymTable,
    typing::{TEnv, Type, VEnv},
};

fn main() -> Result<()> {
    let ctx = Context::create();
    let module = ctx.create_module("main");
    let builder = ctx.create_builder();

    let prog = fs::read_to_string(env::args().nth(1).expect("Expected filepath"))
        .expect("Failed to read file");
    let prog = &prog;

    let (toks, errs) = lexer().parse(prog).into_output_errors();
    if !errs.is_empty() {
        errs.into_iter().for_each(|e| {
            Report::build(ReportKind::Error, (), e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new(e.span().into_range())
                        .with_message(e.reason().to_string())
                        .with_color(Color::Red),
                )
                .finish()
                .print(Source::from(prog))
                .unwrap();
        });
        bail!("compile error")
    }
    let toks = toks.unwrap();

    let mut symt = Rodeo::new();
    let (ast, errs) = parser()
        .map_with(|ast, e| (ast, e.span()))
        .parse_with_state(toks.as_slice().spanned((1..1).into()), &mut symt)
        .into_output_errors();
    let (expr, symt, errs) = if let Some((expr, _)) = ast {
        (Some(expr), Some(symt), errs)
    } else {
        (None, None, errs)
    };
    if !errs.is_empty() {
        errs.into_iter().for_each(|e| {
            Report::build(ReportKind::Error, (), e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new(e.span().into_range())
                        .with_message(e.reason().to_string())
                        .with_color(Color::Red),
                )
                .finish()
                .print(Source::from(prog))
                .unwrap();
        });
        bail!("compile error")
    }

    let mut symt = SymTable::from_rodeo(symt.unwrap());
    let venv = VEnv::new();
    let tenv = TEnv::new()
        .insert(symt.get_or_intern("int"), Type::Int)
        .insert(symt.get_or_intern("string"), Type::String);

    let ((expr, _), errs) = trans_exp(&mut symt, &venv, &tenv, &expr.unwrap());
    if !errs.is_empty() {
        errs.into_iter().for_each(|e| {
            e.report().print(Source::from(prog)).unwrap();
        });
        bail!("compile error")
    }

    let expr = alpha(&mut symt, &expr);
    let expr = lambda_lift(&mut symt, &expr);

    gen_ir(&ctx, &builder, &module, &expr)?;
    module.print_to_file("output.ll").unwrap();

    Ok(())
}
