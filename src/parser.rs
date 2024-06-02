use winnow::ascii::{digit1, multispace1};
use winnow::combinator::{alt, opt, preceded, terminated};
use winnow::error::ParserError;
use winnow::prelude::*;
use winnow::stream::{AsChar, Stream, StreamIsPartial};
use winnow::{
    ascii::multispace0,
    combinator::{delimited, separated, separated_pair},
    token::take_while,
};

use crate::core::{Expr, Pattern, Primitive};

/// A parser combinator for optionally whitespace delimited parsers.
fn ws<'a, I, O, E>(p: impl winnow::Parser<I, O, E>) -> impl winnow::Parser<I, O, E>
where
    I: StreamIsPartial + Stream,
    <I as Stream>::Token: AsChar + Clone,
    E: ParserError<I>,
{
    delimited(multispace0, p, multispace0)
}

/// A parser for a word.
fn word<'a>(s: &mut &'a str) -> PResult<&'a str> {
    take_while(1.., |c: char| c.is_alphanumeric() || c == '-' || c == '_').parse_next(s)
}

/// A parser for a pattern.
fn pattern<'a>(s: &mut &'a str) -> PResult<Pattern<'a>> {
    delimited('(', (separated(0.., ws(word), ','), opt(ws(','))), ')')
        .map(|(names, _): (Vec<_>, _)| Pattern::NameTuple(names))
        .parse_next(s)
}

/// A parser for a new tuple expression.
fn expr_new_named_tuple<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    delimited(
        '(',
        (
            separated(0.., separated_pair(ws(word), '=', ws(expr)), ','),
            opt(ws(',')),
        ),
        ')',
    )
    .map(|(pairs, _)| Expr::NewNamedTuple(pairs))
    .parse_next(s)
}

/// A parser for a new tuple expression.
fn expr_new_unnamed_tuple<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    delimited('(', (separated(0.., ws(expr), ','), opt(ws(','))), ')')
        .map(|(exprs, _)| Expr::NewOrderedTuple(exprs))
        .parse_next(s)
}

fn expr_new_primitive<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    alt((
        digit1
            .parse_to()
            .map(|v: usize| Expr::NewPrimitive(Primitive::Uint(v))),
        ("true").map(|_| Expr::NewPrimitive(Primitive::Bool(true))),
        ("false").map(|_| Expr::NewPrimitive(Primitive::Bool(false))),
        ("nil").map(|_| Expr::NewPrimitive(Primitive::Nil)),
    ))
    .parse_next(s)
}

/// A parser for a new function expression.
fn expr_new_func<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    preceded("func", (opt(ws(pattern)), ws(expr)))
        .map(|(arg_pattern, body)| Expr::NewFunc {
            arg_pattern,
            body: Box::new(body),
        })
        .parse_next(s)
}

fn expr_call_infix<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    alt((
        separated_pair(expr, ws('+'), expr).map(|(e1, e2)| Expr::Call {
            func_name: "+",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws('-'), expr).map(|(e1, e2)| Expr::Call {
            func_name: "-",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws('*'), expr).map(|(e1, e2)| Expr::Call {
            func_name: "*",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws('/'), expr).map(|(e1, e2)| Expr::Call {
            func_name: "/",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws("&&"), expr).map(|(e1, e2)| Expr::Call {
            func_name: "&&",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws("||"), expr).map(|(e1, e2)| Expr::Call {
            func_name: "||",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws("=="), expr).map(|(e1, e2)| Expr::Call {
            func_name: "==",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
        separated_pair(expr, ws("!="), expr).map(|(e1, e2)| Expr::Call {
            func_name: "!=",
            arg: Box::new(Expr::NewOrderedTuple(vec![e1, e2])),
        }),
    ))
    .parse_next(s)
}

/// A parser for a call expression.
fn expr_call<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    alt((
        (word, alt((expr_new_named_tuple, expr_new_unnamed_tuple))).map(|(func_name, arg)| {
            Expr::Call {
                func_name,
                arg: Box::new(arg),
            }
        }),
        delimited('(', expr_call_infix, ')'),
    ))
    .parse_next(s)
}

/// A parser for an if expression.
fn expr_if<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    preceded("if", (ws(expr), ws(expr), opt(preceded("else", ws(expr)))))
        .map(|(cond, main_branch, else_branch)| Expr::If {
            cond: Box::new(cond),
            main_branch: Box::new(main_branch),
            else_branch: else_branch.map(|else_branch| Box::new(else_branch)),
        })
        .parse_next(s)
}

/// A parser for a let expression.
fn expr_let<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    preceded("let", separated_pair(ws(word), '=', ws(expr)))
        .map(|(name, rhs): (_, Expr<'a>)| Expr::Let {
            name,
            rhs: Box::new(rhs),
        })
        .parse_next(s)
}

/// A parser for a block expression.
fn expr_block<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    delimited('{', separated(0.., ws(expr), ';'), '}')
        .map(|exprs| Expr::Block { exprs })
        .parse_next(s)
}

//// A parser for an expression.
fn expr<'a>(s: &mut &'a str) -> PResult<Expr<'a>> {
    alt((
        delimited('(', ws(expr), ')'),
        expr_new_named_tuple,
        expr_new_unnamed_tuple,
        expr_block,
        expr_new_func,
        expr_let,
        expr_if,
        expr_new_primitive,
        expr_call,
        word.map(|s| Expr::Ref(s)),
    ))
    .parse_next(s)
}

#[derive(Debug, thiserror::Error)]
#[error("error while parsing {0}")]
pub struct ParseError(String);

impl<'a> Expr<'a> {
    pub fn parse(s: &'a str) -> Result<Self, ParseError> {
        let s = &mut &*s;
        ws(expr)
            .parse_next(s)
            .map_err(|_| ParseError(s.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn test_word() {
        let r = ws(word).parse("").ok();
        assert_eq!(r, None);
        let r = ws(word).parse(" a").ok();
        assert_eq!(r, Some("a"));
        let r = ws(word).parse("a ").ok();
        assert_eq!(r, Some("a"));
        let r = ws(word).parse("01").ok();
        assert_eq!(r, Some("01"));
        let r = ws(word).parse("abc-d_e").ok();
        assert_eq!(r, Some("abc-d_e"));
        let r = ws(word).parse("abc-d_e f").ok();
        assert_eq!(r, None);
    }

    #[test]
    fn test_let() {
        let r = expr_let.parse("let x = y").ok();
        assert_eq!(
            r,
            Some(Expr::Let {
                name: "x",
                rhs: Box::new(Expr::Ref("y"))
            })
        )
    }

    #[test]
    fn test_if() {
        let r = expr_if.parse("if (x) (1) else (0)").ok();
        assert_eq!(
            r,
            Some(Expr::If {
                cond: Box::new(Expr::Ref("x")),
                main_branch: Box::new(Expr::NewPrimitive(Primitive::Uint(1))),
                else_branch: Some(Box::new(Expr::NewPrimitive(Primitive::Uint(0))))
            })
        );
        let r = expr_if.parse("if (x) (1)").ok();
        assert_eq!(
            r,
            Some(Expr::If {
                cond: Box::new(Expr::Ref("x")),
                main_branch: Box::new(Expr::NewPrimitive(Primitive::Uint(1))),
                else_branch: None
            })
        )
    }

    #[test]
    fn test_new_named_tuple() {
        let r = expr_new_named_tuple.parse("()").ok();
        assert_eq!(r, Some(Expr::NewNamedTuple(HashMap::from_iter([]))));
        let r = expr_new_named_tuple.parse("(a=x)").ok();
        assert_eq!(
            r,
            Some(Expr::NewNamedTuple(HashMap::from_iter([(
                "a",
                Expr::Ref("x")
            )])))
        );
        let r = expr_new_named_tuple.parse("(a=x, b=y)").ok();
        assert_eq!(
            r,
            Some(Expr::NewNamedTuple(HashMap::from_iter([
                ("a", Expr::Ref("x")),
                ("b", Expr::Ref("y"))
            ])))
        );
        let r = expr_new_named_tuple.parse("(a=x,b=y, )").ok();
        assert_eq!(
            r,
            Some(Expr::NewNamedTuple(HashMap::from_iter([
                ("a", Expr::Ref("x")),
                ("b", Expr::Ref("y"))
            ])))
        );
    }

    #[test]
    fn test_new_unnamed_tuple() {
        let r = expr_new_unnamed_tuple.parse("()").ok();
        assert_eq!(r, Some(Expr::NewOrderedTuple(Vec::from_iter([]))));
        let r = expr_new_unnamed_tuple.parse("(x)").ok();
        assert_eq!(
            r,
            Some(Expr::NewOrderedTuple(Vec::from_iter([(Expr::Ref("x"))])))
        );
        let r = expr_new_unnamed_tuple.parse("(x, y)").ok();
        assert_eq!(
            r,
            Some(Expr::NewOrderedTuple(Vec::from_iter([
                Expr::Ref("x"),
                Expr::Ref("y")
            ])))
        );
        let r = expr_new_unnamed_tuple.parse("(x,y, )").ok();
        assert_eq!(
            r,
            Some(Expr::NewOrderedTuple(Vec::from_iter([
                Expr::Ref("x"),
                Expr::Ref("y")
            ])))
        );
    }
}
