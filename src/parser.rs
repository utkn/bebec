use std::collections::HashMap;

use crate::core::{Expr, Pattern, Primitive, Untyped, ValType};

const SYMBOLS: &[&str] = &[
    "=", // assignment
    "!=", "==", "<=", ">=", "||", "&&", "!", "<", ">", // boolean
    "+", "-", "*", "/", "**", // arithmetic
    "[", "]", "(", ")", "{", "}", // delimiters
    ".", // access
    ";", ",", ":", // misc
];

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    Symbol(&'a str),
    Word(&'a str),
    Numeric(&'a str),
    Unknown(&'a str),
}

impl<'a> Token<'a> {
    pub fn contents(&self) -> &'a str {
        match self {
            Token::Numeric(s) | Token::Symbol(s) | Token::Word(s) | Token::Unknown(s) => s,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    source: &'a str,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source }
    }

    pub fn peek(&mut self) -> Option<Token<'a>> {
        self.source = self.source.trim_start();
        if self.source.is_empty() {
            return None;
        }
        let (l, _) = self
            .source
            .split_once(char::is_whitespace)
            .unwrap_or((self.source, self.source));
        if let Some(sym_idx) = l
            .char_indices()
            .rev()
            .map(|(i, _)| i + 1)
            .find(|i| SYMBOLS.contains(&&l[..*i]))
        {
            return Some(Token::Symbol(&l[..sym_idx]));
        }
        if let Some(num_idx) = l
            .char_indices()
            .take_while(|(_, c)| c.is_digit(10))
            .map(|(i, _)| i + 1)
            .last()
        {
            return Some(Token::Numeric(&l[..num_idx]));
        }
        if let Some(word_idx) = l
            .char_indices()
            .take_while(|(_, c)| c.is_alphanumeric() || *c == '_' || *c == '-')
            .map(|(i, _)| i + 1)
            .last()
        {
            return Some(Token::Word(&l[..word_idx]));
        }
        Some(Token::Unknown(l))
    }

    pub fn next(&mut self) -> Option<Token<'a>> {
        let token = self.peek()?;
        self.source = &self.source[token.contents().len()..];
        Some(token)
    }
}

#[derive(Debug, Clone)]
pub struct PrattParser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> PrattParser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self { lexer }
    }

    fn try_consume(&mut self, pred: impl FnOnce(Token<'a>) -> bool) -> Option<Token<'a>> {
        if pred(self.lexer.peek()?) {
            self.lexer.next()
        } else {
            None
        }
    }

    fn parse_type(&mut self) -> Option<ValType<'a>> {
        match self.lexer.peek() {
            Some(Token::Word("bool")) => {
                self.lexer.next().unwrap();
                Some(ValType::Bool)
            }
            Some(Token::Word("uint")) => {
                self.lexer.next().unwrap();
                Some(ValType::Uint)
            }
            Some(Token::Word("char")) => {
                self.lexer.next().unwrap();
                Some(ValType::Char)
            }
            Some(Token::Word("str")) => {
                self.lexer.next().unwrap();
                Some(ValType::String)
            }
            _ => None,
        }
    }

    fn parse_pattern(&mut self) -> Option<Pattern<'a>> {
        // TODO make it recursive !!!!
        self.try_consume(|t| t == Token::Symbol("("))?;
        let mut single_pats = Vec::new();
        while let Some(t) = self.try_consume(|t| matches!(t, Token::Word(_))) {
            let pat_name = t.contents();
            let pat_type = self.parse_type()?;
            single_pats.push(Pattern::Single(pat_name, pat_type));
            if self.try_consume(|t| t == Token::Symbol(",")).is_none() {
                break;
            }
        }
        self.try_consume(|t| t == Token::Symbol(")"))?;
        Some(Pattern::Tuple(single_pats))
    }

    fn parse_new_tuple_expr(&mut self) -> Option<Expr<'a, Untyped>> {
        self.try_consume(|t| t == Token::Symbol("("))?;
        let is_named = {
            let mut test = self.clone();
            test.try_consume(|t| matches!(t, Token::Word(_))).is_some()
                && test.try_consume(|t| t == Token::Symbol("=")).is_some()
        };
        if is_named {
            let mut exprs = HashMap::new();
            loop {
                let Some(Token::Word(key)) = self.try_consume(|t| matches!(t, Token::Word(_)))
                else {
                    break;
                };
                self.try_consume(|t| t == Token::Symbol("="))?;
                let rhs = self.parse_expr(0)?;
                exprs.insert(key, rhs);
                if self.try_consume(|t| t == Token::Symbol(",")).is_none() {
                    break;
                }
            }
            self.try_consume(|t| t == Token::Symbol(")"))?;
            Some(Expr::NewNamedTuple(Untyped, exprs))
        } else {
            let mut exprs = Vec::new();
            while let Some(expr) = self.parse_expr(0) {
                exprs.push(expr);
                if self.try_consume(|t| t == Token::Symbol(",")).is_none() {
                    break;
                }
            }
            self.try_consume(|t| t == Token::Symbol(")"))?;
            Some(Expr::NewOrderedTuple(Untyped, exprs))
        }
    }

    fn parse_let_expr(&mut self) -> Option<Expr<'a, Untyped>> {
        self.try_consume(|t| t == Token::Word("let"))?;
        let binding_name = self
            .try_consume(|t| matches!(t, Token::Word(_)))?
            .contents();
        self.try_consume(|t| t == Token::Symbol("="))?;
        let rhs = self.parse_expr(0)?;
        return Some(Expr::Let {
            ret_type: Untyped,
            name: binding_name,
            rhs: Box::new(rhs),
        });
    }

    fn parse_if_expr(&mut self) -> Option<Expr<'a, Untyped>> {
        self.try_consume(|t| t == Token::Word("if"))?;
        let cond = self.parse_expr(0)?;
        let main_branch = self.parse_expr(0)?;
        let else_branch = if self.lexer.peek().is_some_and(|t| t == Token::Word("else")) {
            self.lexer.next()?;
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        return Some(Expr::If {
            ret_type: Untyped,
            cond: Box::new(cond),
            main_branch: Box::new(main_branch),
            else_branch: else_branch.map(|b| Box::new(b)),
        });
    }

    fn parse_new_func_expr(&mut self) -> Option<Expr<'a, Untyped>> {
        self.lexer.next()?;
        let arg_pattern = self.parse_pattern()?;
        let body = self.parse_expr(0)?;
        return Some(Expr::NewFunc {
            ret_type: Untyped,
            arg_pattern,
            body: Box::new(body),
        });
    }

    pub fn parse_expr(&mut self, min_bp: usize) -> Option<Expr<'a, Untyped>> {
        let mut lhs = match self.lexer.peek() {
            Some(Token::Numeric(num)) => {
                self.lexer.next().unwrap();
                Expr::NewPrimitive(Untyped, Primitive::Uint(num.parse().ok()?))
            }
            Some(Token::Word("true")) | Some(Token::Word("false")) => {
                let bool_val = self.lexer.next().unwrap().contents();
                Expr::NewPrimitive(Untyped, Primitive::Bool(bool_val.parse().ok()?))
            }
            Some(Token::Word("let")) => self.parse_let_expr()?,
            Some(Token::Word("if")) => self.parse_if_expr()?,
            Some(Token::Word("func")) => self.parse_new_func_expr()?,
            Some(Token::Symbol("(")) => self.parse_new_tuple_expr()?,
            Some(Token::Symbol("{")) => {
                self.lexer.next().unwrap();
                let mut exprs = Vec::new();
                while let Some(expr) = self.parse_expr(0) {
                    exprs.push(expr);
                    if self.try_consume(|t| t == Token::Symbol(";")).is_none() {
                        break;
                    }
                }
                self.try_consume(|t| t == Token::Symbol("}"))?;
                Expr::Block {
                    ret_type: Untyped,
                    exprs,
                }
            }
            Some(Token::Word(s)) => {
                self.lexer.next().unwrap();
                Expr::Ref(Untyped, s)
            }
            Some(Token::Symbol(s)) if prefix_binding(s).is_some() => {
                self.lexer.next().unwrap();
                let prefix_binding = prefix_binding(s).unwrap();
                let rhs = self.parse_expr(prefix_binding)?;
                Expr::Call {
                    ret_type: Untyped,
                    func_name: s,
                    arg: Box::new(rhs),
                }
            }
            _ => return None,
        };
        loop {
            match self.lexer.peek() {
                // infix operator.
                Some(Token::Symbol(op))
                    if infix_binding(op).is_some_and(|(l_bp, _)| l_bp >= min_bp) =>
                {
                    self.lexer.next();
                    let (_, r_bp) = infix_binding(op).unwrap();
                    let rhs = self.parse_expr(r_bp)?;
                    lhs = match rhs {
                        Expr::Ref(_, field_name) if op == "." => Expr::Access {
                            ret_type: Untyped,
                            lhs: Box::new(lhs),
                            field_name,
                        },
                        _ => Expr::Call {
                            ret_type: Untyped,
                            func_name: op,
                            arg: Box::new(Expr::NewOrderedTuple(Untyped, vec![lhs, rhs])),
                        },
                    }
                }
                _ => match lhs {
                    // another expression after a ref expression
                    // treat the callee as a prefix operator with a binding of `CALL_BINDING`
                    Expr::Ref(_, r) => {
                        let Some(arg) = self.parse_expr(CALL_BINDING) else {
                            break;
                        };
                        lhs = Expr::Call {
                            ret_type: Untyped,
                            func_name: r,
                            arg: Box::new(arg),
                        }
                    }
                    _ => break,
                },
            };
        }
        Some(lhs)
    }
}

const CALL_BINDING: usize = usize::MAX;

fn prefix_binding(s: &str) -> Option<usize> {
    match s {
        "+" | "-" => Some(9),
        "!" => Some(9),
        _ => None,
    }
}

fn infix_binding(s: &str) -> Option<(usize, usize)> {
    match s {
        "+" | "-" => Some((5, 6)),
        "*" | "/" => Some((7, 8)),
        "&&" | "||" => Some((7, 8)),
        "==" | "!=" | "<" | ">" | "<=" | ">=" => Some((4, 5)),
        "." => Some((14, 13)),
        _ => None,
    }
}

#[derive(Debug, thiserror::Error)]
#[error("error while parsing {0}")]
pub struct ParseError(String);

impl<'a> Expr<'a, Untyped> {
    pub fn parse(s: &'a str) -> Result<Self, ParseError> {
        PrattParser::new(Lexer::new(s))
            .parse_expr(0)
            .ok_or(ParseError(":(".into()))
    }
}
