use crate::core::{Expr, Pattern, PatternBuildError, Primitive, Untyped, ValType};

pub mod constants {
    pub const TYPE_STRING: &str = "str";
    pub const TYPE_CHAR: &str = "char";
    pub const TYPE_UINT: &str = "uint";
    pub const TYPE_BOOL: &str = "bool";
    pub const LET: &str = "let";
    pub const IF: &str = "if";
    pub const ELSE: &str = "else";
    pub const FUNC: &str = "func";
    pub const TUPLE_SEP: &str = ",";
    pub const EXPR_SEP: &str = ";";
    pub const ASSIGN: &str = "=";
    pub const TYPE_SEP: &str = ":";
    pub const ACCESS: &str = ".";

    pub const SYMBOLS: &[&str] = &[
        ASSIGN, // assignment
        "!=", "==", "<=", ">=", "||", "&&", "!", "<", ">", // boolean
        "+", "-", "*", "/", "**", // arithmetic
        "[", "]", "(", ")", "{", "}", // delimiters
        EXPR_SEP, TUPLE_SEP, TYPE_SEP, // misc
        ACCESS,   // access
    ];
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    Word(&'a str),
    Numeric(&'a str),
}

impl<'a> Token<'a> {
    /// Returns the contents of this token.
    pub fn contents(&self) -> &'a str {
        match self {
            Token::Numeric(s) | Token::Word(s) => s,
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

    fn peek_one_escaped(&mut self) -> Option<&'a str> {
        let mut it = self.source.char_indices();
        match (it.next()?, it.next()) {
            // if the next character is an escape sequence, return the first two characters
            ((_, '\\'), Some((i, _))) => Some(&self.source[..i + 1]),
            // otherwise, simply return the first character
            ((i, _), _) => Some(&self.source[..i + 1]),
        }
    }

    pub fn peek_token(&mut self) -> Option<Token<'a>> {
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
            .find(|i| constants::SYMBOLS.contains(&&l[..*i]))
        {
            return Some(Token::Word(&l[..sym_idx]));
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
        Some(Token::Word(l))
    }

    pub fn next_token(&mut self) -> Option<Token<'a>> {
        let token = self.peek_token()?;
        self.source = &self.source[token.contents().len()..];
        Some(token)
    }
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseError {
    #[error("unknown token")]
    BadToken,
    #[error("expected token {0:?}")]
    ExpectedToken(String),
    #[error("expected some word")]
    ExpectedWord,
    #[error("unexpected eof")]
    UnexpectedEof,
    #[error("unexpected type")]
    ExpectedType,
    #[error("unexpected pattern")]
    ExpectedPattern,
    #[error("not a pattern: {0:?}")]
    InvalidPattern(#[from] PatternBuildError),
    #[error("not a numeric: {0:?}")]
    ParseIntError(#[from] std::num::ParseIntError),
    #[error("not a boolean: {0:?}")]
    ParseBoolError(#[from] std::str::ParseBoolError),
}

#[derive(Debug, Clone)]
pub struct PrattParser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> PrattParser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self { lexer }
    }

    fn try_consume<'b>(&mut self, word_contents: &'b str) -> Result<Token<'a>, ParseError> {
        if (self.lexer.peek_token().ok_or(ParseError::UnexpectedEof)?) == Token::Word(word_contents)
        {
            Ok(self.lexer.next_token().unwrap())
        } else {
            Err(ParseError::ExpectedToken(word_contents.into()))
        }
    }

    fn try_consume_non_symbol(&mut self) -> Result<Token<'a>, ParseError> {
        if matches!(
            self.lexer.peek_token().ok_or(ParseError::UnexpectedEof)?,
            Token::Word(s) if !constants::SYMBOLS.contains(&s)
        ) {
            Ok(self.lexer.next_token().unwrap())
        } else {
            Err(ParseError::ExpectedWord)
        }
    }

    fn check_non_symbol_and<'b>(&self, token_after_word: &'b str) -> bool {
        let mut test = self.clone();
        test.try_consume_non_symbol().is_ok() && test.try_consume(token_after_word).is_ok()
    }

    fn parse_bindings_opt(&mut self) -> Result<Vec<(&'a str, Option<ValType<'a>>)>, ParseError> {
        let mut inner_types = Vec::new();
        loop {
            let Ok(Token::Word(key)) = self.try_consume_non_symbol() else {
                break;
            };
            let key_type = self
                .try_consume(constants::TYPE_SEP)
                .and_then(|_| self.parse_type())
                .ok();
            inner_types.push((key, key_type));
            if self.try_consume(constants::TUPLE_SEP).is_err() {
                break;
            }
        }
        Ok(inner_types)
    }

    fn parse_bindings(&mut self) -> Result<Vec<(&'a str, ValType<'a>)>, ParseError> {
        let mut inner_types = Vec::new();
        loop {
            let Ok(Token::Word(key)) = self.try_consume_non_symbol() else {
                break;
            };
            self.try_consume(constants::TYPE_SEP)?;
            let key_type = self.parse_type()?;
            inner_types.push((key, key_type));
            if self.try_consume(constants::TUPLE_SEP).is_err() {
                break;
            }
        }
        Ok(inner_types)
    }

    fn parse_tuple_type_inner(&mut self) -> Result<ValType<'a>, ParseError> {
        let is_named = self.check_non_symbol_and(constants::TYPE_SEP);
        if is_named {
            // named tuple type
            let mut inner_types = self.parse_bindings()?;
            Ok(ValType::NamedTuple(inner_types))
        } else {
            // ordered tuple type
            let mut inner_types = Vec::new();
            while let Ok(ty) = self.parse_type() {
                inner_types.push(ty);
                if self.try_consume(constants::TUPLE_SEP).is_err() {
                    break;
                }
            }
            Ok(ValType::OrderedTuple(inner_types))
        }
    }

    fn parse_type(&mut self) -> Result<ValType<'a>, ParseError> {
        match self.lexer.peek_token() {
            Some(Token::Word(constants::TYPE_BOOL)) => {
                self.lexer.next_token().unwrap();
                Ok(ValType::Bool)
            }
            Some(Token::Word(constants::TYPE_UINT)) => {
                self.lexer.next_token().unwrap();
                Ok(ValType::Uint)
            }
            Some(Token::Word(constants::TYPE_CHAR)) => {
                self.lexer.next_token().unwrap();
                Ok(ValType::Char)
            }
            Some(Token::Word(constants::TYPE_STRING)) => {
                self.lexer.next_token().unwrap();
                Ok(ValType::String)
            }
            Some(Token::Word(constants::FUNC)) => {
                self.lexer.next_token().unwrap();
                let arg_type = self.parse_type()?;
                let ret_type = self.parse_type()?;
                Ok(ValType::Func(Box::new(arg_type), Box::new(ret_type)))
            }
            Some(Token::Word("(")) => {
                self.lexer.next_token().unwrap();
                let ty = self.parse_tuple_type_inner()?;
                self.try_consume(")")?;
                Ok(ty)
            }
            _ => Err(ParseError::ExpectedType),
        }
    }

    fn parse_pattern(&mut self) -> Result<Pattern<'a>, ParseError> {
        let with_parens = self.try_consume("(").is_ok();
        let bindings = self.parse_bindings_opt()?;
        if with_parens {
            self.try_consume(")")?;
        }
        Ok(Pattern::from_iter(bindings))
    }

    fn parse_new_tuple_expr(&mut self) -> Result<Expr<'a, Untyped>, ParseError> {
        self.try_consume("(")?;
        let is_named = self.check_non_symbol_and(constants::ASSIGN);
        if is_named {
            let mut expr_pairs = Vec::new();
            loop {
                let Ok(Token::Word(key)) = self.try_consume_non_symbol() else {
                    break;
                };
                self.try_consume(constants::ASSIGN)?;
                let rhs = self.parse_expr(0)?;
                expr_pairs.push((key, rhs));
                if self.try_consume(constants::TUPLE_SEP).is_err() {
                    break;
                }
            }
            self.try_consume(")")?;
            Ok(Expr::NewNamedTuple(Untyped, expr_pairs))
        } else {
            let mut exprs = Vec::new();
            while let Ok(expr) = self.parse_expr(0) {
                exprs.push(expr);
                if self.try_consume(constants::TUPLE_SEP).is_err() {
                    break;
                }
            }
            self.try_consume(")")?;
            Ok(Expr::NewOrderedTuple(Untyped, exprs))
        }
    }

    fn parse_let_expr(&mut self) -> Result<Expr<'a, Untyped>, ParseError> {
        self.try_consume(constants::LET)?;
        let lhs = self.parse_pattern()?;
        self.try_consume(constants::ASSIGN)?;
        let rhs = self.parse_expr(0)?;
        return Ok(Expr::Let {
            expr_type: Untyped,
            lhs,
            rhs: Box::new(rhs),
        });
    }

    fn parse_if_expr(&mut self) -> Result<Expr<'a, Untyped>, ParseError> {
        self.try_consume(constants::IF)?;
        let cond = self.parse_expr(0)?;
        let main_branch = self.parse_expr(0)?;
        let else_branch = if self
            .lexer
            .peek_token()
            .is_some_and(|t| t == Token::Word(constants::ELSE))
        {
            self.lexer.next_token().unwrap();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        return Ok(Expr::If {
            expr_type: Untyped,
            cond: Box::new(cond),
            main_branch: Box::new(main_branch),
            else_branch: else_branch.map(|b| Box::new(b)),
        });
    }

    fn parse_new_func_expr(&mut self) -> Result<Expr<'a, Untyped>, ParseError> {
        self.try_consume(constants::FUNC)?;
        self.try_consume("(")?;
        let params = self.parse_bindings()?;
        self.try_consume(")")?;
        let body = self.parse_expr(0)?;
        return Ok(Expr::NewFunc {
            expr_type: Untyped,
            params,
            body: Box::new(body),
        });
    }

    pub fn parse_expr(&mut self, min_bp: usize) -> Result<Expr<'a, Untyped>, ParseError> {
        let mut lhs = match self.lexer.peek_token() {
            Some(Token::Numeric(num)) => {
                self.lexer.next_token().unwrap();
                Expr::NewPrimitive(Untyped, Primitive::Uint(num.parse()?))
            }
            Some(Token::Word("true")) | Some(Token::Word("false")) => {
                let bool_val = self.lexer.next_token().unwrap().contents();
                Expr::NewPrimitive(Untyped, Primitive::Bool(bool_val.parse()?))
            }
            Some(Token::Word(constants::LET)) => self.parse_let_expr()?,
            Some(Token::Word(constants::IF)) => self.parse_if_expr()?,
            Some(Token::Word(constants::FUNC)) => self.parse_new_func_expr()?,
            Some(Token::Word("(")) => self.parse_new_tuple_expr()?,
            Some(Token::Word("{")) => {
                self.lexer.next_token().unwrap();
                let mut exprs = Vec::new();
                while let Ok(expr) = self.parse_expr(0) {
                    exprs.push(expr);
                    if self.try_consume(constants::EXPR_SEP).is_err() {
                        break;
                    }
                }
                self.try_consume("}")?;
                Expr::Block {
                    expr_type: Untyped,
                    exprs,
                }
            }
            Some(Token::Word(s))
                if constants::SYMBOLS.contains(&s) && prefix_binding(s).is_some() =>
            {
                self.lexer.next_token().unwrap();
                let prefix_binding = prefix_binding(s).unwrap();
                let rhs = self.parse_expr(prefix_binding)?;
                Expr::Call {
                    expr_type: Untyped,
                    func_name: s,
                    arg: Box::new(rhs),
                }
            }
            Some(Token::Word(s)) if !constants::SYMBOLS.contains(&s) => {
                self.lexer.next_token().unwrap();
                Expr::Ref(Untyped, s)
            }
            _ => return Err(ParseError::BadToken),
        };
        loop {
            match (&lhs, self.lexer.peek_token()) {
                // infix operator.
                (_, Some(Token::Word(op)))
                    if infix_binding(op).is_some_and(|(l_bp, _)| l_bp >= min_bp) =>
                {
                    self.lexer.next_token();
                    let (_, r_bp) = infix_binding(op).unwrap();
                    let rhs = self.parse_expr(r_bp)?;
                    lhs = match rhs {
                        Expr::Ref(_, field_name) if op == constants::ACCESS => Expr::Access {
                            expr_type: Untyped,
                            lhs: Box::new(lhs),
                            field_name,
                        },
                        _ => Expr::Call {
                            expr_type: Untyped,
                            func_name: op,
                            arg: Box::new(Expr::NewOrderedTuple(Untyped, vec![lhs, rhs])),
                        },
                    }
                }
                // start of a new tuple expression after a ref expression means we are performing a function call
                (Expr::Ref(_, r), Some(Token::Word("("))) => {
                    let Ok(arg) = self.parse_new_tuple_expr() else {
                        break;
                    };
                    lhs = Expr::Call {
                        expr_type: Untyped,
                        func_name: r,
                        arg: Box::new(arg),
                    }
                }
                _ => break,
            };
        }
        Ok(lhs)
    }
}

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
        constants::ACCESS => Some((14, 13)),
        _ => None,
    }
}

impl<'a> Expr<'a, Untyped> {
    pub fn parse(s: &'a str) -> Result<Self, ParseError> {
        PrattParser::new(Lexer::new(s)).parse_expr(0)
    }
}
