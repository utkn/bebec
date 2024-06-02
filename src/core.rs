mod extern_func;

use std::collections::HashMap;

use crate::types::Representible;

pub(crate) use extern_func::{extern_func, ExternCallError, ExternCallable, ExternFunc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderedTuple<'a>(pub Vec<Val<'a>>);

impl<'a> IntoIterator for OrderedTuple<'a> {
    type Item = Val<'a>;

    type IntoIter = <Vec<Val<'a>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> FromIterator<Val<'a>> for OrderedTuple<'a> {
    fn from_iter<T: IntoIterator<Item = Val<'a>>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedTuple<'a>(pub HashMap<&'a str, Val<'a>>);

impl<'a> FromIterator<(&'a str, Val<'a>)> for NamedTuple<'a> {
    fn from_iter<T: IntoIterator<Item = (&'a str, Val<'a>)>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for NamedTuple<'a> {
    type Item = (&'a str, Val<'a>);

    type IntoIter = <HashMap<&'a str, Val<'a>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> NamedTuple<'a> {
    pub fn as_ordered<'b>(
        mut self,
        ordered_names: impl IntoIterator<Item = &'b str>,
    ) -> Option<OrderedTuple<'a>> {
        let mut vals = Vec::new();
        for name in ordered_names {
            vals.push(self.0.remove(name)?);
        }
        Some(vals.into_iter().collect())
    }

    pub fn get(&self, field_name: &str) -> Option<&Val<'a>> {
        self.0.get(field_name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, strum::EnumTryAs)]
pub enum Tuple<'a> {
    Named(NamedTuple<'a>),
    Ordered(OrderedTuple<'a>),
}

impl<'a> Tuple<'a> {
    pub fn len(&self) -> usize {
        match self {
            Tuple::Named(tpl) => tpl.0.len(),
            Tuple::Ordered(tpl) => tpl.0.len(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum DestructError {
    #[error("tuple does not contain the name `{0}`")]
    UnsatisfiedName(String),
    #[error("pattern has different length than the tuple {0} != {1}")]
    DifferentLengths(usize, usize),
    #[error("unmatched pattern")]
    UnmatchedPattern,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<'a> {
    Names(Vec<&'a str>),
    TypeFields(Vec<&'a str>),
}

impl<'a> Pattern<'a> {
    pub fn destruct_into_ctx(&self, val: Val<'a>, ctx: &mut Ctx<'a>) -> Result<(), DestructError> {
        match (self, val) {
            (Pattern::Names(names), Val::Tuple(Tuple::Ordered(OrderedTuple(vals)))) => {
                for (name, val) in names.iter().zip(vals.into_iter()) {
                    ctx.extend_local(*name, val);
                }
                Ok(())
            }
            (Pattern::Names(names), Val::Tuple(Tuple::Named(NamedTuple(mut pairs)))) => {
                if names.len() != pairs.len() {
                    return Err(DestructError::DifferentLengths(names.len(), pairs.len()));
                }
                for name in names {
                    let val = pairs
                        .remove(name)
                        .ok_or(DestructError::UnsatisfiedName(name.to_string()))?;
                    ctx.extend_local(name, val);
                }
                Ok(())
            }
            _ => Err(DestructError::UnmatchedPattern),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, strum::EnumTryAs, strum::EnumIs)]
pub enum Primitive {
    Nil,
    Uint(usize),
    Char(char),
    Bool(bool),
    String(String),
}

#[derive(Debug, thiserror::Error)]
pub enum CallError {
    #[error("error during external call: {0:?}")]
    ExternCallError(#[from] ExternCallError),
    #[error("error while destructuring: {0:?}")]
    DestructError(#[from] DestructError),
    #[error("error while evaluating: {0:?}")]
    FuncEvalError(#[from] Box<EvalError>),
    #[error("unmatched pattern")]
    UnmatchedPattern,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InternFunc<'a> {
    arg_pattern: Option<Pattern<'a>>,
    captured_ctx: Ctx<'a>,
    body: Expr<'a>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Func<'a> {
    Intern(InternFunc<'a>),
    Extern(ExternFunc<'a>),
}

impl<'a> Func<'a> {
    pub fn call(&self, arg: Option<Val<'a>>) -> Result<Val<'a>, CallError> {
        match self {
            Func::Intern(InternFunc {
                arg_pattern,
                captured_ctx,
                body,
                ..
            }) => {
                let mut func_ctx = captured_ctx.clone();
                match (arg_pattern, arg) {
                    // Arg pattern and filled arg tuple.
                    (Some(arg_pattern), Some(arg)) => {
                        arg_pattern
                            .destruct_into_ctx(arg, &mut func_ctx)
                            .map_err(CallError::from)?;
                    }
                    // No pattern, empty arg tuple.
                    (None, Some(Val::Tuple(t))) if t.len() == 0 => {}
                    _ => return Err(CallError::UnmatchedPattern),
                };
                body.clone()
                    .eval(&mut func_ctx)
                    .map_err(|err| CallError::FuncEvalError(Box::new(err)))
            }
            Func::Extern(ExternFunc { body, .. }) => body.call(arg).map_err(CallError::from),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, strum::EnumTryAs)]
pub enum Val<'a> {
    Primitive(Primitive),
    Func(Func<'a>),
    Tuple(Tuple<'a>),
}

impl<'a> Val<'a> {
    /// If the value is an ordered tuple, tries to convert it to `T`. However, if the value is a named tuple, first converts it into an ordered tuple with `ordered_names` before converting to `T`.
    /// Returns `None` if `self` is not a tuple, or the conversion from tuples fail.
    pub fn try_destruct_tuple<T>(
        self,
        ordered_names: impl IntoIterator<Item = &'a str>,
    ) -> Option<T>
    where
        T: Representible<'a>,
    {
        let ordered = match self.try_as_tuple()? {
            Tuple::Named(tpl) => tpl.as_ordered(ordered_names)?,
            Tuple::Ordered(tpl) => tpl,
        };
        T::try_from_val(Val::Tuple(Tuple::Ordered(ordered)))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ctx<'a> {
    bindings: Vec<(&'a str, Val<'a>)>,
}

impl<'a> Ctx<'a> {
    pub fn register_func(&mut self, func_name: &'a str, func: &'a impl ExternCallable<'a>) {
        self.extend_local(
            func_name,
            Val::Func(Func::Extern(ExternFunc {
                name: func_name,
                body: func,
            })),
        );
    }

    pub fn extend_local(&mut self, binding_name: &'a str, val: Val<'a>) {
        self.bindings.push((binding_name, val));
    }

    pub fn get(&self, binding_name: &'a str) -> Option<&Val<'a>> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| *name == binding_name)
            .map(|(_, v)| v)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("error during call to `{0}`: {1:?}")]
    CallError(String, CallError),
    #[error("trying to call a value that is not a function `{0}`")]
    NotAFunction(String),
    #[error("invalid reference `{0}`")]
    InvalidReference(String),
    #[error("expected a conditional in the if expression")]
    NotAConditional,
    #[error("invalid field `{0}`")]
    InvalidField(String),
    #[error("trying to access the field of a value that is not a named tuple")]
    NotANamedTuple,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<'a> {
    Ref(&'a str),
    NewPrimitive(Primitive),
    NewNamedTuple(HashMap<&'a str, Expr<'a>>),
    NewOrderedTuple(Vec<Expr<'a>>),
    NewFunc {
        arg_pattern: Option<Pattern<'a>>,
        body: Box<Expr<'a>>,
    },
    Block {
        exprs: Vec<Expr<'a>>,
    },
    Call {
        func_name: &'a str,
        arg: Box<Expr<'a>>,
    },
    Let {
        name: &'a str,
        rhs: Box<Expr<'a>>,
    },
    If {
        cond: Box<Expr<'a>>,
        main_branch: Box<Expr<'a>>,
        else_branch: Option<Box<Expr<'a>>>,
    },
    Access {
        lhs: Box<Expr<'a>>,
        field_name: &'a str,
    },
}

impl<'a> Expr<'a> {
    pub fn eval(self, ctx: &mut Ctx<'a>) -> Result<Val<'a>, EvalError> {
        match self {
            Expr::Ref(token) => match ctx.get(token) {
                Some(v) => Ok(v.clone()),
                None => Err(EvalError::InvalidReference(token.into())),
            },
            Expr::NewPrimitive(p) => Ok(Val::Primitive(p)),
            Expr::NewOrderedTuple(exprs) => {
                let mut eval_exprs = Vec::new();
                for expr in exprs {
                    eval_exprs.push(expr.eval(ctx)?);
                }
                Ok(OrderedTuple(eval_exprs).into())
            }
            Expr::NewNamedTuple(pairs) => {
                let mut eval_pairs = HashMap::new();
                for (k, v) in pairs {
                    eval_pairs.insert(k, v.eval(ctx)?);
                }
                Ok(NamedTuple(eval_pairs).into())
            }
            Expr::NewFunc { arg_pattern, body } => Ok(Val::Func(Func::Intern(InternFunc {
                arg_pattern,
                body: *body,
                captured_ctx: ctx.clone(),
            }))),
            Expr::Access { lhs, field_name } => {
                let lhs = lhs.eval(ctx)?;
                let lhs = lhs
                    .try_as_tuple()
                    .and_then(|t| t.try_as_named())
                    .ok_or(EvalError::NotANamedTuple)?;
                let field = lhs
                    .get(field_name)
                    .ok_or(EvalError::InvalidField(field_name.into()))?;
                Ok(field.clone())
            }
            Expr::Call { func_name, arg } => match ctx.get(func_name).cloned() {
                Some(Val::Func(func)) => func
                    .call(Some(arg.eval(ctx)?))
                    .map_err(|err| EvalError::CallError(func_name.into(), err)),
                Some(_) => Err(EvalError::NotAFunction(func_name.into())),
                None => Err(EvalError::InvalidReference(func_name.into())),
            },
            Expr::Block { mut exprs } => {
                if let Some(last) = exprs.pop() {
                    let mut ext_ctx = ctx.clone();
                    for expr in exprs {
                        expr.eval(&mut ext_ctx)?;
                    }
                    last.eval(&mut ext_ctx)
                } else {
                    Ok(().into())
                }
            }
            Expr::If {
                cond,
                main_branch,
                else_branch,
            } => {
                if cond
                    .eval(ctx)?
                    .try_as_primitive()
                    .and_then(|p| p.try_as_bool())
                    .ok_or(EvalError::NotAConditional)?
                {
                    main_branch.eval(ctx)
                } else if let Some(else_branch) = else_branch {
                    else_branch.eval(ctx)
                } else {
                    Ok(().into())
                }
            }
            Expr::Let { name, rhs } => {
                let rhs = rhs.eval(ctx)?;
                ctx.extend_local(name, rhs.clone());
                Ok(rhs)
            }
        }
    }
}
