mod coercion;
mod context;
mod expression;
mod extern_func;
mod pattern;

use std::collections::{BTreeMap, HashMap};

use crate::types::Representible;

pub use coercion::*;
pub use context::ValCtx;
pub use expression::{EvalError, Expr, Typed, Untyped};
pub(crate) use extern_func::{extern_func, ExternCallError, ExternCallable, ExternFunc};
pub use pattern::{DestructError, Pattern};

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

impl<'a> OrderedTuple<'a> {
    /// Returns the type of the ordered tuple.
    pub fn get_type(&self) -> ValType<'a> {
        ValType::OrderedTuple(self.0.iter().map(Val::get_type).collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedTuple<'a>(pub Vec<(&'a str, Val<'a>)>);

impl<'a> FromIterator<(&'a str, Val<'a>)> for NamedTuple<'a> {
    fn from_iter<T: IntoIterator<Item = (&'a str, Val<'a>)>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for NamedTuple<'a> {
    type Item = (&'a str, Val<'a>);

    type IntoIter = <Vec<(&'a str, Val<'a>)> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> NamedTuple<'a> {
    pub fn iter(&self) -> impl Iterator<Item = &(&'a str, Val<'a>)> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut (&'a str, Val<'a>)> {
        self.0.iter_mut()
    }

    pub fn remove<'b>(&mut self, name: &'b str) -> Option<Val<'a>> {
        if let Some(idx) = self.0.iter().position(|(k, _)| k == &name) {
            Some(self.0.remove(idx).1)
        } else {
            None
        }
    }
    /// Returns the type of the named tuple.
    pub fn get_type(&self) -> ValType<'a> {
        ValType::NamedTuple(self.0.iter().map(|(k, v)| (*k, v.get_type())).collect())
    }

    pub fn as_ordered<'b>(
        mut self,
        ordered_names: impl IntoIterator<Item = &'b str>,
    ) -> Option<OrderedTuple<'a>> {
        let mut vals = Vec::new();
        for name in ordered_names {
            vals.push(self.remove(name)?);
        }
        Some(vals.into_iter().collect())
    }

    pub fn get(&self, field_name: &str) -> Option<&Val<'a>> {
        self.0
            .iter()
            .find(|(k, _)| k == &field_name)
            .map(|(_, v)| v)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, strum::EnumTryAs, strum::EnumIs)]
pub enum Primitive {
    Uint(usize),
    Char(char),
    Bool(bool),
    String(String),
}

impl Primitive {
    /// Returns the type of the primitive.
    pub fn get_type<'a>(&self) -> ValType<'a> {
        match self {
            Primitive::Uint(_) => ValType::Uint,
            Primitive::Bool(_) => ValType::Bool,
            Primitive::Char(_) => ValType::Char,
            Primitive::String(_) => ValType::String,
        }
    }
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
pub struct InternFunc<'a, T> {
    ret_type: ValType<'a>,
    arg_pattern: Pattern<'a>,
    captured_ctx: ValCtx<'a>,
    body: Expr<'a, T>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Func<'a, T> {
    Intern(InternFunc<'a, T>),
    Extern(ExternFunc<'a>),
}

impl<'a> Func<'a, Typed<'a>> {
    pub fn arg_pattern(&self) -> &Pattern<'a> {
        match self {
            Func::Intern(InternFunc { arg_pattern, .. })
            | Func::Extern(ExternFunc { arg_pattern, .. }) => arg_pattern,
        }
    }
    pub fn call(&self, arg: Val<'a>) -> Result<Val<'a>, CallError> {
        match self {
            Func::Intern(InternFunc {
                arg_pattern,
                captured_ctx,
                body,
                ..
            }) => {
                let mut func_ctx = captured_ctx.clone();
                arg_pattern
                    .destruct_val(arg, &mut func_ctx)
                    .map_err(CallError::from)?;
                body.clone()
                    .eval(&mut func_ctx)
                    .map_err(|err| CallError::FuncEvalError(Box::new(err)))
            }
            Func::Extern(ExternFunc { body, .. }) => body.call(arg).map_err(CallError::from),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, strum::EnumTryAs, strum::EnumIs)]
pub enum Val<'a> {
    Primitive(Primitive),
    Func(Func<'a, Typed<'a>>),
    OrderedTuple(OrderedTuple<'a>),
    NamedTuple(NamedTuple<'a>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, strum::EnumTryAs)]
pub enum ValType<'a> {
    Uint,
    Char,
    Bool,
    String,
    OrderedTuple(Vec<ValType<'a>>),
    NamedTuple(Vec<(&'a str, ValType<'a>)>),
    Func(Box<ValType<'a>>, Box<ValType<'a>>),
}

impl<'a> ValType<'a> {
    /// Returns the type of an empty ordered tuple.
    pub fn nil() -> Self {
        ValType::OrderedTuple(vec![])
    }

    pub fn unwrap_singular_tuple(&self) -> &Self {
        match self {
            // Coerce a tuple with a single element into the inner value
            ValType::OrderedTuple(t) if t.len() == 1 => t.get(0).unwrap(),
            _ => self,
        }
    }
}

impl<'a> Val<'a> {
    /// Returns a `nil` value, i.e., an empty ordered tuple.
    pub fn nil() -> Self {
        Val::OrderedTuple(OrderedTuple(Default::default()))
    }

    /// Returns true iff this value is of type `nil`.
    pub fn is_nil(&self) -> bool {
        match self {
            Val::OrderedTuple(OrderedTuple(vals)) if vals.is_empty() => true,
            _ => false,
        }
    }

    /// Returns the type of the value.
    pub fn get_type(&self) -> ValType<'a> {
        match self {
            Val::Primitive(p) => p.get_type(),
            Val::OrderedTuple(t) => t.get_type(),
            Val::NamedTuple(t) => t.get_type(),
            Val::Func(Func::Intern(InternFunc {
                arg_pattern,
                ret_type,
                ..
            }))
            | Val::Func(Func::Extern(ExternFunc {
                arg_pattern,
                ret_type,
                ..
            })) => ValType::Func(Box::new(arg_pattern.to_type()), Box::new(ret_type.clone())),
        }
    }

    pub fn unwrap_singular_tuple(self) -> Self {
        match self {
            // Coerce a tuple with a single element into the inner value
            Val::OrderedTuple(OrderedTuple(mut t)) if t.len() == 1 => t.remove(0),
            _ => self,
        }
    }

    /// If the value is an ordered tuple, tries to convert it to `T`. However, if the value is a named tuple, first converts it into an ordered tuple with `ordered_names` before converting to `T`.
    /// Returns `None` if `self` is not a tuple, or the conversion from tuples fail.
    pub fn try_destruct_tuple<T>(
        self,
        ordered_names: impl IntoIterator<Item = &'a str>,
    ) -> Option<T>
    where
        T: Representible<'a>,
    {
        let ordered = if self.is_named_tuple() {
            self.try_as_named_tuple()
                .unwrap()
                .as_ordered(ordered_names)?
        } else if let Some(tpl) = self.try_as_ordered_tuple() {
            tpl
        } else {
            return None;
        };
        T::try_from_val(Val::OrderedTuple(ordered))
    }
}
