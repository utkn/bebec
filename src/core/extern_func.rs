use std::error::Error;

use super::{Pattern, Val, ValType};

#[derive(Debug, thiserror::Error)]
pub enum ExternCallError {
    #[error("no arguments provided")]
    NoArgsProvided,
    #[error("unexpected argument")]
    TypeError,
    #[error("{0:?}")]
    Any(Box<dyn Error>),
}

pub trait ExternCallable<'a> {
    fn call(&self, arg: Val<'a>) -> Result<Val<'a>, ExternCallError>;
}

impl<'a, T> ExternCallable<'a> for T
where
    T: Fn(Val<'a>) -> Result<Val<'a>, ExternCallError>,
{
    fn call(&self, arg: Val<'a>) -> Result<Val<'a>, ExternCallError> {
        (self)(arg)
    }
}

#[derive(Clone)]
pub struct ExternFunc<'a> {
    pub(super) arg_pattern: Pattern<'a>,
    pub(super) ret_type: ValType<'a>,
    pub(super) func_name: &'a str,
    pub(super) body: &'a dyn ExternCallable<'a>,
}

impl<'a> std::cmp::Eq for ExternFunc<'a> {}

impl<'a> std::cmp::PartialEq for ExternFunc<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.func_name == other.func_name
    }
}

impl<'a> std::fmt::Debug for ExternFunc<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.func_name)
    }
}

macro_rules! extern_func {
    (( $( $ids:ident : $ts: ty ),+ ) => $body:expr) => {
        |val: Val<'_>| -> Result<Val<'_>, ExternCallError> {
            let ($($ids),+,): ($($ts),+,) = val
                .try_destruct_tuple([
                    $(stringify!($ids)),+
                ])
                .ok_or(ExternCallError::TypeError)?;
            Ok($body.into())
        }
    };
}

pub(crate) use extern_func;
