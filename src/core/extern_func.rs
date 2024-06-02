use std::error::Error;

use super::Val;

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
    fn call(&self, arg: Option<Val<'a>>) -> Result<Val<'a>, ExternCallError>;
}

impl<'a, T> ExternCallable<'a> for T
where
    T: Fn(Option<Val<'a>>) -> Result<Val<'a>, ExternCallError>,
{
    fn call(&self, arg: Option<Val<'a>>) -> Result<Val<'a>, ExternCallError> {
        (self)(arg)
    }
}

#[derive(Clone)]
pub struct ExternFunc<'a> {
    pub(super) name: &'a str,
    pub(super) body: &'a dyn ExternCallable<'a>,
}

impl<'a> std::cmp::Eq for ExternFunc<'a> {}

impl<'a> std::cmp::PartialEq for ExternFunc<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<'a> std::fmt::Debug for ExternFunc<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name)
    }
}

macro_rules! extern_func {
    (( $( $ids:ident : $ts: ty ),+ ) => $body:expr) => {
        |val: Option<Val<'_>>| -> Result<Val<'_>, ExternCallError> {
            let val = val.ok_or(ExternCallError::NoArgsProvided)?;
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
