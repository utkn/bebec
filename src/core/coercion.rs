use itertools::Itertools;

use super::{ExternFunc, Func, InternFunc, Pattern, Val, ValType};

#[derive(Debug, Clone, thiserror::Error)]
#[error("cannot coerce {0:?} to {1:?}")]
pub struct CoercionError(String, String);

impl<'a> ValType<'a> {
    pub fn try_coerce(
        &self,
        to_type: &ValType<'a>,
        mut self_val: Option<&mut Val<'a>>,
    ) -> Result<ValType<'a>, CoercionError> {
        debug_assert!(self_val
            .as_ref()
            .map(|v| &v.get_type() == self)
            .unwrap_or(true));
        if self == to_type {
            return Ok(to_type.clone());
        }
        if let Some(coerced_type) = try_coerce_unwrap(self, to_type, self_val.as_deref_mut()) {
            return Ok(coerced_type);
        }
        if let Some(coerced_type) = try_coerce_by_order(self, to_type, self_val.as_deref_mut()) {
            return Ok(coerced_type);
        }
        if let Some(coerced_type) = try_coerce_func_arg(self, to_type, self_val.as_deref_mut()) {
            return Ok(coerced_type);
        }
        Err(CoercionError(
            format!("{:?}", self),
            format!("{:?}", to_type),
        ))
    }
}

fn try_coerce_unwrap<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    from_val: Option<&mut Val<'a>>,
) -> Option<ValType<'a>> {
    debug_assert!(from_val
        .as_ref()
        .map(|v| &v.get_type() == from_type)
        .unwrap_or(true));
    // If the type cannot be unwrapped, this coercion will never work.
    if from_type.unwrap_singular_tuple() == from_type {
        return None;
    }
    // Unwrap the value (if it exists)
    let mut unwrapped_val = from_val
        .as_deref()
        .cloned()
        .map(|v| v.unwrap_singular_tuple());
    // Perform coercion on the unwrapped value (from the unwrapped type)
    let coerced_type = from_type
        .unwrap_singular_tuple()
        .try_coerce(to_type, unwrapped_val.as_mut());
    if let Ok(coerced_type) = coerced_type {
        if let (Some(unwrapped_val), Some(from_val)) = (unwrapped_val, from_val) {
            _ = std::mem::replace(from_val, unwrapped_val);
        }
        Some(coerced_type)
    } else {
        None
    }
}

fn try_coerce_by_order<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    from_val: Option<&mut Val<'a>>,
) -> Option<ValType<'a>> {
    debug_assert!(from_val
        .as_ref()
        .map(|v| &v.get_type() == from_type)
        .unwrap_or(true));
    match (from_type, to_type) {
        (ValType::NamedTuple(named_types), ValType::OrderedTuple(val_types))
            if named_types.len() == val_types.len() =>
        {
            let coerced_types = named_types
                .iter()
                .zip(val_types.iter())
                .flat_map(|((_, from_ty), to_ty)| from_ty.try_coerce(to_ty, None))
                .collect_vec();
            if coerced_types.len() == named_types.len() {
                if let Some(Val::NamedTuple(from_vals)) = from_val {
                    from_vals
                        .iter_mut()
                        .zip(val_types.iter())
                        .zip(coerced_types.iter())
                        .for_each(|(((_, from_val), from_type), to_type)| {
                            from_type.try_coerce(to_type, Some(from_val)).unwrap();
                        });
                }
                Some(ValType::OrderedTuple(coerced_types))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn try_coerce_func_arg<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    from_val: Option<&mut Val<'a>>,
) -> Option<ValType<'a>> {
    debug_assert!(from_val
        .as_ref()
        .map(|v| &v.get_type() == from_type)
        .unwrap_or(true));
    match (from_type, to_type) {
        (ValType::Func(from_arg_type, ret_type), ValType::Func(to_arg_type, _)) => {
            if let Ok(coerced_arg_type) = from_arg_type.try_coerce(&to_arg_type, None) {
                match from_val {
                    Some(Val::Func(..)) => {
                        Some(ValType::Func(Box::new(coerced_arg_type), ret_type.clone()))
                    }
                    _ => None,
                }
            } else {
                None
            }
        }
        _ => None,
    }
}
