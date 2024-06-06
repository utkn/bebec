use itertools::Itertools;

use super::{Val, ValType};

#[derive(Debug, Clone, thiserror::Error)]
#[error("cannot coerce {0:?} to {1:?}")]
pub struct CoercionError(String, String);

pub fn try_coerce<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    mut from_val: Option<&mut Val<'a>>,
) -> Result<ValType<'a>, CoercionError> {
    if let Some(from_val) = from_val.as_ref() {
        debug_assert_eq!(&from_val.get_type(), from_type);
    }
    if from_type == to_type {
        return Ok(to_type.clone());
    }
    if let Some(coerced_type) = try_coerce_unwrap(from_type, to_type, from_val.as_deref_mut()) {
        return Ok(coerced_type);
    }
    if let Some(coerced_type) = try_coerce_by_order(from_type, to_type, from_val.as_deref_mut()) {
        return Ok(coerced_type);
    }
    if let Some(coerced_type) = try_coerce_func_arg(from_type, to_type, from_val.as_deref_mut()) {
        return Ok(coerced_type);
    }
    Err(CoercionError(
        format!("{:?}", from_type),
        format!("{:?}", to_type),
    ))
}

fn try_coerce_unwrap<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    from_val: Option<&mut Val<'a>>,
) -> Option<ValType<'a>> {
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
    let coerced_type = try_coerce(
        from_type.unwrap_singular_tuple(),
        to_type,
        unwrapped_val.as_mut(),
    );
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
    match (from_type, to_type) {
        (ValType::NamedTuple(named_types), ValType::OrderedTuple(val_types))
            if named_types.len() == val_types.len() =>
        {
            let coerced_types = named_types
                .iter()
                .zip(val_types.iter())
                .flat_map(|((_, from_ty), to_ty)| try_coerce(from_ty, to_ty, None))
                .collect_vec();
            if coerced_types.len() == named_types.len() {
                if let Some(Val::NamedTuple(from_vals)) = from_val {
                    from_vals
                        .iter_mut()
                        .zip(val_types.iter())
                        .zip(coerced_types.iter())
                        .for_each(|(((_, from_val), from_type), to_type)| {
                            try_coerce(from_type, to_type, Some(from_val)).unwrap();
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
    match (from_type, to_type) {
        (ValType::Func(from_arg_type, ret_type), ValType::Func(to_arg_type, _)) => {
            if let Ok(coerced_arg_type) = try_coerce(&from_arg_type, &to_arg_type, None) {
                Some(ValType::Func(Box::new(coerced_arg_type), ret_type.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}
