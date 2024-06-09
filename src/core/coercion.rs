use super::{ExternFunc, Func, InternFunc, Val, ValType};

#[derive(Debug, Clone, thiserror::Error)]
#[error("cannot coerce {from_type} to {to_type}")]
pub struct CoercionError {
    from_type: String,
    to_type: String,
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct CoercionStrategy: u8 {
        const UNWRAP = 1;
        const INTRA_TUPLE = 1 << 1;
        const INTER_TUPLE_TO_ORDERED = 1 << 2;
        const INTER_TUPLE_TO_NAMED = 1 << 3;
        const INTER_FUNC = 1 << 4;
    }
}

impl CoercionStrategy {
    pub fn let_pattern() -> CoercionStrategy {
        CoercionStrategy::UNWRAP | CoercionStrategy::INTRA_TUPLE | CoercionStrategy::INTER_FUNC
    }

    pub fn arg_pattern() -> CoercionStrategy {
        CoercionStrategy::let_pattern() | CoercionStrategy::INTER_TUPLE_TO_NAMED
    }
}

pub fn try_coerce<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    mut from_val: Option<&mut Val<'a>>,
    strategy: CoercionStrategy,
) -> Result<ValType<'a>, CoercionError> {
    if let Some(from_val) = from_val.as_ref() {
        debug_assert_eq!(&from_val.get_type(), from_type);
    }
    if from_type == to_type {
        return Ok(to_type.clone());
    }
    if strategy.contains(CoercionStrategy::UNWRAP) {
        if let Some(coerced_type) =
            try_coerce_unwrap(from_type, to_type, from_val.as_deref_mut(), strategy)
        {
            return Ok(coerced_type);
        }
    }
    if strategy.contains(CoercionStrategy::INTRA_TUPLE) {
        if let Some(coerced_type) =
            try_coerce_intra_tuple(from_type, to_type, from_val.as_deref_mut(), strategy)
        {
            return Ok(coerced_type);
        }
    }
    if strategy.contains(CoercionStrategy::INTER_TUPLE_TO_ORDERED) {
        if let Some(coerced_type) =
            try_coerce_inter_tuple_to_ordered(from_type, to_type, from_val.as_deref_mut(), strategy)
        {
            return Ok(coerced_type);
        }
    }
    if strategy.contains(CoercionStrategy::INTER_TUPLE_TO_NAMED) {
        if let Some(coerced_type) =
            try_coerce_inter_tuple_to_named(from_type, to_type, from_val.as_deref_mut(), strategy)
        {
            return Ok(coerced_type);
        }
    }
    if strategy.contains(CoercionStrategy::INTER_FUNC) {
        if let Some(coerced_type) =
            try_coerce_inter_func(from_type, to_type, from_val.as_deref_mut())
        {
            return Ok(coerced_type);
        }
    }
    Err(CoercionError {
        from_type: from_type.to_string(),
        to_type: to_type.to_string(),
    })
}

fn try_batch_coerce_types<'a: 'b, 'b>(
    from_types: impl IntoIterator<Item = &'b ValType<'a>> + 'b + Clone,
    to_types: impl IntoIterator<Item = &'b ValType<'a>> + 'b + Clone,
    from_vals: Option<impl IntoIterator<Item = &'b mut Val<'a>> + 'b>,
    strategy: CoercionStrategy,
) -> Result<Vec<ValType<'a>>, CoercionError> {
    let mut coerced_types = Vec::new();
    for (from_ty, to_ty) in from_types
        .clone()
        .into_iter()
        .zip(to_types.clone().into_iter())
    {
        coerced_types.push(try_coerce(from_ty, to_ty, None, strategy)?);
    }
    if let Some(from_vals) = from_vals {
        for ((from_ty, to_ty), to_val) in from_types.into_iter().zip(to_types).zip(from_vals) {
            try_coerce(from_ty, to_ty, Some(to_val), strategy)?;
        }
    }
    Ok(coerced_types)
}

fn try_coerce_unwrap<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    from_val: Option<&mut Val<'a>>,
    strategy: CoercionStrategy,
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
        strategy,
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

fn try_coerce_intra_tuple<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    mut from_val: Option<&mut Val<'a>>,
    strategy: CoercionStrategy,
) -> Option<ValType<'a>> {
    match (from_type, to_type) {
        (ValType::NamedTuple(from_types), ValType::NamedTuple(to_types))
            if from_types.len() == to_types.len()
                && from_types
                    .iter()
                    .all(|(name1, _)| to_types.iter().any(|(name2, _)| name1 == name2)) =>
        {
            let coerced_types = try_batch_coerce_types(
                from_types.iter().map(|(_, ty)| ty),
                to_types.iter().map(|(_, ty)| ty),
                from_val
                    .as_deref_mut()
                    .and_then(|v| v.try_as_ordered_tuple_mut())
                    .map(|tpl| tpl.iter_mut()),
                strategy,
            );
            match coerced_types {
                Ok(coerced_types) => Some(ValType::NamedTuple(
                    coerced_types
                        .into_iter()
                        .zip(from_types)
                        .map(|(ty, (name, _))| (*name, ty))
                        .collect(),
                )),
                Err(_) => None,
            }
        }
        (ValType::OrderedTuple(from_types), ValType::OrderedTuple(to_types))
            if from_types.len() == to_types.len() =>
        {
            let coerced_types = try_batch_coerce_types(
                from_types.iter(),
                to_types.iter(),
                from_val
                    .as_deref_mut()
                    .and_then(|v| v.try_as_ordered_tuple_mut())
                    .map(|tpl| tpl.iter_mut()),
                strategy,
            );
            match coerced_types {
                Ok(coerced_types) => Some(ValType::OrderedTuple(coerced_types)),
                Err(_) => None,
            }
        }
        _ => None,
    }
}

fn try_coerce_inter_tuple_to_ordered<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    mut from_val: Option<&mut Val<'a>>,
    strategy: CoercionStrategy,
) -> Option<ValType<'a>> {
    match (from_type, to_type) {
        (ValType::NamedTuple(named_types), ValType::OrderedTuple(val_types))
            if named_types.len() == val_types.len() =>
        {
            let coerced_types = try_batch_coerce_types(
                named_types.iter().map(|(_, ty)| ty),
                val_types.iter(),
                from_val
                    .as_deref_mut()
                    .and_then(|v| v.try_as_named_tuple_mut())
                    .map(|tpl| tpl.iter_mut().map(|(_, ty)| ty)),
                strategy,
            );
            match coerced_types {
                Ok(coerced_types) => Some(ValType::OrderedTuple(coerced_types)),
                Err(_) => None,
            }
        }
        _ => None,
    }
}

fn try_coerce_inter_tuple_to_named<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    mut from_val: Option<&mut Val<'a>>,
    strategy: CoercionStrategy,
) -> Option<ValType<'a>> {
    match (from_type, to_type) {
        (ValType::OrderedTuple(val_types), ValType::NamedTuple(named_types))
            if named_types.len() == val_types.len() =>
        {
            let coerced_types = try_batch_coerce_types(
                val_types.iter(),
                named_types.iter().map(|(_, ty)| ty),
                from_val
                    .as_deref_mut()
                    .and_then(|v| v.try_as_ordered_tuple_mut())
                    .map(|tpl| tpl.iter_mut()),
                strategy,
            );
            match coerced_types {
                Ok(coerced_types) => Some(ValType::NamedTuple(
                    coerced_types
                        .into_iter()
                        .zip(named_types)
                        .map(|(ty, (name, _))| (*name, ty))
                        .collect(),
                )),
                Err(_) => None,
            }
        }
        _ => None,
    }
}

fn try_coerce_inter_func<'a>(
    from_type: &ValType<'a>,
    to_type: &ValType<'a>,
    from_val: Option<&mut Val<'a>>,
) -> Option<ValType<'a>> {
    match (from_type, to_type) {
        (ValType::Func(from_arg_type, from_ret_type), ValType::Func(to_arg_type, to_ret_type))
            if from_ret_type == to_ret_type =>
        {
            if let Ok(coerced_arg_type) = try_coerce(
                &from_arg_type,
                &to_arg_type,
                None,
                CoercionStrategy::INTER_TUPLE_TO_ORDERED,
            ) {
                match from_val {
                    Some(Val::Func(Func::Extern(ExternFunc { arg_type, .. })))
                    | Some(Val::Func(Func::Intern(InternFunc { arg_type, .. }))) => {
                        _ = std::mem::replace(arg_type, coerced_arg_type.clone());
                    }
                    Some(Val::Uninit(ValType::Func(arg_type, _))) => {
                        _ = std::mem::replace(arg_type.as_mut(), coerced_arg_type.clone());
                    }
                    _ => {}
                }
                Some(ValType::Func(
                    Box::new(coerced_arg_type),
                    from_ret_type.clone(),
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}
