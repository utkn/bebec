use super::{context::TypeCtx, CoercionError, NamedTuple, OrderedTuple, Val, ValCtx, ValType};

#[derive(Debug, Clone, thiserror::Error)]
pub enum DestructError {
    #[error("coercion error: {0:?}")]
    CoercionError(#[from] CoercionError),
    #[error("unmatched pattern (pattern `{0}`, value `{1}`)")]
    UnmatchedPattern(String, String),
    #[error("pattern requires the field `{0}` to be present")]
    UnsatisfiedName(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<'a> {
    Single(&'a str, ValType<'a>),
    OrderedTuple(Vec<Pattern<'a>>),
    NamedTuple(Vec<(&'a str, ValType<'a>)>),
}

impl<'a> Pattern<'a> {
    /// Constructs a pattern from the given type. It is guaranteed that the generated type will match a value of the given type.
    pub fn from_type(val_type: &ValType<'a>) -> Self {
        const PLACEHOLDER_NAME: &str = "@";
        match val_type {
            ValType::OrderedTuple(tpl) => {
                Pattern::OrderedTuple(tpl.iter().map(Pattern::from_type).collect())
            }
            ValType::NamedTuple(tpl) => {
                Pattern::NamedTuple(tpl.iter().map(|(k, v)| (*k, v.clone())).collect())
            }
            t => Pattern::Single(PLACEHOLDER_NAME, t.clone()),
        }
    }

    /// Converts a pattern to the most general type that would match this pattern.
    pub fn to_type(&self) -> ValType<'a> {
        match self {
            Pattern::Single(_, ty) => ty.clone(),
            Pattern::OrderedTuple(pats) => {
                ValType::OrderedTuple(pats.iter().map(Pattern::to_type).collect())
            }
            Pattern::NamedTuple(pats) => ValType::NamedTuple(pats.iter().cloned().collect()),
        }
    }

    pub fn destruct_types(&self, type_ctx: &mut TypeCtx<'a>) {
        match self {
            Pattern::Single(name, ty) => type_ctx.extend(name, ty.clone()),
            Pattern::OrderedTuple(pats) => pats.iter().for_each(|p| p.destruct_types(type_ctx)),
            Pattern::NamedTuple(pats) => pats
                .iter()
                .for_each(|(name, ty)| type_ctx.extend(name, ty.clone())),
        }
    }

    pub fn destruct_val(
        &self,
        val: Val<'a>,
        val_ctx: &mut ValCtx<'a>,
    ) -> Result<(), DestructError> {
        match (self, val) {
            (Pattern::Single(name, ty), val) => {
                destruct_val_single(name, ty, &val.get_type(), Some((val, val_ctx)))
            }
            (Pattern::OrderedTuple(pats), Val::OrderedTuple(OrderedTuple(vals)))
                if pats.len() == vals.len() =>
            {
                for (pat, val) in pats.iter().zip(vals.into_iter()) {
                    pat.destruct_val(val, val_ctx)?;
                }
                Ok(())
            }
            (Pattern::NamedTuple(pats), Val::OrderedTuple(OrderedTuple(vals)))
                if pats.len() == vals.len() =>
            {
                for ((name, ty), val) in pats.iter().zip(vals.into_iter()) {
                    destruct_val_single(name, ty, &val.get_type(), Some((val, val_ctx)))?;
                }
                Ok(())
            }
            (Pattern::NamedTuple(pats), Val::NamedTuple(mut pairs))
                if pats.len() == pairs.len() =>
            {
                for (name, ty) in pats {
                    let field = pairs
                        .remove(name)
                        .ok_or(DestructError::UnsatisfiedName(name.to_string()))?;
                    destruct_val_single(name, ty, &field.get_type(), Some((field, val_ctx)))?;
                }
                Ok(())
            }
            (pat, val) => Err(DestructError::UnmatchedPattern(
                format!("{:?}", pat),
                format!("{:?}", val),
            )),
        }
    }
}

fn destruct_val_single<'a>(
    pat_name: &'a str,
    pat_type: &ValType<'a>,
    val_type: &ValType<'a>,
    to_extend: Option<(Val<'a>, &mut ValCtx<'a>)>,
) -> Result<(), DestructError> {
    if let Some((mut val, val_ctx)) = to_extend {
        val_type.try_coerce(pat_type, Some(&mut val))?;
        val_ctx.extend(pat_name, val);
        Ok(())
    } else {
        val_type.try_coerce(pat_type, None)?;
        Ok(())
    }
}
