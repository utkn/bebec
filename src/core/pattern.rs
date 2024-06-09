use super::{try_coerce, CoercionError, CoercionStrategy, OrderedTuple, Val, ValCtx, ValType};

#[derive(Debug, Clone, thiserror::Error)]
pub enum DestructError {
    #[error("coercion error: {0:?}")]
    CoercionError(#[from] CoercionError),
    #[error("unmatched pattern (pattern `{pat}`, value `{val}`)")]
    UnmatchedPattern { pat: String, val: String },
    #[error("pattern requires the field `{0}` to be present")]
    UnsatisfiedName(String),
    #[error("no corresponding binding exists on the pattern for the named tuple")]
    NoCorrespondingBinding,
}

#[derive(Debug, Clone, thiserror::Error)]
#[error("could not build a pattern from the type {0}")]
pub struct PatternBuildError(String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<'a> {
    Binding(&'a str, Option<ValType<'a>>),
    PatternList(Vec<Pattern<'a>>),
}

impl<'a> FromIterator<(&'a str, ValType<'a>)> for Pattern<'a> {
    fn from_iter<T: IntoIterator<Item = (&'a str, ValType<'a>)>>(iter: T) -> Self {
        Pattern::PatternList(
            iter.into_iter()
                .map(|(k, v)| Pattern::Binding(k, Some(v)))
                .collect(),
        )
    }
}

impl<'a> FromIterator<(&'a str, Option<ValType<'a>>)> for Pattern<'a> {
    fn from_iter<T: IntoIterator<Item = (&'a str, Option<ValType<'a>>)>>(iter: T) -> Self {
        Pattern::PatternList(
            iter.into_iter()
                .map(|(k, v)| Pattern::Binding(k, v))
                .collect(),
        )
    }
}

impl<'a> Pattern<'a> {
    pub fn destruct_val(
        &self,
        val: Val<'a>,
        val_ctx: &mut ValCtx<'a>,
        coercion_strategy: CoercionStrategy,
    ) -> Result<(), DestructError> {
        match (self, val) {
            (_, Val::Uninit(ValType::OrderedTuple(types))) => {
                // Partially instantiate the uninitialized value to be able to match against the inner values.
                self.destruct_val(
                    Val::OrderedTuple(types.iter().map(ValType::to_uninit).collect()),
                    val_ctx,
                    coercion_strategy,
                )
            }
            (_, Val::Uninit(ValType::NamedTuple(types))) => {
                // Partially instantiate the uninitialized value to be able to match against the inner values.
                self.destruct_val(
                    Val::NamedTuple(types.iter().map(|(k, v)| (*k, v.to_uninit())).collect()),
                    val_ctx,
                    coercion_strategy,
                )
            }
            (Pattern::Binding(name, ty), val) => destruct_val_single(
                name,
                ty.as_ref(),
                &val.get_type(),
                Some((val, val_ctx)),
                coercion_strategy,
            ),
            (Pattern::PatternList(pats), Val::OrderedTuple(OrderedTuple(vals)))
                if pats.len() == vals.len() =>
            {
                for (pat, val) in pats.iter().zip(vals.into_iter()) {
                    pat.destruct_val(val, val_ctx, coercion_strategy)?;
                }
                Ok(())
            }
            (Pattern::PatternList(pats), Val::NamedTuple(mut pairs))
                if pats.len() == pairs.len() =>
            {
                for pat in pats {
                    let Pattern::Binding(name, ty) = pat else {
                        return Err(DestructError::NoCorrespondingBinding);
                    };
                    let field = pairs
                        .remove(name)
                        .ok_or(DestructError::UnsatisfiedName(name.to_string()))?;
                    destruct_val_single(
                        name,
                        ty.as_ref(),
                        &field.get_type(),
                        Some((field, val_ctx)),
                        coercion_strategy,
                    )?;
                }
                Ok(())
            }
            (Pattern::PatternList(pats), val) if pats.len() == 1 => pats
                .get(0)
                .unwrap()
                .destruct_val(val, val_ctx, coercion_strategy),
            (pat, val) => Err(DestructError::UnmatchedPattern {
                pat: format!("{:?}", pat),
                val: format!("{:?}", val),
            }),
        }
    }
}

fn destruct_val_single<'a>(
    pat_name: &'a str,
    pat_type: Option<&ValType<'a>>,
    val_type: &ValType<'a>,
    to_extend: Option<(Val<'a>, &mut ValCtx<'a>)>,
    coercion_strategy: CoercionStrategy,
) -> Result<(), DestructError> {
    if let Some((mut val, val_ctx)) = to_extend {
        if let Some(pat_type) = pat_type {
            try_coerce(val_type, pat_type, Some(&mut val), coercion_strategy)?;
        }
        val_ctx.extend(pat_name, val);
        Ok(())
    } else {
        if let Some(pat_type) = pat_type {
            try_coerce(val_type, pat_type, None, coercion_strategy)?;
        }
        Ok(())
    }
}
