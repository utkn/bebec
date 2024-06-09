use super::{
    context::TypeCtx, try_coerce, CallError, CoercionError, CoercionStrategy, DestructError, Func,
    InternFunc, NamedTuple, OrderedTuple, Pattern, PatternBuildError, Primitive, Val, ValCtx,
    ValType,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Untyped;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Typed<'a>(ValType<'a>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<'a, T> {
    Ref(T, &'a str),
    NewPrimitive(T, Primitive),
    NewNamedTuple(T, Vec<(&'a str, Self)>),
    NewOrderedTuple(T, Vec<Self>),
    NewFunc {
        expr_type: T,
        params: Vec<(&'a str, ValType<'a>)>,
        body: Box<Self>,
    },
    Block {
        expr_type: T,
        exprs: Vec<Self>,
    },
    Call {
        expr_type: T,
        func_name: &'a str,
        arg: Box<Self>,
    },
    Let {
        expr_type: T,
        lhs: Pattern<'a>,
        rhs: Box<Self>,
    },
    If {
        expr_type: T,
        cond: Box<Self>,
        main_branch: Box<Self>,
        else_branch: Option<Box<Self>>,
    },
    Access {
        expr_type: T,
        lhs: Box<Self>,
        field_name: &'a str,
    },
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("invalid reference `{0}`")]
    InvalidRef(String),
    #[error("expected `{0}` to be a function, but it has a type {1}")]
    NotAFunction(String, String),
    #[error("if branches must return the same value, but the main branch returns {main_type}, whereas the else branch returns {else_type}")]
    InconsistentIfBranches {
        main_type: String,
        else_type: String,
    },
    #[error("if condition cannot be coerced to a boolean, {0:?}")]
    NotAConditional(CoercionError),
    #[error("invalid field `{0}` on a named tuple of type {1}")]
    InvalidField(String, String),
    #[error("trying to access the field of a value that is not a named tuple")]
    NotANamedTuple,
    #[error("arguments do not match on call to `{0}`: {1:?}")]
    ArgCoercionError(String, CoercionError),
    #[error("destruct error on let: {0:?}")]
    DestructLetError(DestructError),
    #[error("argument pattern cannot be trivially destructed: {0:?}")]
    MalformedArgPattern(DestructError),
}

impl<'a> Expr<'a, Untyped> {
    /// Performs type checking and turns the expression into an evaluatable state.
    pub fn to_typed(self, ctx: &mut TypeCtx<'a>) -> Result<Expr<'a, Typed<'a>>, TypeError> {
        match self {
            Expr::Ref(_, s) => Ok(Expr::Ref(
                Typed(ctx.get(s).cloned().ok_or(TypeError::InvalidRef(s.into()))?),
                s,
            )),
            Expr::NewPrimitive(_, p) => Ok(Expr::NewPrimitive(Typed(p.get_primitive_type()), p)),
            Expr::NewNamedTuple(_, tpl) => {
                let mut named_tpl_type = Vec::new();
                let mut typed_tpl = Vec::new();
                for (k, v) in tpl {
                    let typed_v = v.to_typed(ctx)?;
                    named_tpl_type.push((k, typed_v.get_expr_type()));
                    typed_tpl.push((k, typed_v));
                }
                Ok(Expr::NewNamedTuple(
                    Typed(ValType::NamedTuple(named_tpl_type)),
                    typed_tpl,
                ))
            }
            Expr::NewOrderedTuple(_, tpl) => {
                let mut ordered_tpl_type = Vec::new();
                let mut typed_tpl = Vec::new();
                for v in tpl {
                    let typed_v = v.to_typed(ctx)?;
                    ordered_tpl_type.push(typed_v.get_expr_type());
                    typed_tpl.push(typed_v);
                }
                Ok(Expr::NewOrderedTuple(
                    Typed(ValType::OrderedTuple(ordered_tpl_type)),
                    typed_tpl,
                ))
            }
            Expr::NewFunc {
                expr_type: _,
                params,
                body,
            } => {
                let mut ext_ctx = ctx.clone();
                for (name, ty) in params.clone() {
                    ext_ctx.extend(name, ty);
                }
                let typed_body = body.to_typed(&mut ext_ctx)?;
                let expr_type = ValType::Func(
                    Box::new(ValType::NamedTuple(params.clone())),
                    Box::new(typed_body.get_expr_type()),
                );
                Ok(Expr::NewFunc {
                    expr_type: Typed(expr_type),
                    params,
                    body: Box::new(typed_body),
                })
            }
            Expr::Block {
                expr_type: _,
                exprs,
            } => {
                let mut typed_exprs = Vec::new();
                let mut inner_ctx = ctx.clone();
                for expr in exprs {
                    typed_exprs.push(expr.to_typed(&mut inner_ctx)?);
                }
                let ret_type = typed_exprs
                    .last()
                    .map(Expr::get_expr_type)
                    .unwrap_or(ValType::nil());
                Ok(Expr::Block {
                    expr_type: Typed(ret_type),
                    exprs: typed_exprs,
                })
            }
            Expr::Let {
                expr_type: _,
                lhs,
                rhs,
            } => {
                let typed_rhs = rhs.to_typed(ctx)?;
                let rhs_type = typed_rhs.get_expr_type();
                let mut tmp_ctx = ValCtx::default();
                lhs.destruct_val(
                    rhs_type.to_uninit(),
                    &mut tmp_ctx,
                    CoercionStrategy::let_pattern(),
                )
                .map_err(|err| TypeError::DestructLetError(err))?;
                ctx.collect_types(tmp_ctx);
                Ok(Expr::Let {
                    expr_type: Typed(typed_rhs.get_expr_type()),
                    lhs,
                    rhs: Box::new(typed_rhs),
                })
            }
            Expr::Call {
                expr_type: _,
                func_name,
                arg,
            } => {
                let typed_arg = arg.to_typed(ctx)?;
                let (expected_arg_type, ret_type) = match ctx.get(func_name).cloned() {
                    Some(ValType::Func(arg_type, ret_type)) => (arg_type, ret_type),
                    Some(t) => {
                        return Err(TypeError::NotAFunction(
                            func_name.into(),
                            format!("{:?}", t),
                        ))
                    }
                    None => return Err(TypeError::InvalidRef(func_name.into())),
                };
                let arg_type = typed_arg.get_expr_type();
                try_coerce(
                    &arg_type,
                    &expected_arg_type,
                    None,
                    CoercionStrategy::arg_pattern(),
                )
                .map_err(|err| TypeError::ArgCoercionError(func_name.into(), err))?;
                Ok(Expr::Call {
                    expr_type: Typed(*ret_type),
                    func_name,
                    arg: Box::new(typed_arg),
                })
            }
            Expr::If {
                expr_type: _,
                cond,
                main_branch,
                else_branch,
            } => {
                let typed_cond = cond.to_typed(ctx)?;
                let cond_type = typed_cond.get_expr_type();
                try_coerce(&cond_type, &ValType::Bool, None, CoercionStrategy::UNWRAP)
                    .map_err(|err| TypeError::NotAConditional(err))?;
                let typed_main_branch = main_branch.to_typed(ctx)?;
                let typed_else_branch = if let Some(else_branch) = else_branch {
                    Some(else_branch.to_typed(ctx)?)
                } else {
                    None
                };
                let main_type = typed_main_branch.get_expr_type();
                let else_type = typed_else_branch
                    .as_ref()
                    .map(|b| b.get_expr_type())
                    .unwrap_or(ValType::nil());
                if main_type != else_type {
                    return Err(TypeError::InconsistentIfBranches {
                        main_type: main_type.to_string(),
                        else_type: else_type.to_string(),
                    });
                }
                Ok(Expr::If {
                    expr_type: Typed(main_type),
                    cond: Box::new(typed_cond),
                    main_branch: Box::new(typed_main_branch),
                    else_branch: typed_else_branch.map(|b| Box::new(b)),
                })
            }
            Expr::Access {
                expr_type: _,
                lhs,
                field_name,
            } => {
                let typed_lhs = lhs.to_typed(ctx)?;
                let lhs_type = typed_lhs
                    .get_expr_type()
                    .try_as_named_tuple()
                    .ok_or(TypeError::NotANamedTuple)?;
                let field_type = lhs_type
                    .iter()
                    .find(|(k, _)| k == &field_name)
                    .map(|(_, v)| v)
                    .ok_or(TypeError::InvalidField(
                        field_name.into(),
                        format!("{:?}", lhs_type),
                    ))?;
                Ok(Expr::Access {
                    expr_type: Typed(field_type.clone()),
                    lhs: Box::new(typed_lhs),
                    field_name,
                })
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("error during call to `{0}`: {1:?}")]
    CallError(String, CallError),
    #[error("error while destructuring: {0:?}")]
    DestructError(#[from] DestructError),
    #[error("trying to call a value that is not a function `{0}`")]
    NotAFunction(String),
    #[error("invalid reference `{0}`")]
    InvalidReference(String),
    #[error("expected a conditional in the if expression: {0:?}")]
    NotAConditional(CoercionError),
    #[error("invalid field `{0}`")]
    InvalidField(String),
    #[error("trying to access the field of a value that is not a named tuple")]
    NotANamedTuple,
    #[error("argument {0} cannot be represented as a pattern: {1:?}")]
    MalformedArg(String, PatternBuildError),
    #[error("malformed expression: {0}")]
    MalformedExpr(String),
}

impl<'a> Expr<'a, Typed<'a>> {
    pub fn get_expr_type(&self) -> ValType<'a> {
        match self {
            Expr::Ref(Typed(t), _)
            | Expr::NewPrimitive(Typed(t), _)
            | Expr::NewNamedTuple(Typed(t), _)
            | Expr::NewOrderedTuple(Typed(t), _)
            | Expr::NewFunc {
                expr_type: Typed(t),
                ..
            }
            | Expr::Block {
                expr_type: Typed(t),
                ..
            }
            | Expr::Call {
                expr_type: Typed(t),
                ..
            }
            | Expr::Let {
                expr_type: Typed(t),
                ..
            }
            | Expr::If {
                expr_type: Typed(t),
                ..
            }
            | Expr::Access {
                expr_type: Typed(t),
                ..
            } => t.clone(),
        }
    }

    pub fn eval(self, ctx: &mut ValCtx<'a>) -> Result<Val<'a>, EvalError> {
        match self {
            Expr::Ref(_, s) => match ctx.get(s) {
                Some(v) => Ok(v.clone()),
                None => Err(EvalError::InvalidReference(s.into())),
            },
            Expr::NewPrimitive(_, p) => Ok(Val::Primitive(p)),
            Expr::NewOrderedTuple(_, exprs) => {
                let mut eval_exprs = Vec::new();
                for expr in exprs {
                    eval_exprs.push(expr.eval(ctx)?);
                }
                Ok(OrderedTuple(eval_exprs).into())
            }
            Expr::NewNamedTuple(_, pairs) => {
                let mut eval_pairs = Vec::new();
                for (k, v) in pairs {
                    eval_pairs.push((k, v.eval(ctx)?));
                }
                Ok(NamedTuple(eval_pairs).into())
            }
            Expr::NewFunc {
                expr_type: Typed(ValType::Func(arg_type, ret_type)),
                params,
                body,
            } => Ok(Val::Func(Func::Intern(InternFunc {
                ret_type: *ret_type,
                arg_type: *arg_type,
                arg_pattern: Pattern::from_iter(params),
                body: *body,
                captured_ctx: ctx.clone(),
            }))),
            Expr::Access {
                expr_type: _,
                lhs,
                field_name,
            } => {
                let lhs = lhs.eval(ctx)?;
                let lhs = lhs.try_as_named_tuple().ok_or(EvalError::NotANamedTuple)?;
                let field = lhs
                    .get(field_name)
                    .ok_or(EvalError::InvalidField(field_name.into()))?;
                Ok(field.clone())
            }
            Expr::Call {
                expr_type: _,
                func_name,
                arg,
            } => {
                let arg = arg.eval(ctx)?;
                match ctx.get(func_name) {
                    Some(Val::Func(func)) => func
                        .call(arg)
                        .map_err(|err| EvalError::CallError(func_name.into(), err)),
                    Some(_) => Err(EvalError::NotAFunction(func_name.into())),
                    None => Err(EvalError::InvalidReference(func_name.into())),
                }
            }
            Expr::Block {
                expr_type: _,
                mut exprs,
            } => {
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
                expr_type: _,
                cond,
                main_branch,
                else_branch,
            } => {
                let mut cond = cond.eval(ctx)?;
                try_coerce(
                    &cond.get_type(),
                    &ValType::Bool,
                    Some(&mut cond),
                    CoercionStrategy::UNWRAP,
                )
                .map_err(|err| EvalError::NotAConditional(err))?;
                if cond.try_as_primitive().unwrap().try_as_bool().unwrap() {
                    main_branch.eval(ctx)
                } else if let Some(else_branch) = else_branch {
                    else_branch.eval(ctx)
                } else {
                    Ok(().into())
                }
            }
            Expr::Let {
                expr_type: _,
                lhs,
                rhs,
            } => {
                let rhs = rhs.eval(ctx)?;
                lhs.destruct_val(rhs.clone(), ctx, CoercionStrategy::let_pattern())?;
                Ok(rhs)
            }
            _ => Err(EvalError::MalformedExpr(format!("{:?}", self))),
        }
    }
}
