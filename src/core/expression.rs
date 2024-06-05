use std::collections::HashMap;

use super::{
    context::TypeCtx, CallError, Func, InternFunc, NamedTuple, OrderedTuple, Pattern, Primitive,
    Val, ValCtx, ValType,
};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Untyped;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Typed<'a>(ValType<'a>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<'a, T> {
    Ref(T, &'a str),
    NewPrimitive(T, Primitive),
    NewNamedTuple(T, HashMap<&'a str, Expr<'a, T>>),
    NewOrderedTuple(T, Vec<Expr<'a, T>>),
    NewFunc {
        ret_type: T,
        arg_pattern: Pattern<'a>,
        body: Box<Expr<'a, T>>,
    },
    Block {
        ret_type: T,
        exprs: Vec<Expr<'a, T>>,
    },
    Call {
        ret_type: T,
        func_name: &'a str,
        arg: Box<Expr<'a, T>>,
    },
    Let {
        ret_type: T,
        name: &'a str,
        rhs: Box<Expr<'a, T>>,
    },
    If {
        ret_type: T,
        cond: Box<Expr<'a, T>>,
        main_branch: Box<Expr<'a, T>>,
        else_branch: Option<Box<Expr<'a, T>>>,
    },
    Access {
        ret_type: T,
        lhs: Box<Expr<'a, T>>,
        field_name: &'a str,
    },
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("expected type {expected}, got {actual}")]
    InvalidType { expected: String, actual: String },
    #[error("invalid reference `{0}`")]
    InvalidRef(String),
    #[error("expected `{0}` to be a function, but it has a type {1}")]
    NotAFunction(String, String),
    #[error("if branches do not return the same value")]
    InconsistentIfBranches,
    #[error("if condition is not a boolean but has type {0}")]
    NotAConditional(String),
    #[error("invalid field `{0}` on a named tuple of type {1}")]
    InvalidField(String, String),
    #[error("trying to access the field of a value that is not a named tuple")]
    NotANamedTuple,
    #[error("invalid arguments {0} to the call, which expects {1}")]
    InvalidArgs(String, String),
}

impl<'a> Expr<'a, Untyped> {
    pub fn to_typed(self, ctx: &mut TypeCtx<'a>) -> Result<Expr<'a, Typed<'a>>, TypeError> {
        match self {
            Expr::Ref(_, s) => Ok(Expr::Ref(
                Typed(ctx.get(s).cloned().ok_or(TypeError::InvalidRef(s.into()))?),
                s,
            )),
            Expr::NewPrimitive(_, p) => Ok(Expr::NewPrimitive(Typed(p.get_type()), p)),
            Expr::NewNamedTuple(_, tpl) => {
                let mut named_tpl_type = HashMap::new();
                let mut typed_tpl = HashMap::new();
                for (k, v) in tpl {
                    let typed_v = v.to_typed(ctx)?;
                    named_tpl_type.insert(k, typed_v.get_type());
                    typed_tpl.insert(k, typed_v);
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
                    ordered_tpl_type.push(typed_v.get_type());
                    typed_tpl.push(typed_v);
                }
                Ok(Expr::NewOrderedTuple(
                    Typed(ValType::OrderedTuple(ordered_tpl_type)),
                    typed_tpl,
                ))
            }
            Expr::NewFunc {
                ret_type: _,
                arg_pattern,
                body,
            } => {
                let mut ext_ctx = ctx.clone();
                arg_pattern.destruct_types(&mut ext_ctx);
                let typed_body = body.to_typed(&mut ext_ctx)?;
                let ret_type = ValType::Func(Box::new(typed_body.get_type()));
                Ok(Expr::NewFunc {
                    ret_type: Typed(ret_type),
                    arg_pattern,
                    body: Box::new(typed_body),
                })
            }
            Expr::Block { ret_type: _, exprs } => {
                let mut typed_exprs = Vec::new();
                let mut inner_ctx = ctx.clone();
                for expr in exprs {
                    typed_exprs.push(expr.to_typed(&mut inner_ctx)?);
                }
                let ret_type = typed_exprs
                    .last()
                    .map(|expr| expr.get_type())
                    .unwrap_or(ValType::Nil);
                Ok(Expr::Block {
                    ret_type: Typed(ret_type),
                    exprs: typed_exprs,
                })
            }
            Expr::Let {
                ret_type: _,
                name,
                rhs,
            } => {
                let typed_rhs = rhs.to_typed(ctx)?;
                ctx.extend(name, typed_rhs.get_type());
                // If we are extending with a function, additionally keep track of the argument pattern, since we need this information
                // to check if the calls are being invoked with correct arguments.
                if let Expr::NewFunc { arg_pattern, .. } = &typed_rhs {
                    ctx.extend_pattern(name, arg_pattern.clone())
                }
                Ok(Expr::Let {
                    ret_type: Typed(typed_rhs.get_type()),
                    name,
                    rhs: Box::new(typed_rhs),
                })
            }
            Expr::Call {
                ret_type: _,
                func_name,
                arg,
            } => {
                let typed_arg = arg.to_typed(ctx)?;
                let ret_type = match ctx.get(func_name).cloned() {
                    Some(ValType::Func(ret_type)) => ret_type,
                    Some(t) => {
                        return Err(TypeError::NotAFunction(
                            func_name.into(),
                            format!("{:?}", t),
                        ))
                    }
                    None => return Err(TypeError::InvalidRef(func_name.into())),
                };
                let arg_type = typed_arg.get_type();
                let expected_pat = ctx.get_pattern(func_name).unwrap();
                if !expected_pat.can_destruct(&arg_type) {
                    return Err(TypeError::InvalidArgs(
                        format!("{:?}", arg_type),
                        format!("{:?}", expected_pat),
                    ));
                }
                Ok(Expr::Call {
                    ret_type: Typed(*ret_type),
                    func_name,
                    arg: Box::new(typed_arg),
                })
            }
            Expr::If {
                ret_type: _,
                cond,
                main_branch,
                else_branch,
            } => {
                let typed_cond = cond.to_typed(ctx)?;
                let cond_type = typed_cond.get_type();
                if cond_type != ValType::Bool
                    && cond_type != ValType::OrderedTuple(vec![ValType::Bool])
                {
                    return Err(TypeError::NotAConditional(format!("{:?}", cond_type)));
                }
                let typed_main_branch = main_branch.to_typed(ctx)?;
                let typed_else_branch = if let Some(else_branch) = else_branch {
                    Some(else_branch.to_typed(ctx)?)
                } else {
                    None
                };
                let main_type = typed_main_branch.get_type();
                let else_type = typed_else_branch
                    .as_ref()
                    .map(|b| b.get_type())
                    .unwrap_or(ValType::Nil);
                if main_type != else_type {
                    return Err(TypeError::InconsistentIfBranches);
                }
                Ok(Expr::If {
                    ret_type: Typed(main_type),
                    cond: Box::new(typed_cond),
                    main_branch: Box::new(typed_main_branch),
                    else_branch: typed_else_branch.map(|b| Box::new(b)),
                })
            }
            Expr::Access {
                ret_type: _,
                lhs,
                field_name,
            } => {
                let typed_lhs = lhs.to_typed(ctx)?;
                let lhs_type = typed_lhs
                    .get_type()
                    .try_as_named_tuple()
                    .ok_or(TypeError::NotANamedTuple)?;
                let field_type = lhs_type.get(field_name).ok_or(TypeError::InvalidField(
                    field_name.into(),
                    format!("{:?}", lhs_type),
                ))?;
                Ok(Expr::Access {
                    ret_type: Typed(field_type.clone()),
                    lhs: Box::new(typed_lhs),
                    field_name,
                })
            }
        }
    }
}

impl<'a> Expr<'a, Typed<'a>> {
    pub fn get_type(&self) -> ValType<'a> {
        match self {
            Expr::Ref(Typed(t), _)
            | Expr::NewPrimitive(Typed(t), _)
            | Expr::NewNamedTuple(Typed(t), _)
            | Expr::NewOrderedTuple(Typed(t), _)
            | Expr::NewFunc {
                ret_type: Typed(t), ..
            }
            | Expr::Block {
                ret_type: Typed(t), ..
            }
            | Expr::Call {
                ret_type: Typed(t), ..
            }
            | Expr::Let {
                ret_type: Typed(t), ..
            }
            | Expr::If {
                ret_type: Typed(t), ..
            }
            | Expr::Access {
                ret_type: Typed(t), ..
            } => t.clone(),
        }
    }

    pub fn eval(self, ctx: &mut ValCtx<'a>) -> Result<Val<'a>, EvalError> {
        match self {
            Expr::Ref(_, token) => match ctx.get(token) {
                Some(v) => Ok(v.clone()),
                None => Err(EvalError::InvalidReference(token.into())),
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
                let mut eval_pairs = HashMap::new();
                for (k, v) in pairs {
                    eval_pairs.insert(k, v.eval(ctx)?);
                }
                Ok(NamedTuple(eval_pairs).into())
            }
            Expr::NewFunc {
                ret_type: _,
                arg_pattern,
                body,
            } => Ok(Val::Func(Func::Intern(InternFunc {
                ret_type: body.get_type(),
                arg_pattern,
                body: *body,
                captured_ctx: ctx.clone(),
            }))),
            Expr::Access {
                ret_type: _,
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
                ret_type: _,
                func_name,
                arg,
            } => match ctx.get(func_name).cloned() {
                Some(Val::Func(func)) => func
                    .call(arg.eval(ctx)?)
                    .map_err(|err| EvalError::CallError(func_name.into(), err)),
                Some(_) => Err(EvalError::NotAFunction(func_name.into())),
                None => Err(EvalError::InvalidReference(func_name.into())),
            },
            Expr::Block {
                ret_type: _,
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
                ret_type: _,
                cond,
                main_branch,
                else_branch,
            } => {
                if cond
                    .eval(ctx)?
                    .unwrap_singular_tuple()
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
            Expr::Let {
                ret_type: _,
                name,
                rhs,
            } => {
                let rhs = rhs.eval(ctx)?;
                ctx.extend(name, rhs.clone());
                Ok(rhs)
            }
        }
    }
}
