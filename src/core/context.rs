use super::{ExternCallable, ExternFunc, Func, Pattern, Val, ValType};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ValCtx<'a> {
    bindings: Vec<(&'a str, Val<'a>)>,
}

impl<'a> ValCtx<'a> {
    pub fn register_func(
        &mut self,
        func_name: &'a str,
        arg_pattern: Pattern<'a>,
        ret_type: ValType<'a>,
        body: &'a impl ExternCallable<'a>,
    ) {
        self.extend(
            func_name,
            Val::Func(Func::Extern(ExternFunc {
                ret_type,
                arg_pattern,
                func_name,
                body,
            })),
        );
    }

    pub fn extend(&mut self, binding_name: &'a str, val: Val<'a>) {
        self.bindings.push((binding_name, val));
    }

    pub fn get(&self, binding_name: &'a str) -> Option<&Val<'a>> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| *name == binding_name)
            .map(|(_, v)| v)
    }
}

impl<'a> From<ValCtx<'a>> for TypeCtx<'a> {
    fn from(val_ctx: ValCtx<'a>) -> Self {
        Self {
            bindings: val_ctx
                .bindings
                .into_iter()
                .map(|(name, val)| (name, val.get_type()))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeCtx<'a> {
    bindings: Vec<(&'a str, ValType<'a>)>,
}

impl<'a> TypeCtx<'a> {
    pub fn extend(&mut self, binding_name: &'a str, val_type: ValType<'a>) {
        self.bindings.push((binding_name, val_type));
    }

    pub fn get(&self, binding_name: &'a str) -> Option<&ValType<'a>> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| *name == binding_name)
            .map(|(_, v)| v)
    }

    pub fn collect_types(&mut self, val_ctx: ValCtx<'a>) {
        self.bindings
            .extend(val_ctx.bindings.into_iter().map(|(k, v)| (k, v.get_type())))
    }
}
