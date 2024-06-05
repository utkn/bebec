use super::{ExternCallable, ExternFunc, Func, InternFunc, Pattern, Val, ValType};

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
            patterns: val_ctx
                .bindings
                .iter()
                .flat_map(|(k, v)| v.try_as_func_ref().map(|f| (k, f)))
                .map(|(func_name, func)| {
                    (
                        *func_name,
                        match func {
                            Func::Intern(InternFunc { arg_pattern, .. })
                            | Func::Extern(ExternFunc { arg_pattern, .. }) => arg_pattern.clone(),
                        },
                    )
                })
                .collect(),
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
    patterns: Vec<(&'a str, Pattern<'a>)>,
}

impl<'a> TypeCtx<'a> {
    pub fn extend(&mut self, binding_name: &'a str, val_type: ValType<'a>) {
        self.bindings.push((binding_name, val_type));
    }

    pub fn extend_pattern(&mut self, pattern_name: &'a str, pattern: Pattern<'a>) {
        self.patterns.push((pattern_name, pattern));
    }

    pub fn get_pattern(&self, pattern_name: &'a str) -> Option<&Pattern<'a>> {
        self.patterns
            .iter()
            .rev()
            .find(|(name, _)| *name == pattern_name)
            .map(|(_, v)| v)
    }

    pub fn get(&self, binding_name: &'a str) -> Option<&ValType<'a>> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| *name == binding_name)
            .map(|(_, v)| v)
    }
}
