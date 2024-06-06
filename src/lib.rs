mod core;
mod parser;
mod types;

#[cfg(test)]
mod tests {
    use crate::core::{extern_func, Expr, ExternCallError, Pattern, Val, ValCtx, ValType};

    #[test]
    fn integration_basic() {
        let mut ctx = ValCtx::default();
        let res = Expr::parse(
            r#"{
                let x: uint = 5;
                let y: bool = true;
                if (y) { x } else { 6 }
            }"#,
        )
        .unwrap()
        .to_typed(&mut ctx.clone().into())
        .unwrap()
        .eval(&mut ctx)
        .unwrap();
        assert_eq!(res, 5.into())
    }

    #[test]
    fn integration_call_intern() {
        let mut ctx = ValCtx::default();
        let res = Expr::parse(
            r#"{
                let foo: func(a: uint) uint = func(a: uint) a;
                (foo(5), foo(a=4))
            }"#,
        )
        .unwrap()
        .to_typed(&mut ctx.clone().into())
        .unwrap()
        .eval(&mut ctx)
        .unwrap();
        assert_eq!(res, (5, 4).into())
    }

    #[test]
    fn integration_call_extern() {
        let mut ctx = ValCtx::default();
        let add = extern_func!((a: usize, b: usize) => a + b);
        ctx.register_func(
            "add",
            Pattern::NamedTuple(vec![("a", ValType::Uint), ("b", ValType::Uint)]),
            ValType::Uint,
            &add,
        );
        let res = Expr::parse(r#"(add(4, 5), add(a=4, b=3))"#)
            .unwrap()
            .to_typed(&mut ctx.clone().into())
            .unwrap()
            .eval(&mut ctx)
            .unwrap();
        assert_eq!(res, (9, 7).into())
    }

    #[test]
    fn integration_multi_call() {
        let mut ctx = ValCtx::default();
        let add = extern_func!((a: usize, b: usize) => a + b);
        let sub = extern_func!((a: usize, b: usize) => a - b);
        ctx.register_func(
            "+",
            Pattern::NamedTuple(vec![("a", ValType::Uint), ("b", ValType::Uint)]),
            ValType::Uint,
            &add,
        );
        ctx.register_func(
            "-",
            Pattern::NamedTuple(vec![("a", ValType::Uint), ("b", ValType::Uint)]),
            ValType::Uint,
            &sub,
        );
        let res = Expr::parse(
            r#"{
                let double: func(a: uint) uint = func(a: uint) a + a;
                let triple1: func(a: uint) uint = func(a: uint) double(a) + a;
                (triple1(9), {
                    let triple2: func(a: uint) uint  = func(a: uint) a + (a + a);
                    triple2(3)
                }, {
                    let triple3: func(a: uint) uint = func(a: uint) (double(a) + double(a)) - a;
                    triple3(4)
                })
            }"#,
        )
        .unwrap()
        .to_typed(&mut ctx.clone().into())
        .unwrap()
        .eval(&mut ctx)
        .unwrap();
        assert_eq!(res, (27, 9, 12).into())
    }

    // #[test]
    // fn integration_5() {
    //     let mut ctx = ValCtx::default();
    //     let res = Expr::parse(
    //         r#"{
    //             let Employee = func(hours uint, salary uint) (hours=hours, salary=salary);
    //             let utkan = Employee(hours=1000, salary=0);
    //             (utkan.hours, utkan.salary)
    //         }"#,
    //     )
    //     .unwrap()
    //     .to_typed(&mut ctx.clone().into())
    //     .unwrap()
    //     .eval(&mut ctx)
    //     .unwrap();
    //     assert_eq!(res, (1000, 0).into())
    // }

    #[test]
    fn integration_coercion() {
        let mut ctx = ValCtx::default();
        let res = Expr::parse(
            r#"{
                let test2: func(uint) uint = func(a: uint) a;
                let test3: (uint, ()) = (a=5, b=());
                ()
            }"#,
        )
        .unwrap()
        .to_typed(&mut ctx.clone().into())
        .unwrap()
        .eval(&mut ctx)
        .unwrap();
        assert_eq!(res, ().into())
    }
}
