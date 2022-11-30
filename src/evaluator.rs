use crate::ast::{Block, Expr, Ident, InfixOp, PrefixOp, Program, Stmt};
use crate::environment::Environment;
use crate::object::Object;

pub fn eval_program(prog: Program, env: &mut Environment) -> RuntimeResult<Object> {
    let mut result = Object::Null;

    for stmt in prog.0 {
        result = eval_stmt(stmt, env)?;
        // if we hit a `return`, unwrap the value and early return
        if let Object::Ret(e) = result {
            return Ok(*e);
        }
    }

    Ok(result)
}

fn eval_stmt(stmt: Stmt, env: &mut Environment) -> RuntimeResult<Object> {
    match stmt {
        Stmt::Let(ident, e) => {
            let obj = eval_expr(e, env)?;
            env.set(ident, obj);
            // The let statement itself evaluates to null.
            // Another option is to make it a walrus operator.
            Ok(Object::Null)
        }
        Stmt::Ret(e) => Ok(Object::Ret(eval_expr(e, env)?.into())),
        Stmt::Expr(e) => eval_expr(e, env),
    }
}

fn eval_expr(expr: Expr, env: &mut Environment) -> RuntimeResult<Object> {
    match expr {
        Expr::Int(n) => Ok(Object::Int(n)),
        Expr::Bool(b) => Ok(Object::Bool(b)),
        Expr::Prefix { op, right } => eval_prefix(op, eval_expr(*right, env)?),
        Expr::Infix { op, left, right } => {
            eval_infix(op, eval_expr(*left, env)?, eval_expr(*right, env)?)
        }
        Expr::If { cond, consq, alter } => eval_if(*cond, consq, alter, env),
        Expr::Ident(ident) => env.get(&ident),
        Expr::Fn { params, body } => Ok(Object::Fn {
            params,
            body,
            env: env.clone(),
        }),
        Expr::Call { func, args } => {
            // eval func and args into objects
            let func = eval_expr(*func, env)?;
            let args = args
                .into_iter()
                .map(|e| eval_expr(e, env))
                .collect::<RuntimeResult<Vec<Object>>>()?;
            let Object::Fn { params, body, env } = func else {
                return Err(RuntimeError::NotCallable(func));
            };

            // check if # of args match
            if params.len() != args.len() {
                return Err(RuntimeError::BadNumOfArguments {
                    expected: params.len(),
                    got: args.len(),
                });
            }

            // prepare environment, create local bindings
            let mut extended_env = Environment::enclose(env);
            for (ident, obj) in params.into_iter().zip(args.into_iter()) {
                extended_env.set(ident, obj);
            }

            // eval the block in local scope
            let result = eval_block(body, &mut extended_env)?;

            // unpack if result is a return variant;
            // we don't want this to bubble up
            if let Object::Ret(e) = result {
                Ok(*e)
            } else {
                Ok(result)
            }
        }
    }
}

fn eval_prefix(op: PrefixOp, right: Object) -> RuntimeResult<Object> {
    // Design choices:
    // 1. `-` should only accept number as operand.
    // 2. `!` applies to the `truthy value` of its operand.
    match op {
        PrefixOp::Negate => match right {
            Object::Int(n) => Ok(Object::Int(-n)),
            _ => Err(RuntimeError::BadUnaryOperand(op, right)),
        },
        PrefixOp::Not => Ok(Object::Bool(!bool::from(&right))),
    }
}

fn eval_infix(op: InfixOp, left: Object, right: Object) -> RuntimeResult<Object> {
    match (&left, &right) {
        (Object::Int(l), Object::Int(r)) => match op {
            InfixOp::Plus => Ok(Object::Int(l + r)),
            InfixOp::Minus => Ok(Object::Int(l - r)),
            InfixOp::Mult => Ok(Object::Int(l * r)),
            InfixOp::Div => {
                if *r != 0 {
                    Ok(Object::Int(l / r))
                } else {
                    Err(RuntimeError::ZeroDivisionError)
                }
            }
            InfixOp::EQ => Ok(Object::Bool(l == r)),
            InfixOp::NQ => Ok(Object::Bool(l != r)),
            InfixOp::LT => Ok(Object::Bool(l < r)),
            InfixOp::GT => Ok(Object::Bool(l > r)),
        },
        _ => match op {
            InfixOp::EQ => Ok(Object::Bool(left == right)),
            InfixOp::NQ => Ok(Object::Bool(left != right)),
            _ => Err(RuntimeError::BadBinaryOperand(op, left, right)),
        },
    }
}

fn eval_if(
    cond: Expr,
    consq: Block,
    alter: Option<Block>,
    env: &mut Environment,
) -> RuntimeResult<Object> {
    let cond = eval_expr(cond, env)?;

    if bool::from(&cond) {
        eval_block(consq, env)
    } else if let Some(block) = alter {
        eval_block(block, env)
    } else {
        Ok(Object::Null)
    }
}

fn eval_block(block: Block, env: &mut Environment) -> RuntimeResult<Object> {
    let mut result = Object::Null;

    for stmt in block.0 {
        result = eval_stmt(stmt, env)?;
        // if we hit a `return`, do NOT unwrap, return the `Ret` variant
        if let Object::Ret(_) = result {
            return Ok(result);
        }
    }

    Ok(result)
}

#[derive(Debug)]
pub enum RuntimeError {
    BadUnaryOperand(PrefixOp, Object),
    BadBinaryOperand(InfixOp, Object, Object),
    ZeroDivisionError,
    UnboundIdentifier(Ident),
    NotCallable(Object),
    BadNumOfArguments { expected: usize, got: usize },
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn eval_helper(input: &str) -> Object {
        let lexer = Lexer::new(input.to_string());
        let mut parser = Parser::new(lexer);
        let prog = parser.parse_program();
        assert_eq!(parser.errors(), vec![]);

        eval_program(prog, &mut Environment::new()).unwrap()
    }

    #[test]
    fn int_expr() {
        let cases = [
            ("5", 5),
            ("10", 10),
            ("-5", -5),
            ("-10", -10),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for (input, val) in cases {
            assert_eq!(eval_helper(input), Object::Int(val));
        }
    }

    #[test]
    fn bool_expr() {
        let cases = [
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];

        for (input, val) in cases {
            assert_eq!(eval_helper(input), Object::Bool(val));
        }
    }

    #[test]
    fn if_expr() {
        let cases = [
            ("if (true) { 10 }", Some(10)),
            ("if (false) { 10 }", None),
            ("if (1) { 10 }", Some(10)),
            ("if (1 < 2) { 10 }", Some(10)),
            ("if (1 > 2) { 10 }", None),
            ("if (1 > 2) { 10 } else { 20 }", Some(20)),
            ("if (1 < 2) { 10 } else { 20 }", Some(10)),
        ];

        for (input, val) in cases {
            assert_eq!(
                eval_helper(input),
                match val {
                    Some(n) => Object::Int(n),
                    None => Object::Null,
                }
            )
        }
    }

    #[test]
    fn return_expr() {
        let cases = [
            ("return 10;", 10),
            ("return 10; 9;", 10),
            ("return 2 * 5; 9;", 10),
            ("9; return 2 * 5; 9;", 10),
            (
                "\
if (10 > 1) {
    if (10 > 1) {
        return 10;
    }
    return 1;
}
",
                10,
            ),
        ];

        for (input, val) in cases {
            assert_eq!(eval_helper(input), Object::Int(val))
        }
    }

    #[test]
    fn let_expr() {
        let cases = [
            ("let a = 5; a;", 5),
            ("let a = 5 * 5; a;", 25),
            ("let a = 5; let b = a; b;", 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for (input, val) in cases {
            assert_eq!(eval_helper(input), Object::Int(val))
        }
    }

    #[test]
    fn function_application() {
        let cases = [
            ("let identity = fn(x) { x; }; identity(5);", 5),
            ("let identity = fn(x) { return x; }; identity(5);", 5),
            ("let double = fn(x) { x * 2; }; double(5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            ("fn(x) { x; }(5)", 5),
        ];

        for (input, val) in cases {
            assert_eq!(eval_helper(input), Object::Int(val))
        }
    }

    #[test]
    fn closure() {
        let input = "\
let newAdder = fn(x) {
    fn(y) { x + y };
};
let addTwo = newAdder(2);
addTwo(2);
";
        assert_eq!(eval_helper(input), Object::Int(4))
    }
}
