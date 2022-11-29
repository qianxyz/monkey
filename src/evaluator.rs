use crate::ast::{Expr, InfixOp, PrefixOp, Program, Stmt};
use crate::object::Object;

pub fn eval_program(prog: Program) -> RuntimeResult<Object> {
    let mut result = Object::Null;

    for stmt in prog.0 {
        result = eval_stmt(stmt)?;
    }

    Ok(result)
}

fn eval_stmt(stmt: Stmt) -> RuntimeResult<Object> {
    match stmt {
        Stmt::Let(_, _) => todo!(),
        Stmt::Ret(_) => todo!(),
        Stmt::Expr(e) => eval_expr(e),
    }
}

fn eval_expr(expr: Expr) -> RuntimeResult<Object> {
    match expr {
        Expr::Int(n) => Ok(Object::Int(n)),
        Expr::Bool(b) => Ok(Object::Bool(b)),
        Expr::Prefix { op, right } => eval_prefix(op, eval_expr(*right)?),
        Expr::Infix { op, left, right } => eval_infix(op, eval_expr(*left)?, eval_expr(*right)?),
        _ => todo!(),
    }
}

fn eval_prefix(op: PrefixOp, right: Object) -> RuntimeResult<Object> {
    // TODO: what should these return?
    // 1. "!0" and "!1"
    // 2. "-true" and "-false"
    // 3. "-null"
    match op {
        PrefixOp::Negate => match right {
            Object::Int(n) => Ok(Object::Int(-n)),
            _ => Err(RuntimeError), // bad operand type for "-"
        },
        PrefixOp::Not => match right {
            Object::Bool(b) => Ok(Object::Bool(!b)),
            Object::Null => Ok(Object::Bool(true)),
            Object::Int(n) => Ok(Object::Bool(n == 0)),
        },
    }
}

fn eval_infix(op: InfixOp, left: Object, right: Object) -> RuntimeResult<Object> {
    match (&left, &right) {
        (Object::Int(l), Object::Int(r)) => match op {
            InfixOp::Plus => Ok(Object::Int(l + r)),
            InfixOp::Minus => Ok(Object::Int(l - r)),
            InfixOp::Mult => Ok(Object::Int(l * r)),
            InfixOp::Div => Ok(Object::Int(l / r)),
            InfixOp::EQ => Ok(Object::Bool(l == r)),
            InfixOp::NQ => Ok(Object::Bool(l != r)),
            InfixOp::LT => Ok(Object::Bool(l < r)),
            InfixOp::GT => Ok(Object::Bool(l > r)),
        },
        _ => match op {
            InfixOp::EQ => Ok(Object::Bool(left == right)),
            InfixOp::NQ => Ok(Object::Bool(left != right)),
            _ => Err(RuntimeError), // bad operands for op
        },
    }
}

#[derive(Debug)]
pub struct RuntimeError;

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

        eval_program(prog).unwrap()
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
}
