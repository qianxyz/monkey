use crate::ast::{Block, Expr, InfixOp, PrefixOp, Program, Stmt};
use crate::object::Object;

pub fn eval_program(prog: Program) -> RuntimeResult<Object> {
    let mut result = Object::Null;

    for stmt in prog.0 {
        result = eval_stmt(stmt)?;
        // if we hit a `return`, unwrap the value and early return
        if let Object::Ret(e) = result {
            return Ok(*e);
        }
    }

    Ok(result)
}

fn eval_stmt(stmt: Stmt) -> RuntimeResult<Object> {
    match stmt {
        Stmt::Let(_, _) => todo!(),
        Stmt::Ret(e) => Ok(Object::Ret(eval_expr(e)?.into())),
        Stmt::Expr(e) => eval_expr(e),
    }
}

fn eval_expr(expr: Expr) -> RuntimeResult<Object> {
    match expr {
        Expr::Int(n) => Ok(Object::Int(n)),
        Expr::Bool(b) => Ok(Object::Bool(b)),
        Expr::Prefix { op, right } => eval_prefix(op, eval_expr(*right)?),
        Expr::Infix { op, left, right } => eval_infix(op, eval_expr(*left)?, eval_expr(*right)?),
        Expr::If { cond, consq, alter } => eval_if(*cond, consq, alter),
        _ => todo!(),
    }
}

fn eval_prefix(op: PrefixOp, right: Object) -> RuntimeResult<Object> {
    // Design choices:
    // 1. `-` should only accept number as operand.
    // 2. `!` applies to the `truthy value` of its operand.
    match op {
        PrefixOp::Negate => match right {
            Object::Int(n) => Ok(Object::Int(-n)),
            _ => Err(RuntimeError), // bad operand type for "-"
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

fn eval_if(cond: Expr, consq: Block, alter: Option<Block>) -> RuntimeResult<Object> {
    let cond = eval_expr(cond)?;

    if bool::from(&cond) {
        eval_block(consq)
    } else if let Some(block) = alter {
        eval_block(block)
    } else {
        Ok(Object::Null)
    }
}

fn eval_block(block: Block) -> RuntimeResult<Object> {
    let mut result = Object::Null;

    for stmt in block.0 {
        result = eval_stmt(stmt)?;
        // if we hit a `return`, do NOT unwrap, return the `Ret` variant
        if let Object::Ret(_) = result {
            return Ok(result);
        }
    }

    Ok(result)
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
}
