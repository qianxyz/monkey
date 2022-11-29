use crate::ast::{Expr, Program, Stmt};
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
        Expr::Bool(_) => todo!(),
        _ => todo!(),
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
    fn int_literal() {
        let cases = [("5;", 5), ("10", 10)];

        for (input, val) in cases {
            assert_eq!(eval_helper(input), Object::Int(val));
        }
    }
}
