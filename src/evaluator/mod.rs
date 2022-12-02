pub mod environment;
pub mod object;

use std::cell::RefCell;
use std::rc::Rc;

use crate::parser::{Block, Expr, Ident, InfixOp, PrefixOp, Program, Stmt};
pub use environment::Environment;
pub use object::Object;

pub struct Evaluator {
    env: Rc<RefCell<Environment>>,
}

impl Evaluator {
    pub fn new() -> Self {
        Self {
            env: Rc::new(RefCell::new(Environment::new())),
        }
    }

    pub fn eval_program(&mut self, prog: Program) -> RuntimeResult<Object> {
        let mut result = Object::Null;

        for stmt in prog.0 {
            result = self.eval_stmt(stmt)?;
            // if we hit a `return`, unwrap the value and early return
            if let Object::Ret(e) = result {
                return Ok(*e);
            }
        }

        Ok(result)
    }

    fn eval_stmt(&mut self, stmt: Stmt) -> RuntimeResult<Object> {
        match stmt {
            Stmt::Let(ident, expr) => {
                let obj = self.eval_expr(expr)?;
                self.env.borrow_mut().set(ident, obj);
                // The let statement itself evaluates to null.
                Ok(Object::Null)
            }
            Stmt::Ret(e) => Ok(Object::Ret(self.eval_expr(e)?.into())),
            Stmt::Expr(e) => self.eval_expr(e),
        }
    }

    fn eval_expr(&mut self, expr: Expr) -> RuntimeResult<Object> {
        match expr {
            Expr::Int(n) => Ok(Object::Int(n)),
            Expr::Bool(b) => Ok(Object::Bool(b)),
            Expr::Prefix { op, right } => {
                let right = self.eval_expr(*right)?;
                self.eval_prefix(op, right)
            }
            Expr::Infix { op, left, right } => {
                let left = self.eval_expr(*left)?;
                let right = self.eval_expr(*right)?;
                self.eval_infix(op, left, right)
            }
            Expr::If { cond, consq, alter } => {
                let cond = self.eval_expr(*cond)?;
                self.eval_if(cond, consq, alter)
            }
            Expr::Ident(ident) => self.env.borrow().get(&ident),
            Expr::Fn { params, body } => Ok(Object::Fn {
                params,
                body,
                env: Rc::clone(&self.env),
            }),
            Expr::Call { func, args } => {
                let func = self.eval_expr(*func)?;
                let args = args
                    .into_iter()
                    .map(|e| self.eval_expr(e))
                    .collect::<Result<Vec<_>, _>>()?;
                Self::eval_call(func, args)
            }
        }
    }

    fn eval_prefix(&mut self, op: PrefixOp, right: Object) -> RuntimeResult<Object> {
        match op {
            // `-` should only accept number as operand
            PrefixOp::Negate => match right {
                Object::Int(n) => Ok(Object::Int(-n)),
                _ => Err(RuntimeError::BadUnaryOperand(op, right)),
            },
            // `!` applies to the `truthy value` of its operand
            PrefixOp::Not => Ok(Object::Bool(!bool::from(&right))),
        }
    }

    fn eval_infix(&mut self, op: InfixOp, left: Object, right: Object) -> RuntimeResult<Object> {
        match (&left, &right) {
            // numbers can be +-*/ and compared
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
            // generally objects have Eq trait
            _ => match op {
                InfixOp::EQ => Ok(Object::Bool(left == right)),
                InfixOp::NQ => Ok(Object::Bool(left != right)),
                _ => Err(RuntimeError::BadBinaryOperand(op, left, right)),
            },
        }
    }

    fn eval_if(
        &mut self,
        cond: Object,
        consq: Block,
        alter: Option<Block>,
    ) -> RuntimeResult<Object> {
        if bool::from(&cond) {
            self.eval_block(consq)
        } else if let Some(block) = alter {
            self.eval_block(block)
        } else {
            // false predicate with no else evals to null
            Ok(Object::Null)
        }
    }

    fn eval_block(&mut self, block: Block) -> RuntimeResult<Object> {
        let mut result = Object::Null;

        for stmt in block.0 {
            result = self.eval_stmt(stmt)?;
            // if we hit a `return`, do NOT unwrap, return the `Ret` variant
            if let Object::Ret(_) = result {
                return Ok(result);
            }
        }

        Ok(result)
    }

    fn eval_call(func: Object, args: Vec<Object>) -> RuntimeResult<Object> {
        // assert the func object is a callable variant
        // the env inside is the scope captured by the function
        let Object::Fn { params, body, env } = func else {
            return Err(RuntimeError::NotCallable(func));
        };
        // check # of params
        if params.len() != args.len() {
            return Err(RuntimeError::BadNumOfArguments {
                expected: params.len(),
                got: args.len(),
            });
        }

        // create local scope enclosing the function scope
        let mut local = Environment::enclose(env);
        // bind variables to local scope
        for (param, obj) in params.into_iter().zip(args.into_iter()) {
            local.set(param, obj);
        }

        // eval the body in the local scope
        let mut eval = Evaluator {
            env: Rc::new(RefCell::new(local)),
        };
        let result = eval.eval_block(body)?;

        // unpack if result is a return variant;
        // we don't want this to bubble up
        if let Object::Ret(e) = result {
            Ok(*e)
        } else {
            Ok(result)
        }
    }
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

        let mut evaluator = Evaluator::new();
        evaluator.eval_program(prog).unwrap()
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
    fn func_call() {
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

    #[test]
    fn recursion() {
        let input = "\
let fib = fn(x) {
    if (x < 2) {
        x;
    } else {
        fib(x - 1) + fib(x - 2);
    }
};
fib(10);
";
        assert_eq!(eval_helper(input), Object::Int(55))
    }
}
