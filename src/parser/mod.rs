pub mod ast;

use std::mem;

use crate::lexer::{Lexer, Token};
pub use ast::{Block, Expr, Ident, InfixOp, PrefixOp, Program, Stmt};

#[derive(PartialEq, PartialOrd)]
enum Precedence {
    Lowest,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // fn(X)
}

impl From<&Token> for Precedence {
    fn from(t: &Token) -> Self {
        use Token::*;
        match t {
            EQ | NQ => Self::Equals,
            LT | GT => Self::LessGreater,
            Plus | Minus => Self::Sum,
            Asterisk | Slash => Self::Product,
            LParen => Self::Call,
            _ => Self::Lowest,
        }
    }
}

pub struct Parser {
    /// a lexer to spit out tokens
    lexer: Lexer,

    /// current parse point
    curr: Token,

    /// the next parse point
    peek: Token,

    /// collection of errors
    errors: Vec<ParseError>,
}

impl Parser {
    pub fn new(mut lexer: Lexer) -> Self {
        // set first two tokens
        let curr = lexer.next_token();
        let peek = lexer.next_token();

        Self {
            lexer,
            curr,
            peek,
            errors: vec![],
        }
    }

    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }

    /// Advance the parse point, return the current token.
    fn next_token(&mut self) -> Token {
        mem::replace(
            &mut self.curr,
            mem::replace(&mut self.peek, self.lexer.next_token()),
        )
    }

    pub fn parse_program(&mut self) -> Program {
        let mut stmts = Vec::new();

        while self.curr != Token::Eof {
            match self.parse_stmt() {
                Ok(s) => stmts.push(s),
                Err(e) => self.errors.push(e),
            }
        }

        Program(stmts)
    }

    fn parse_stmt(&mut self) -> ParseResult<Stmt> {
        match self.curr {
            Token::Let => self.parse_let_stmt(),
            Token::Return => self.parse_ret_stmt(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_let_stmt(&mut self) -> ParseResult<Stmt> {
        self.next_token(); // skip the `let` token

        // `let` must be followed by an identifier
        let ident = self.assert_curr_is_ident()?;

        // the identifier must be followed by a `=`
        self.assert_curr(Token::Assign)?;

        let value = self.parse_expr(Precedence::Lowest)?;

        // skip the optional semicolon
        if self.curr == Token::Semicolon {
            self.next_token();
        }

        Ok(Stmt::Let(ident, value))
    }

    fn parse_ret_stmt(&mut self) -> ParseResult<Stmt> {
        self.next_token(); // skip the `return` token

        let return_value = self.parse_expr(Precedence::Lowest)?;

        // skip the optional semicolon
        if self.curr == Token::Semicolon {
            self.next_token();
        }

        Ok(Stmt::Ret(return_value))
    }

    fn parse_expr_stmt(&mut self) -> ParseResult<Stmt> {
        let expr = self.parse_expr(Precedence::Lowest)?;

        // skip the optional semicolon
        if self.curr == Token::Semicolon {
            self.next_token();
        }

        Ok(Stmt::Expr(expr))
    }

    fn parse_expr(&mut self, precedence: Precedence) -> ParseResult<Expr> {
        use Token::*;
        let mut left = match &self.curr {
            Ident(_) => self.parse_ident(),
            Int(_) => self.parse_int(),
            True | False => self.parse_boolean(),
            LParen => self.parse_grouped_expr(),
            If => self.parse_if_expr(),
            Function => self.parse_func_literal(),
            t => {
                if let Ok(op) = PrefixOp::try_from(t) {
                    self.parse_prefix(op)
                } else {
                    return Err(ParseError::NoPrefixParseFn(self.next_token()));
                }
            }
        }?;

        while precedence < Precedence::from(&self.curr) {
            left = match &self.curr {
                LParen => self.parse_call_expr(left),
                t => {
                    if let Ok(op) = InfixOp::try_from(t) {
                        self.parse_infix(op, left)
                    } else {
                        return Err(ParseError::NoInfixParseFn(self.next_token()));
                    }
                }
            }?;
        }

        Ok(left)
    }

    fn parse_ident(&mut self) -> ParseResult<Expr> {
        let Token::Ident(s) = self.next_token() else { unreachable!() };
        Ok(Expr::Ident(Ident(s)))
    }

    fn parse_int(&mut self) -> ParseResult<Expr> {
        let Token::Int(s) = self.next_token() else { unreachable!() };
        match s.parse() {
            Ok(n) => Ok(Expr::Int(n)),
            _ => Err(ParseError::ParseIntError(s)),
        }
    }

    fn parse_prefix(&mut self, op: PrefixOp) -> ParseResult<Expr> {
        self.next_token();
        let right = Box::new(self.parse_expr(Precedence::Prefix)?);

        Ok(Expr::Prefix { op, right })
    }

    fn parse_infix(&mut self, op: InfixOp, left: Expr) -> ParseResult<Expr> {
        let prec = Precedence::from(&self.next_token());
        let right = Box::new(self.parse_expr(prec)?);

        Ok(Expr::Infix {
            op,
            left: left.into(),
            right,
        })
    }

    fn parse_boolean(&mut self) -> ParseResult<Expr> {
        match self.next_token() {
            Token::True => Ok(Expr::Bool(true)),
            Token::False => Ok(Expr::Bool(false)),
            _ => unreachable!(),
        }
    }

    fn parse_grouped_expr(&mut self) -> ParseResult<Expr> {
        self.next_token(); // the `(`
        let expr = self.parse_expr(Precedence::Lowest)?;

        // assert the closing `)`
        self.assert_curr(Token::RParen).map(|_| expr)
    }

    fn parse_if_expr(&mut self) -> ParseResult<Expr> {
        self.next_token(); // the `if` token

        // the condition is wrapped in `()`
        self.assert_curr(Token::LParen)?;
        let cond = self.parse_expr(Precedence::Lowest)?;
        self.assert_curr(Token::RParen)?;

        let consq = self.parse_block_stmt()?;

        let alter = if self.curr == Token::Else {
            self.next_token(); // skip the `else`
            Some(self.parse_block_stmt()?)
        } else {
            None
        };

        Ok(Expr::If {
            cond: cond.into(),
            consq,
            alter,
        })
    }

    fn parse_block_stmt(&mut self) -> ParseResult<Block> {
        let mut stmts = Vec::new();

        self.assert_curr(Token::LBrace)?;

        while self.curr != Token::RBrace && self.curr != Token::Eof {
            stmts.push(self.parse_stmt()?);
        }
        self.assert_curr(Token::RBrace)?;

        Ok(Block(stmts))
    }

    fn parse_func_literal(&mut self) -> ParseResult<Expr> {
        self.next_token(); // the `fn`

        let params = self.parse_func_params()?;

        let body = self.parse_block_stmt()?;

        Ok(Expr::Fn { params, body })
    }

    fn parse_func_params(&mut self) -> ParseResult<Vec<Ident>> {
        let mut idents = Vec::new();

        self.assert_curr(Token::LParen)?;

        // no parameters
        if self.curr == Token::RParen {
            self.next_token();
            return Ok(idents);
        }

        // get the first identifier
        idents.push(self.assert_curr_is_ident()?);

        while self.curr == Token::Comma {
            self.next_token();
            idents.push(self.assert_curr_is_ident()?);
        }

        self.assert_curr(Token::RParen)?;

        Ok(idents)
    }

    fn parse_call_expr(&mut self, func: Expr) -> ParseResult<Expr> {
        let args = self.parse_call_args()?;

        Ok(Expr::Call {
            func: func.into(),
            args,
        })
    }

    fn parse_call_args(&mut self) -> ParseResult<Vec<Expr>> {
        self.next_token(); // skip the `(`

        let mut args = Vec::new();

        if self.curr == Token::RParen {
            self.next_token();
            return Ok(args);
        }

        args.push(self.parse_expr(Precedence::Lowest)?);
        while self.curr == Token::Comma {
            self.next_token();
            args.push(self.parse_expr(Precedence::Lowest)?);
        }

        self.assert_curr(Token::RParen)?;

        Ok(args)
    }

    /// Check if the current token is expected.
    /// This advances the parse point anyway.
    fn assert_curr(&mut self, expected: Token) -> ParseResult<Token> {
        match self.next_token() {
            t if t == expected => Ok(t),
            t => Err(ParseError::UnexpectedToken { expected, got: t }),
        }
    }

    /// Check if the current token is an identifier.
    /// This advances the parse point anyway.
    fn assert_curr_is_ident(&mut self) -> ParseResult<Ident> {
        match self.next_token() {
            Token::Ident(s) => Ok(Ident(s)),
            t => Err(ParseError::NotAnIdentifier(t)),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedToken { expected: Token, got: Token },
    NotAnIdentifier(Token),
    ParseIntError(String),
    NoPrefixParseFn(Token),
    NoInfixParseFn(Token),
}

pub type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_helper(input: &str) -> Vec<Stmt> {
        let mut parser = Parser::new(Lexer::new(input.to_string()));
        let prog = parser.parse_program();
        assert_eq!(parser.errors, vec![]);
        prog.0
    }

    #[test]
    fn let_stmt() {
        let input = "\
let x = 5;
let y = 10;
let foobar = 838383;
";
        let expect = [("x", 5), ("y", 10), ("foobar", 838383)];

        let stmts = parse_helper(input);
        for (s, (x, n)) in stmts.into_iter().zip(expect.into_iter()) {
            assert_eq!(s, Stmt::Let(Ident(x.to_string()), Expr::Int(n)));
        }
    }

    #[test]
    fn return_stmts() {
        let input = "\
return 5;
return 10;
return 993322;
";
        let expect = [5, 10, 993322];

        let stmts = parse_helper(input);
        for (s, n) in stmts.into_iter().zip(expect.into_iter()) {
            assert_eq!(s, Stmt::Ret(Expr::Int(n)))
        }
    }

    #[test]
    fn ident_expr() {
        let input = "x; y;";
        let expect = ["x", "y"];

        let stmts = parse_helper(input);
        for (s, x) in stmts.into_iter().zip(expect.iter()) {
            assert_eq!(s, Stmt::Expr(Expr::Ident(Ident(x.to_string()))));
        }
    }

    #[test]
    fn prefix_expr() {
        let cases = [("!5;", PrefixOp::Not, 5), ("-15;", PrefixOp::Negate, 15)];

        for (input, op, n) in cases {
            let stmts = parse_helper(input);
            assert_eq!(
                stmts[0],
                Stmt::Expr(Expr::Prefix {
                    op,
                    right: Expr::Int(n).into()
                })
            )
        }
    }

    #[test]
    fn infix_expr() {
        use InfixOp::*;
        let cases = [
            ("5 + 5;", Plus),
            ("5 - 5;", Minus),
            ("5 * 5;", Mult),
            ("5 / 5;", Div),
            ("5 > 5;", GT),
            ("5 < 5;", LT),
            ("5 == 5;", EQ),
            ("5 != 5;", NQ),
        ];
        let five = || Box::new(Expr::Int(5));

        for (input, op) in cases {
            let stmts = parse_helper(input);
            assert_eq!(
                stmts[0],
                Stmt::Expr(Expr::Infix {
                    op,
                    left: five(),
                    right: five()
                })
            )
        }
    }

    #[test]
    fn precedence_parsing() {
        let cases = [
            ("-a * b", "((-a) * b);\n"),
            ("!-a", "(!(-a));\n"),
            ("a + b + c", "((a + b) + c);\n"),
            ("a + b - c", "((a + b) - c);\n"),
            ("a * b * c", "((a * b) * c);\n"),
            ("a * b / c", "((a * b) / c);\n"),
            ("a + b / c", "(a + (b / c));\n"),
            (
                "a + b * c + d / e - f",
                "(((a + (b * c)) + (d / e)) - f);\n",
            ),
            ("3 + 4; -5 * 5", "(3 + 4);\n((-5) * 5);\n"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4));\n"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4));\n"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));\n",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));\n",
            ),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4);\n"),
            ("(5 + 5) * 2", "((5 + 5) * 2);\n"),
            ("2 / (5 + 5)", "(2 / (5 + 5));\n"),
            ("-(5 + 5)", "(-(5 + 5));\n"),
            ("!(true == true)", "(!(true == true));\n"),
            ("a + add(b * c) + d", "((a + add((b * c))) + d);\n"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)));\n",
            ),
            (
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g));\n",
            ),
        ];

        for (input, expect) in cases {
            let mut parser = Parser::new(Lexer::new(input.to_string()));
            let program = parser.parse_program();
            //assert_eq!(parser.errors, vec![]);
            assert_eq!(program.to_string(), expect);
        }
    }

    #[test]
    fn boolean_expr() {
        let cases = [("true;", true), ("false", false)];

        for (input, b) in cases {
            let stmts = parse_helper(input);
            assert_eq!(stmts[0], Stmt::Expr(Expr::Bool(b)))
        }
    }

    #[test]
    fn if_expr() {
        let input = "\
if (x < y) { x; }
if (x < y) { x; } else { y; }";
        let x = || Expr::Ident(Ident("x".to_string()));
        let y = || Expr::Ident(Ident("y".to_string()));

        let stmts = parse_helper(input);
        for i in 0..2 {
            assert_eq!(
                stmts[i],
                Stmt::Expr(Expr::If {
                    cond: Expr::Infix {
                        op: InfixOp::LT,
                        left: x().into(),
                        right: y().into()
                    }
                    .into(),
                    consq: Block(vec![Stmt::Expr(x())]),
                    alter: if i == 0 {
                        None
                    } else {
                        Some(Block(vec![Stmt::Expr(y())]))
                    }
                })
            );
        }
    }

    #[test]
    fn function_literal() {
        let input = "fn(x, y) { x + y; }";
        let x = || Ident("x".to_string());
        let y = || Ident("y".to_string());

        let stmts = parse_helper(input);
        assert_eq!(
            stmts[0],
            Stmt::Expr(Expr::Fn {
                params: vec![x(), y()],
                body: Block(vec![Stmt::Expr(Expr::Infix {
                    op: InfixOp::Plus,
                    left: Expr::Ident(x()).into(),
                    right: Expr::Ident(y()).into(),
                })])
            })
        )
    }

    #[test]
    fn func_params() {
        let cases = [
            ("fn() {};", vec![]),
            ("fn(x) {};", vec!["x"]),
            ("fn(x, y, z) {};", vec!["x", "y", "z"]),
        ];

        for (input, params) in cases {
            let stmts = parse_helper(input);
            assert_eq!(
                stmts[0],
                Stmt::Expr(Expr::Fn {
                    params: params.iter().map(|s| Ident(s.to_string())).collect(),
                    body: Block(vec![])
                })
            );
        }
    }

    #[test]
    fn call_expr() {
        let input = "add(1, 2 + 3, 4 * 5)";

        let stmts = parse_helper(input);
        assert_eq!(
            stmts[0],
            Stmt::Expr(Expr::Call {
                func: Expr::Ident(Ident("add".to_string())).into(),
                args: vec![
                    Expr::Int(1),
                    Expr::Infix {
                        op: InfixOp::Plus,
                        left: Expr::Int(2).into(),
                        right: Expr::Int(3).into()
                    },
                    Expr::Infix {
                        op: InfixOp::Mult,
                        left: Expr::Int(4).into(),
                        right: Expr::Int(5).into()
                    },
                ]
            })
        )
    }
}
