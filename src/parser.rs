use std::mem;

use crate::ast::{Block, Expr, Ident, Program, Stmt};
use crate::lexer::Lexer;
use crate::token::Token;

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
        let mut left = match self.curr {
            Ident(_) => self.parse_ident(),
            Int(_) => self.parse_int(),
            Minus | Bang => self.parse_prefix(),
            _ => return Err(ParseError::NoPrefixParseFn(self.next_token())),
        }?;

        while precedence < Precedence::from(&self.curr) {
            left = match self.curr {
                Plus | Minus | Slash | Asterisk | EQ | NQ | LT | GT => self.parse_infix(left)?,
                _ => return Err(ParseError::NoInfixParseFn(self.next_token())),
            };
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

    fn parse_prefix(&mut self) -> ParseResult<Expr> {
        let op = self.next_token();
        let right = Box::new(self.parse_expr(Precedence::Prefix)?);

        Ok(Expr::Prefix { op, right })
    }

    fn parse_infix(&mut self, left: Expr) -> ParseResult<Expr> {
        let prec = Precedence::from(&self.curr);
        let op = self.next_token();
        let right = Box::new(self.parse_expr(prec)?);

        Ok(Expr::Infix {
            op,
            left: left.into(),
            right,
        })
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
        let cases = [("!5;", Token::Bang, 5), ("-15;", Token::Minus, 15)];

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
        use Token::*;
        let cases = [
            ("5 + 5;", Plus),
            ("5 - 5;", Minus),
            ("5 * 5;", Asterisk),
            ("5 / 5;", Slash),
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
            //("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            //("(5 + 5) * 2", "((5 + 5) * 2)"),
            //("2 / (5 + 5)", "(2 / (5 + 5))"),
            //("-(5 + 5)", "(-(5 + 5))"),
            //("!(true == true)", "(!(true == true))"),
            //("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            //(
            //    "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
            //    "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            //),
            //(
            //    "add(a + b + c * d / f + g)",
            //    "add((((a + b) + ((c * d) / f)) + g))",
            //),
        ];

        for (input, expect) in cases {
            let mut parser = Parser::new(Lexer::new(input.to_string()));
            let program = parser.parse_program();
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
                        op: Token::LT,
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
                    op: Token::Plus,
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
                        op: Token::Plus,
                        left: Expr::Int(2).into(),
                        right: Expr::Int(3).into()
                    },
                    Expr::Infix {
                        op: Token::Asterisk,
                        left: Expr::Int(4).into(),
                        right: Expr::Int(5).into()
                    },
                ]
            })
        )
    }
}

/*

    fn parse_boolean(&mut self) -> Option<Expr> {
        Some(Expr::Bool(Boolean {
            token: self.cur.clone(),
            value: self.cur_token_is(TokenType::True),
        }))
    }

    fn parse_grouped_expr(&mut self) -> Option<Expr> {
        self.next_token();
        let expr = self.parse_expr(Precedence::Lowest);

        // this will properly register an error
        if !self.expect_peek(TokenType::RParen) {
            return None;
        }

        expr
    }

    fn parse_if_expr(&mut self) -> Option<Expr> {
        let cur = self.cur.clone();

        // `if` must be followed by a `(` ...
        if !self.expect_peek(TokenType::LParen) {
            return None;
        }

        self.next_token();
        let condition = self.parse_expr(Precedence::Lowest)?;

        // ... then closed by a `)`
        if !self.expect_peek(TokenType::RParen) {
            return None;
        }

        // the consequence must be enclosed in curly braces
        if !self.expect_peek(TokenType::LBrace) {
            return None;
        }

        // this handles the closing curly brace
        let consequence = self.parse_block_stmt()?;

        let alternative = if self.peek_token_is(TokenType::Else) {
            self.next_token();
            if !self.expect_peek(TokenType::LBrace) {
                return None;
            }
            Some(self.parse_block_stmt())?
        } else {
            None
        };

        Some(Expr::If(IfExpr {
            token: cur,
            condition: condition.into(),
            consequence,
            alternative,
        }))
    }

    fn parse_block_stmt(&mut self) -> Option<BlockStmt> {
        let cur = self.cur.clone();
        let mut stmts = Vec::new();

        self.next_token();

        while !self.cur_token_is(TokenType::RBrace) && !self.cur.is_eof() {
            stmts.push(self.parse_stmt()?);
            self.next_token();
        }

        Some(BlockStmt { token: cur, stmts })
    }

    fn parse_func_literal(&mut self) -> Option<Expr> {
        let token = self.cur.clone();

        if !self.expect_peek(TokenType::LParen) {
            return None;
        }

        // this takes care of `)`
        let params = self.parse_func_params()?;

        if !self.expect_peek(TokenType::LBrace) {
            return None;
        }

        let body = self.parse_block_stmt()?;

        Some(Expr::Fn(FuncLiteral {
            token,
            params,
            body,
        }))
    }

    fn parse_func_params(&mut self) -> Option<Vec<Identifier>> {
        let mut idents = Vec::new();

        // no parameters
        if self.peek_token_is(TokenType::RParen) {
            self.next_token();
            return Some(idents);
        }

        // get the first parameter
        self.next_token();
        let ident = Identifier {
            token: self.cur.clone(),
            value: self.cur.literal().to_string(),
        };
        idents.push(ident);

        // if there are more, separated by commas
        while self.peek_token_is(TokenType::Comma) {
            // advance twice so cur points to the identifier
            self.next_token();
            self.next_token();
            let ident = Identifier {
                token: self.cur.clone(),
                value: self.cur.literal().to_string(),
            };
            idents.push(ident);
        }

        if !self.expect_peek(TokenType::RParen) {
            return None;
        }

        Some(idents)
    }

    fn parse_call_expr(&mut self, func: Expr) -> Option<Expr> {
        let token = self.cur.clone();
        let args = self.parse_call_args()?;

        Some(Expr::Call(CallExpr {
            token,
            func: func.into(),
            args,
        }))
    }

    fn parse_call_args(&mut self) -> Option<Vec<Expr>> {
        let mut args = Vec::new();

        if self.peek_token_is(TokenType::RParen) {
            self.next_token();
            return Some(args);
        }

        self.next_token();
        args.push(self.parse_expr(Precedence::Lowest)?);
        while self.peek_token_is(TokenType::Comma) {
            self.next_token();
            self.next_token();
            args.push(self.parse_expr(Precedence::Lowest)?);
        }

        if !self.expect_peek(TokenType::RParen) {
            return None;
        }

        Some(args)
    }

*/
