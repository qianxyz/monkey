use std::mem;

use crate::ast::{Block, Expr, Ident, Program, Stmt};
use crate::lexer::Lexer;
use crate::token::Token;

type PrefixParseFn = fn(&mut Parser) -> Option<Expr>;
type InfixParseFn = fn(&mut Parser, Expr) -> Option<Expr>;

impl TryFrom<&Token> for PrefixParseFn {
    type Error = ParseError;

    fn try_from(value: &Token) -> Result<Self, Self::Error> {
        use Token::*;
        match value {
            Ident(_) => Ok(Parser::parse_ident),
            Int(_) => Ok(Parser::parse_int),
            Minus | Bang => Ok(Parser::parse_prefix),
            _ => Err(ParseError),
        }
    }
}

impl TryFrom<&Token> for InfixParseFn {
    type Error = ParseError;

    fn try_from(value: &Token) -> Result<Self, Self::Error> {
        use Token::*;
        match value {
            Plus | Minus | Slash | Asterisk | EQ | NQ | LT | GT => Ok(Parser::parse_infix),
            _ => Err(ParseError),
        }
    }
}

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
            if let Some(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            } else {
                self.next_token();
            }
        }

        Program(stmts)
    }

    fn parse_stmt(&mut self) -> Option<Stmt> {
        match self.curr {
            Token::Let => self.parse_let_stmt(),
            Token::Return => self.parse_ret_stmt(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_let_stmt(&mut self) -> Option<Stmt> {
        // `let` must be followed by an identifier
        let Token::Ident(_) = self.peek else {
            self.errors.push(ParseError);
            return None;
        };
        self.next_token(); // skip the `let` token

        // the identifier must be followed by a `=`
        if self.peek != Token::Assign {
            self.errors.push(ParseError);
            return None;
        }

        let Token::Ident(s) = self.next_token() else { unreachable!() };
        let ident = Ident(s);
        self.next_token();

        let value = self.parse_expr(Precedence::Lowest)?;

        // skip the optional semicolon
        if self.curr == Token::Semicolon {
            self.next_token();
        }

        Some(Stmt::Let(ident, value))
    }

    fn parse_ret_stmt(&mut self) -> Option<Stmt> {
        self.next_token(); // skip the `return` token

        let return_value = self.parse_expr(Precedence::Lowest)?;

        // skip the optional semicolon
        if self.curr == Token::Semicolon {
            self.next_token();
        }

        Some(Stmt::Ret(return_value))
    }

    fn parse_expr_stmt(&mut self) -> Option<Stmt> {
        let expr = self.parse_expr(Precedence::Lowest)?;

        // skip the optional semicolon
        if self.curr == Token::Semicolon {
            self.next_token();
        }

        Some(Stmt::Expr(expr))
    }

    fn parse_expr(&mut self, precedence: Precedence) -> Option<Expr> {
        let prefix_fn = match PrefixParseFn::try_from(&self.curr) {
            Ok(f) => f,
            Err(e) => {
                self.errors.push(e);
                return None;
            }
        };
        let mut left = prefix_fn(self)?;

        while precedence < Precedence::from(&self.curr) {
            let infix_fn = match InfixParseFn::try_from(&self.curr) {
                Ok(f) => f,
                Err(_) => {
                    // TODO: it is always an error?
                    return Some(left);
                }
            };
            left = infix_fn(self, left)?;
        }

        Some(left)
    }

    fn parse_ident(&mut self) -> Option<Expr> {
        let Token::Ident(s) = self.next_token() else { unreachable!() };
        Some(Expr::Ident(Ident(s)))
    }

    fn parse_int(&mut self) -> Option<Expr> {
        let Token::Int(s) = self.next_token() else { unreachable!() };
        match s.parse() {
            Ok(n) => Some(Expr::Int(n)),
            _ => {
                self.errors.push(ParseError);
                None
            }
        }
    }

    fn parse_prefix(&mut self) -> Option<Expr> {
        let op = self.next_token();
        let right = Box::new(self.parse_expr(Precedence::Prefix)?);

        Some(Expr::Prefix { op, right })
    }

    fn parse_infix(&mut self, left: Expr) -> Option<Expr> {
        let prec = Precedence::from(&self.curr);
        let op = self.next_token();
        let right = Box::new(self.parse_expr(prec)?);

        Some(Expr::Infix {
            op,
            left: left.into(),
            right,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseError;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn let_stmt() {
        let input = "\
let x = 5;
let y = 10;
let foobar = 838383;
";
        let expect = [("x", 5), ("y", 10), ("foobar", 838383)];

        let mut parser = Parser::new(Lexer::new(input.to_string()));
        let prog = parser.parse_program();
        assert_eq!(parser.errors, vec![]);

        for (s, (x, n)) in prog.0.into_iter().zip(expect.into_iter()) {
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

        let mut parser = Parser::new(Lexer::new(input.to_string()));
        let prog = parser.parse_program();
        assert_eq!(parser.errors, vec![]);

        for (s, n) in prog.0.into_iter().zip(expect.into_iter()) {
            assert_eq!(s, Stmt::Ret(Expr::Int(n)))
        }
    }

    #[test]
    fn ident_expr() {
        let input = "x; y;";
        let expect = ["x", "y"];

        let mut parser = Parser::new(Lexer::new(input.to_string()));
        let prog = parser.parse_program();
        assert_eq!(parser.errors, vec![]);

        for (s, x) in prog.0.into_iter().zip(expect.iter()) {
            assert_eq!(s, Stmt::Expr(Expr::Ident(Ident(x.to_string()))));
        }
    }

    #[test]
    fn prefix_expr() {
        let cases = [("!5;", Token::Bang, 5), ("-15;", Token::Minus, 15)];

        for (input, op, n) in cases {
            let mut parser = Parser::new(Lexer::new(input.to_string()));
            let prog = parser.parse_program();
            assert_eq!(parser.errors, vec![]);
            assert_eq!(
                prog.0[0],
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
            let mut parser = Parser::new(Lexer::new(input.to_string()));
            let prog = parser.parse_program();
            //assert_eq!(parser.errors, vec![]);
            assert_eq!(
                prog.0[0],
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
}

/*
    // ? Most of the parsing functions return Option<ast::Stmt>, which is None
    // when we encounter a parsing error. The error itself, however,
    // is not returned directly, and instead is handled by each function.
    // This grants more flexibility, e.g., raising multiple errors
    // in one parsing function; If such need never rises at the end,
    // maybe it's better to be explicit by returning Result<Stmt, ParseError>.

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

    fn cur_token_is(&self, t: TokenType) -> bool {
        self.cur.ttype() == &t
    }

    fn peek_token_is(&self, t: TokenType) -> bool {
        self.peek.ttype() == &t
    }

    /// An "assertion function".
    /// If the next token is of expected type, advance parse point;
    /// Otherwise, report a ParseError.
    fn expect_peek(&mut self, t: TokenType) -> bool {
        if self.peek_token_is(t) {
            self.next_token();
            true
        } else {
            self.peek_error(t);
            false
        }
    }

    /// Append to errors if the next token is not expected.
    fn peek_error(&mut self, t: TokenType) {
        let e = ParseError::UnexpectedToken {
            expected: t,
            got: *self.peek.ttype(),
        };
        self.errors.push(e);
    }

    /// This happens when parser is to parse an expression, but found
    /// a token that is not supposed to be a prefix.
    fn no_prefix_parse_fn_error(&mut self, t: TokenType) {
        self.errors.push(ParseError::NoPrefixParseFn(t))
    }

    fn cur_precedence(&self) -> Precedence {
        self.cur.ttype().into()
    }

    fn peek_precedence(&self) -> Precedence {
        self.peek.ttype().into()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedToken { expected: TokenType, got: TokenType },
    ParseIntError(String),
    NoPrefixParseFn(TokenType),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parser_helper(input: &str) -> (Vec<Stmt>, Vec<ParseError>) {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();

        (program.stmts, parser.errors)
    }

    #[test]
    fn let_stmts_error() {
        let input = "\
let x 5;
let = 10;
let 838383;
";
        use TokenType::*;
        let errs = [(Assign, Int), (Ident, Assign), (Ident, Int)];

        let (_, errors) = parser_helper(input);

        for (e, (l, r)) in errors.iter().zip(errs.into_iter()) {
            assert_eq!(
                e,
                &ParseError::UnexpectedToken {
                    expected: l,
                    got: r,
                }
            )
        }

        assert_eq!(errors.len(), 3);
    }

    #[test]
    fn too_big_int() {
        let input = "100000000000000000000000";
        let (stmts, errors) = parser_helper(input);
        assert!(stmts.is_empty());
        assert_eq!(errors.len(), 1);

        assert_eq!(errors[0], ParseError::ParseIntError(input.to_string()))
    }

    #[test]
    fn boolean_expr() {
        let inputs = [
            ("true;", TokenType::True, true),
            ("false", TokenType::False, false),
        ];

        for (input, ttype, b) in inputs {
            let (stmts, errors) = parser_helper(input);
            assert_eq!(errors, vec![]);
            assert_eq!(stmts.len(), 1);
            assert_eq!(
                stmts[0],
                Stmt::Expr(ExprStmt {
                    token: Token::new(ttype, &b.to_string()),
                    expr: Expr::Bool(Boolean {
                        token: Token::new(ttype, &b.to_string()),
                        value: b
                    })
                })
            )
        }
    }

    #[test]
    fn if_expr() {
        let input = "if (x < y) { x }";
        let (stmts, errors) = parser_helper(input);

        assert_eq!(
            stmts[0],
            Stmt::Expr(ExprStmt {
                token: Token::new(TokenType::If, "if"),
                expr: Expr::If(IfExpr {
                    token: Token::new(TokenType::If, "if"),
                    condition: Expr::Infix(InfixExpr {
                        token: Token::new(TokenType::LT, "<"),
                        left: Expr::Ident(Identifier {
                            token: Token::new(TokenType::Ident, "x"),
                            value: "x".to_string()
                        })
                        .into(),
                        op: "<".to_string(),
                        right: Expr::Ident(Identifier {
                            token: Token::new(TokenType::Ident, "y"),
                            value: "y".to_string()
                        })
                        .into(),
                    })
                    .into(),
                    consequence: BlockStmt {
                        token: Token::new(TokenType::LBrace, "{"),
                        stmts: vec![Stmt::Expr(ExprStmt {
                            token: Token::new(TokenType::Ident, "x"),
                            expr: Expr::Ident(Identifier {
                                token: Token::new(TokenType::Ident, "x"),
                                value: "x".to_string()
                            })
                        })]
                    },
                    alternative: None
                })
            })
        );
        assert_eq!(errors, vec![]);
        assert_eq!(stmts.len(), 1);
    }

    #[test]
    fn if_else_expr() {
        let input = "if (x < y) { x } else { y }";
        let (stmts, errors) = parser_helper(input);

        assert_eq!(
            stmts[0],
            Stmt::Expr(ExprStmt {
                token: Token::new(TokenType::If, "if"),
                expr: Expr::If(IfExpr {
                    token: Token::new(TokenType::If, "if"),
                    condition: Expr::Infix(InfixExpr {
                        token: Token::new(TokenType::LT, "<"),
                        left: Expr::Ident(Identifier {
                            token: Token::new(TokenType::Ident, "x"),
                            value: "x".to_string()
                        })
                        .into(),
                        op: "<".to_string(),
                        right: Expr::Ident(Identifier {
                            token: Token::new(TokenType::Ident, "y"),
                            value: "y".to_string()
                        })
                        .into(),
                    })
                    .into(),
                    consequence: BlockStmt {
                        token: Token::new(TokenType::LBrace, "{"),
                        stmts: vec![Stmt::Expr(ExprStmt {
                            token: Token::new(TokenType::Ident, "x"),
                            expr: Expr::Ident(Identifier {
                                token: Token::new(TokenType::Ident, "x"),
                                value: "x".to_string()
                            })
                        })]
                    },
                    alternative: Some(BlockStmt {
                        token: Token::new(TokenType::LBrace, "{"),
                        stmts: vec![Stmt::Expr(ExprStmt {
                            token: Token::new(TokenType::Ident, "y"),
                            expr: Expr::Ident(Identifier {
                                token: Token::new(TokenType::Ident, "y"),
                                value: "y".to_string()
                            })
                        })]
                    }),
                })
            })
        );
        assert_eq!(errors, vec![]);
        assert_eq!(stmts.len(), 1);
    }

    #[test]
    fn function_literal() {
        let input = "fn(x, y) { x + y; }";
        let (stmts, _) = parser_helper(input);

        assert_eq!(
            stmts[0],
            Stmt::Expr(ExprStmt {
                token: Token::new(TokenType::Function, "fn"),
                expr: Expr::Fn(FuncLiteral {
                    token: Token::new(TokenType::Function, "fn"),
                    params: vec![
                        Identifier {
                            token: Token::new(TokenType::Ident, "x"),
                            value: "x".to_string()
                        },
                        Identifier {
                            token: Token::new(TokenType::Ident, "y"),
                            value: "y".to_string()
                        },
                    ],
                    body: BlockStmt {
                        token: Token::new(TokenType::LBrace, "{"),
                        stmts: vec![Stmt::Expr(ExprStmt {
                            token: Token::new(TokenType::Ident, "x"),
                            expr: Expr::Infix(InfixExpr {
                                token: Token::new(TokenType::Plus, "+"),
                                left: Expr::Ident(Identifier {
                                    token: Token::new(TokenType::Ident, "x"),
                                    value: "x".to_string()
                                })
                                .into(),
                                op: "+".to_string(),
                                right: Expr::Ident(Identifier {
                                    token: Token::new(TokenType::Ident, "y"),
                                    value: "y".to_string()
                                })
                                .into(),
                            })
                        })]
                    }
                })
            })
        );
    }

    #[test]
    fn func_params() {
        let cases = [
            ("fn() {};", vec![]),
            ("fn(x) {};", vec!["x"]),
            ("fn(x, y, z) {};", vec!["x", "y", "z"]),
        ];

        for (input, params) in cases {
            let (stmts, _) = parser_helper(input);
            assert_eq!(
                stmts[0],
                Stmt::Expr(ExprStmt {
                    token: Token::new(TokenType::Function, "fn"),
                    expr: Expr::Fn(FuncLiteral {
                        token: Token::new(TokenType::Function, "fn"),
                        params: params
                            .iter()
                            .map(|x| Identifier {
                                token: Token::new(TokenType::Ident, x),
                                value: x.to_string()
                            })
                            .collect(),
                        body: BlockStmt {
                            token: Token::new(TokenType::LBrace, "{"),
                            stmts: vec![]
                        }
                    })
                })
            );
        }
    }

    #[test]
    fn call_expr() {
        let input = "add(1, 2 + 3, 4 * 5)";
        let (stmts, errors) = parser_helper(input);
        assert_eq!(errors, vec![]);
        assert_eq!(
            stmts[0],
            Stmt::Expr(ExprStmt {
                token: Token::new(TokenType::Ident, "add"),
                expr: Expr::Call(CallExpr {
                    token: Token::new(TokenType::LParen, "("),
                    func: Expr::Ident(Identifier {
                        token: Token::new(TokenType::Ident, "add"),
                        value: "add".to_string()
                    })
                    .into(),
                    args: vec![
                        Expr::Int(IntLiteral {
                            token: Token::new(TokenType::Int, "1"),
                            value: 1
                        }),
                        Expr::Infix(InfixExpr {
                            token: Token::new(TokenType::Plus, "+"),
                            left: Expr::Int(IntLiteral {
                                token: Token::new(TokenType::Int, "2"),
                                value: 2
                            })
                            .into(),
                            op: "+".to_string(),
                            right: Expr::Int(IntLiteral {
                                token: Token::new(TokenType::Int, "3"),
                                value: 3
                            })
                            .into(),
                        }),
                        Expr::Infix(InfixExpr {
                            token: Token::new(TokenType::Asterisk, "*"),
                            left: Expr::Int(IntLiteral {
                                token: Token::new(TokenType::Int, "4"),
                                value: 4
                            })
                            .into(),
                            op: "*".to_string(),
                            right: Expr::Int(IntLiteral {
                                token: Token::new(TokenType::Int, "5"),
                                value: 5
                            })
                            .into(),
                        }),
                    ]
                })
            })
        )
    }
}
*/
