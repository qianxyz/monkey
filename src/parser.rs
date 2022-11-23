use std::collections::HashMap;
use std::mem;

use crate::ast;
use crate::lexer::Lexer;
use crate::token::{Token, TokenType};

type PrefixParseFn = fn(&mut Parser) -> Option<ast::Expr>;
type InfixParseFn = fn(&mut Parser, ast::Expr) -> ast::Expr;

enum Precedence {
    Lowest,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // fn(X)
}

struct Parser {
    /// a lexer to spit out tokens
    lexer: Lexer,

    /// current parse point
    cur: Token,

    /// the next parse point
    peek: Token,

    /// collection of errors
    errors: Vec<ParseError>,

    prefix_parse_fns: HashMap<TokenType, PrefixParseFn>,

    infix_parse_fns: HashMap<TokenType, InfixParseFn>,
}

impl Parser {
    fn new(mut lexer: Lexer) -> Self {
        // set first two tokens
        let cur = lexer.next_token();
        let peek = lexer.next_token();

        let mut ret = Self {
            lexer,
            cur,
            peek,
            errors: Vec::new(),
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
        };

        ret.register_prefix(TokenType::Ident, Self::parse_identifier);
        ret.register_prefix(TokenType::Int, Self::parse_int_literal);

        ret
    }

    fn register_prefix(&mut self, t: TokenType, f: PrefixParseFn) {
        self.prefix_parse_fns.insert(t, f);
    }

    fn register_infix(&mut self, t: TokenType, f: InfixParseFn) {
        self.infix_parse_fns.insert(t, f);
    }

    fn next_token(&mut self) {
        self.cur = mem::replace(&mut self.peek, self.lexer.next_token());
    }

    fn parse_program(&mut self) -> ast::Program {
        let mut stmts = Vec::new();

        while !self.cur.is_eof() {
            if let Some(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            }
            self.next_token();
        }

        ast::Program { stmts }
    }

    // ? Most of the parsing functions return Option<ast::Stmt>, which is None
    // when we encounter a parsing error. The error itself, however,
    // is not returned directly, and instead is handled by `Parser::peek_error`.
    // This grants more flexibility, e.g., raising multiple errors
    // in one parsing function; If such need never rises at the end,
    // maybe it's better to be explicit by returning Result<Stmt, ParseError>.
    fn parse_stmt(&mut self) -> Option<ast::Stmt> {
        match self.cur.ttype() {
            TokenType::Let => Some(ast::Stmt::Let(self.parse_let_stmt()?)),
            TokenType::Return => Some(ast::Stmt::Return(self.parse_return_stmt()?)),
            _ => Some(ast::Stmt::Expr(self.parse_expr_stmt()?)),
        }
    }

    fn parse_let_stmt(&mut self) -> Option<ast::LetStmt> {
        let token = self.cur.clone(); // the `Let` token

        // `Let` must be followed by an identifier
        if !self.expect_peek(TokenType::Ident) {
            return None;
        }
        let name = ast::Identifier {
            token: self.cur.clone(),
            value: self.cur.literal().to_string(),
        };

        // the next token must be `=`
        if !self.expect_peek(TokenType::Assign) {
            return None;
        }

        // TODO: we skip parsing the expression for now
        while !self.cur_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        Some(ast::LetStmt {
            token,
            name,
            value: ast::Expr::Dummy,
        })
    }

    fn parse_return_stmt(&mut self) -> Option<ast::ReturnStmt> {
        let token = self.cur.clone(); // the `Return` token
        self.next_token();

        // TODO: we skip parsing the expression for now
        while !self.cur_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        Some(ast::ReturnStmt {
            token,
            return_value: ast::Expr::Dummy,
        })
    }

    fn parse_expr_stmt(&mut self) -> Option<ast::ExprStmt> {
        let token = self.cur.clone();
        let expr = self.parse_expr(Precedence::Lowest)?;

        // An expression statement ends with an optional semicolon.
        // This makes REPL friendlier, since you can type `5 + 5`
        // and it's the same as `5 + 5;`.
        if self.peek_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        Some(ast::ExprStmt { token, expr })
    }

    fn parse_expr(&mut self, precedence: Precedence) -> Option<ast::Expr> {
        // clippy suggests this one-liner:
        // self.prefix_parse_fns.get(self.cur.ttype()).map(|f| f(self))
        // But it does not work, since closure requires unique access to self,
        // but self is already borrowed by accessing `prefix_parse_fn`.
        // Instead, we must end this borrow by extracting `f` first.
        if let Some(f) = self.prefix_parse_fns.get(self.cur.ttype()) {
            f(self)
        } else {
            None
        }
    }

    fn parse_identifier(&mut self) -> Option<ast::Expr> {
        Some(ast::Expr::Ident(ast::Identifier {
            token: self.cur.clone(),
            value: self.cur.literal().to_string(),
        }))
    }

    fn parse_int_literal(&mut self) -> Option<ast::Expr> {
        let token = self.cur.clone();
        match self.cur.literal().parse::<i32>() {
            Ok(value) => Some(ast::Expr::Int(ast::IntLiteral { token, value })),
            Err(_) => {
                self.errors
                    .push(ParseError::ParseIntError(self.cur.literal().to_string()));
                None
            }
        }
    }

    fn cur_token_is(&self, t: TokenType) -> bool {
        self.cur.ttype() == &t
    }

    fn peek_token_is(&self, t: TokenType) -> bool {
        self.peek.ttype() == &t
    }

    /// An `assertion function`.
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
}

#[derive(Debug, PartialEq, Eq)]
enum ParseError {
    UnexpectedToken { expected: TokenType, got: TokenType },
    ParseIntError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parser_helper(input: &str) -> (Vec<ast::Stmt>, Vec<ParseError>) {
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let program = parser.parse_program();

        (program.stmts, parser.errors)
    }

    #[test]
    fn let_stmts() {
        let input = "\
let x = 5;
let y = 10;
let foobar = 838383;
";
        let expected = [("x", 5), ("y", 10), ("foobar", 838383)];

        let (stmts, errors) = parser_helper(input);

        assert_eq!(stmts.len(), 3);
        assert!(errors.is_empty());

        for i in 0..3 {
            assert_eq!(
                stmts[i],
                ast::Stmt::Let(ast::LetStmt {
                    token: Token::new(TokenType::Let, "let"),
                    name: ast::Identifier {
                        token: Token::new(TokenType::Ident, expected[i].0),
                        value: expected[i].0.to_string(),
                    },
                    value: ast::Expr::Int(ast::IntLiteral {
                        token: Token::new(TokenType::Int, &expected[i].1.to_string()),
                        value: expected[i].1
                    })
                })
            )
        }
    }

    #[test]
    fn let_stmts_error() {
        let input = "\
let x 5;
let = 10;
let 838383;
";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        parser.parse_program();
        let mut errors = parser.errors.iter();
        assert_eq!(
            errors.next().unwrap(),
            &ParseError::UnexpectedToken {
                expected: TokenType::Assign,
                got: TokenType::Int,
            }
        );
        assert_eq!(
            errors.next().unwrap(),
            &ParseError::UnexpectedToken {
                expected: TokenType::Ident,
                got: TokenType::Assign,
            }
        );
        assert_eq!(
            errors.next().unwrap(),
            &ParseError::UnexpectedToken {
                expected: TokenType::Ident,
                got: TokenType::Int,
            }
        );
        assert!(errors.next().is_none());
    }

    #[test]
    fn return_stmts() {
        let input = "\
return 5;
return 10;
return 993322;
";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        let mut stmts = program.stmts.iter();
        for _ in 0..3 {
            let stmt = stmts.next().unwrap();
            assert_eq!(stmt.token_literal(), "return");
            let Stmt::Return(s) = stmt else { panic!() };
            assert_eq!(s.token_literal(), "return");
        }
        assert!(stmts.next().is_none());
    }

    #[test]
    fn ident_expr() {
        let input = "foobar;";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        let mut stmts = program.stmts.iter();

        let s = stmts.next().unwrap();
        let Stmt::Expr(s) = s else { panic!() };
        let Expr::Ident(e) = &s.expr else { panic!() };
        assert_eq!(e.value, "foobar");
        assert_eq!(e.token_literal(), "foobar");

        assert!(stmts.next().is_none());
    }

    #[test]
    fn int_literal_expr() {
        let input = "5;";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        let mut stmts = program.stmts.iter();

        let s = stmts.next().unwrap();
        let Stmt::Expr(s) = s else { panic!() };
        let Expr::Int(e) = &s.expr else { panic!() };
        assert_eq!(e.value, 5);
        assert_eq!(e.token_literal(), "5");

        assert!(stmts.next().is_none());
    }

    #[test]
    fn too_big_int() {
        let input = "100000000000000000000000";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        parser.parse_program();
        let mut errors = parser.errors.iter();

        assert_eq!(
            errors.next().unwrap(),
            &ParseError::ParseIntError(input.to_string())
        );

        assert!(errors.next().is_none());
    }
}
