use std::mem;

use crate::ast;
use crate::lexer::Lexer;
use crate::token::{Token, TokenType};

struct Parser<'a> {
    /// a lexer to spit out tokens
    lexer: &'a mut Lexer,

    /// current parse point
    cur: Token,

    /// the next parse point
    peek: Token,

    /// collection of errors
    errors: Vec<ParserError>,
}

impl<'a> Parser<'a> {
    fn new(lexer: &'a mut Lexer) -> Self {
        // set first two tokens
        let cur = lexer.next_token();
        let peek = lexer.next_token();

        Self {
            lexer,
            cur,
            peek,
            errors: Vec::new(),
        }
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

    fn parse_stmt(&mut self) -> Option<ast::Stmt> {
        match self.cur.ttype() {
            TokenType::Let => Some(ast::Stmt::Let(self.parse_let_stmt()?)),
            TokenType::Return => Some(ast::Stmt::Return(self.parse_return_stmt()?)),
            _ => None,
        }
    }

    // TODO: this function returning None means we have a ParserError.
    // Since every let statement is either an ast::LetStmt or a ParserError,
    // it may be better to return Result<> here.
    fn parse_let_stmt(&mut self) -> Option<ast::LetStmt> {
        // TODO: token owns a String, so we have to explicitly clone here.
        // maybe it can just hold a reference &str so it can be copied.
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
            name: name.into(),
            value: ast::Expr::Dummy,
        })
    }

    fn parse_return_stmt(&mut self) -> Option<ast::ReturnStmt> {
        let token = self.cur.clone();
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

    fn cur_token_is(&self, t: TokenType) -> bool {
        self.cur.ttype() == &t
    }

    fn peek_token_is(&self, t: TokenType) -> bool {
        self.peek.ttype() == &t
    }

    /// An `assertion function`, where we only advance parse point
    /// if the next token is of expected type.
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
        let e = ParserError {
            expected: t,
            got: *self.peek.ttype(),
        };
        self.errors.push(e);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ParserError {
    expected: TokenType,
    got: TokenType,
}

#[cfg(test)]
mod tests {
    use crate::ast::{Node, Stmt};

    use super::*;

    fn let_stmt_helper(s: &Stmt, name: &str) {
        assert_eq!(s.token_literal(), "let");
        let Stmt::Let(s) = s else { panic!() };
        assert_eq!(s.name.value, name);
        assert_eq!(s.name.token_literal(), name);
    }

    #[test]
    fn let_stmts() {
        let input = "\
let x = 5;
let y = 10;
let foobar = 838383;
";
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);

        let program = parser.parse_program();
        let mut stmts = program.stmts.iter();

        let_stmt_helper(stmts.next().unwrap(), "x");
        let_stmt_helper(stmts.next().unwrap(), "y");
        let_stmt_helper(stmts.next().unwrap(), "foobar");
        assert!(stmts.next().is_none());
    }

    #[test]
    fn let_stmts_error() {
        let input = "\
let x 5;
let = 10;
let 838383;
";
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program();
        assert!(program.stmts.is_empty()); // no valid statements
        let mut errors = parser.errors.iter();
        assert_eq!(
            errors.next().unwrap(),
            &ParserError {
                expected: TokenType::Assign,
                got: TokenType::Int,
            }
        );
        assert_eq!(
            errors.next().unwrap(),
            &ParserError {
                expected: TokenType::Ident,
                got: TokenType::Assign,
            }
        );
        assert_eq!(
            errors.next().unwrap(),
            &ParserError {
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
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
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
}
