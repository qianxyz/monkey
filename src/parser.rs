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
}

impl<'a> Parser<'a> {
    fn new(lexer: &'a mut Lexer) -> Self {
        // set first two tokens
        let cur = lexer.next_token();
        let peek = lexer.next_token();

        Self { lexer, cur, peek }
    }

    fn next_token(&mut self) {
        self.cur = mem::replace(&mut self.peek, self.lexer.next_token());
    }

    fn parse_program(&mut self) -> ast::Program {
        let mut stmts = Vec::new();

        while !self.cur.is_eof() {
            if let Ok(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            }
            self.next_token();
        }

        ast::Program { stmts }
    }

    fn parse_stmt(&mut self) -> Result<ast::Stmt, ParserError> {
        match self.cur.ttype() {
            TokenType::Let => Ok(ast::Stmt::Let(self.parse_let_stmt()?)),
            _ => todo!(),
        }
    }

    fn parse_let_stmt(&mut self) -> Result<ast::LetStmt, ParserError> {
        // TODO: token owns a String, so we have to explicitly clone here.
        // maybe it can just hold a reference &str so it can be copied.
        let token = self.cur.clone(); // the `Let` token

        // `Let` must be followed by an identifier
        if !self.expect_peek(TokenType::Ident) {
            return Err(ParserError);
        }
        let name = ast::Identifier {
            token: self.cur.clone(),
            value: self.cur.literal().to_string(),
        };

        // the next token must be `=`
        if !self.expect_peek(TokenType::Assign) {
            return Err(ParserError);
        }

        // TODO: we skip parsing the expression for now
        while !self.cur_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        Ok(ast::LetStmt {
            token: token,
            name: name.into(),
            value: ast::Expr::Dummy,
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
            false
        }
    }
}

struct ParserError;

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
}
