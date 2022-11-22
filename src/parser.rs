use std::collections::HashMap;
use std::mem;

use crate::ast;
use crate::lexer::Lexer;
use crate::token::{Token, TokenType};

type PrefixParseFn = fn(&mut Parser) -> ast::Expr;
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
    errors: Vec<ParserError>,

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

    fn parse_stmt(&mut self) -> Option<ast::Stmt> {
        match self.cur.ttype() {
            TokenType::Let => Some(ast::Stmt::Let(self.parse_let_stmt()?)),
            TokenType::Return => Some(ast::Stmt::Return(self.parse_return_stmt()?)),
            _ => Some(ast::Stmt::Expr(self.parse_expr_stmt()?)),
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
        #[allow(clippy::manual_map)]
        if let Some(f) = self.prefix_parse_fns.get(self.cur.ttype()) {
            Some(f(self))
        } else {
            None
        }
    }

    fn parse_identifier(&mut self) -> ast::Expr {
        ast::Expr::Ident(ast::Identifier {
            token: self.cur.clone(),
            value: self.cur.literal().to_string(),
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
    use crate::ast::{Expr, Node, Stmt};

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
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

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
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
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
}
