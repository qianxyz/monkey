use std::mem;

use crate::ast::Program;
use crate::lexer::Lexer;
use crate::token::Token;

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

    fn parse_program(&mut self) -> Program {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Stmt, Node};

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
