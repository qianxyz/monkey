use std::collections::HashMap;
use std::mem;

use crate::ast::{
    Expr, ExprStmt, Identifier, InfixExpr, IntLiteral, LetStmt, PrefixExpr, Program, ReturnStmt,
    Stmt,
};
use crate::lexer::Lexer;
use crate::token::{Token, TokenType};

type PrefixParseFn = fn(&mut Parser) -> Option<Expr>;
type InfixParseFn = fn(&mut Parser, Expr) -> Expr;

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
        ret.register_prefix(TokenType::Bang, Self::parse_prefix_expr);
        ret.register_prefix(TokenType::Minus, Self::parse_prefix_expr);

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

    fn parse_program(&mut self) -> Program {
        let mut stmts = Vec::new();

        while !self.cur.is_eof() {
            if let Some(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            }
            self.next_token();
        }

        Program { stmts }
    }

    // ? Most of the parsing functions return Option<ast::Stmt>, which is None
    // when we encounter a parsing error. The error itself, however,
    // is not returned directly, and instead is handled by each function.
    // This grants more flexibility, e.g., raising multiple errors
    // in one parsing function; If such need never rises at the end,
    // maybe it's better to be explicit by returning Result<Stmt, ParseError>.
    fn parse_stmt(&mut self) -> Option<Stmt> {
        match self.cur.ttype() {
            TokenType::Let => Some(Stmt::Let(self.parse_let_stmt()?)),
            TokenType::Return => Some(Stmt::Return(self.parse_return_stmt()?)),
            _ => Some(Stmt::Expr(self.parse_expr_stmt()?)),
        }
    }

    fn parse_let_stmt(&mut self) -> Option<LetStmt> {
        let token = self.cur.clone(); // the `Let` token

        // `Let` must be followed by an identifier
        if !self.expect_peek(TokenType::Ident) {
            return None;
        }
        let name = Identifier {
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

        Some(LetStmt {
            token,
            name,
            value: Expr::Dummy,
        })
    }

    fn parse_return_stmt(&mut self) -> Option<ReturnStmt> {
        let token = self.cur.clone(); // the `Return` token
        self.next_token();

        // TODO: we skip parsing the expression for now
        while !self.cur_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        Some(ReturnStmt {
            token,
            return_value: Expr::Dummy,
        })
    }

    fn parse_expr_stmt(&mut self) -> Option<ExprStmt> {
        let token = self.cur.clone();
        let expr = self.parse_expr(Precedence::Lowest)?;

        // An expression statement ends with an optional semicolon.
        // This makes REPL friendlier, since you can type `5 + 5`
        // and it's the same as `5 + 5;`.
        if self.peek_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        Some(ExprStmt { token, expr })
    }

    fn parse_expr(&mut self, precedence: Precedence) -> Option<Expr> {
        // `map` doesn't work here; we must extract `f` (func pointer is Copy)
        // and end the first self borrow before calling `f(self)`.
        if let Some(f) = self.prefix_parse_fns.get(self.cur.ttype()) {
            f(self)
        } else {
            self.no_prefix_parse_fn_error(*self.cur.ttype());
            None
        }
    }

    fn parse_identifier(&mut self) -> Option<Expr> {
        Some(Expr::Ident(Identifier {
            token: self.cur.clone(),
            value: self.cur.literal().to_string(),
        }))
    }

    fn parse_int_literal(&mut self) -> Option<Expr> {
        let token = self.cur.clone();
        match self.cur.literal().parse::<i32>() {
            Ok(value) => Some(Expr::Int(IntLiteral { token, value })),
            Err(_) => {
                self.errors
                    .push(ParseError::ParseIntError(self.cur.literal().to_string()));
                None
            }
        }
    }

    fn parse_prefix_expr(&mut self) -> Option<Expr> {
        let cur = self.cur.clone();
        let op = cur.literal().to_string();
        self.next_token();
        let right = self.parse_expr(Precedence::Prefix)?;

        Some(Expr::Prefix(PrefixExpr {
            token: cur,
            op,
            right: right.into(),
        }))
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
}

#[derive(Debug, PartialEq, Eq)]
enum ParseError {
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
    fn let_stmts() {
        let input = "\
let x = 5;
let y = 10;
let foobar = 838383;
";
        let expected = [("x", "5"), ("y", "10"), ("foobar", "838383")];

        let (stmts, errors) = parser_helper(input);

        for (s, (x, n)) in stmts.iter().zip(expected.into_iter()) {
            assert_eq!(
                s,
                &Stmt::Let(LetStmt {
                    token: Token::new(TokenType::Let, "let"),
                    name: Identifier {
                        token: Token::new(TokenType::Ident, x),
                        value: x.to_string(),
                    },
                    value: Expr::Int(IntLiteral {
                        token: Token::new(TokenType::Int, n),
                        value: n.parse().unwrap()
                    })
                })
            )
        }

        assert_eq!(errors.first(), None);
        assert_eq!(stmts.len(), 3);
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
    fn return_stmts() {
        let input = "\
return 5;
return 10;
return 993322;
";
        let expected = ["5", "10", "993322"];

        let (stmts, errors) = parser_helper(input);

        for (s, n) in stmts.iter().zip(expected.into_iter()) {
            assert_eq!(
                s,
                &Stmt::Return(ReturnStmt {
                    token: Token::new(TokenType::Return, "return"),
                    return_value: Expr::Int(IntLiteral {
                        token: Token::new(TokenType::Int, n),
                        value: n.parse().unwrap(),
                    })
                })
            )
        }

        assert_eq!(errors.first(), None);
        assert_eq!(stmts.len(), 3);
    }

    #[test]
    fn ident_expr() {
        let input = "foobar;";
        let (stmts, errors) = parser_helper(input);

        assert_eq!(
            stmts[0],
            Stmt::Expr(ExprStmt {
                token: Token::new(TokenType::Ident, "foobar"),
                expr: Expr::Ident(Identifier {
                    token: Token::new(TokenType::Ident, "foobar"),
                    value: "foobar".to_string()
                })
            })
        );

        assert_eq!(errors.first(), None);
        assert_eq!(stmts.len(), 1);
    }

    #[test]
    fn int_literal_expr() {
        let input = "5;";
        let (stmts, errors) = parser_helper(input);

        assert_eq!(
            stmts[0],
            Stmt::Expr(ExprStmt {
                token: Token::new(TokenType::Int, "5"),
                expr: Expr::Int(IntLiteral {
                    token: Token::new(TokenType::Int, "5"),
                    value: 5
                })
            })
        );

        assert_eq!(errors.first(), None);
        assert_eq!(stmts.len(), 1);
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
    fn prefix_exprs() {
        use TokenType::*;
        let inputs = [("!5", Bang, "!", 5), ("-15", Minus, "-", 15)];

        for (input, ttype, op, val) in inputs {
            let (stmts, errors) = parser_helper(input);
            assert_eq!(errors.first(), None);
            assert_eq!(stmts.len(), 1);
            assert_eq!(
                stmts[0],
                Stmt::Expr(ExprStmt {
                    token: Token::new(ttype, op),
                    expr: Expr::Prefix(PrefixExpr {
                        token: Token::new(ttype, op),
                        op: op.to_string(),
                        right: Box::new(Expr::Int(IntLiteral {
                            token: Token::new(TokenType::Int, &val.to_string()),
                            value: val
                        }))
                    })
                })
            )
        }
    }

    #[test]
    fn infix_expr() {
        use TokenType::*;
        let inputs = [
            ("5 + 5;", Plus, "+"),
            ("5 - 5;", Minus, "-"),
            ("5 * 5;", Asterisk, "*"),
            ("5 / 5;", Slash, "/"),
            ("5 > 5;", GT, ">"),
            ("5 < 5;", LT, "<"),
            ("5 == 5;", EQ, "=="),
            ("5 != 5;", NQ, "!="),
        ];
        let five = Token::new(TokenType::Int, "5");

        for (input, ttype, op) in inputs {
            let (stmts, errors) = parser_helper(input);
            assert_eq!(errors.first(), None);
            assert_eq!(
                stmts[0],
                Stmt::Expr(ExprStmt {
                    token: five.clone(),
                    expr: Expr::Infix(InfixExpr {
                        token: Token::new(ttype, op),
                        left: Box::new(Expr::Int(IntLiteral {
                            token: five.clone(),
                            value: 5
                        })),
                        op: op.to_string(),
                        right: Box::new(Expr::Int(IntLiteral {
                            token: five.clone(),
                            value: 5
                        }))
                    })
                })
            )
        }
    }
}
