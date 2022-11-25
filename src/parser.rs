use std::collections::HashMap;
use std::mem;

use crate::ast::*;
use crate::lexer::Lexer;
use crate::token::{Token, TokenType};

type PrefixParseFn = fn(&mut Parser) -> Option<Expr>;
type InfixParseFn = fn(&mut Parser, Expr) -> Option<Expr>;

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

impl From<&TokenType> for Precedence {
    fn from(t: &TokenType) -> Self {
        use TokenType::*;
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

        ret.register_prefix(TokenType::True, Self::parse_boolean);
        ret.register_prefix(TokenType::False, Self::parse_boolean);
        ret.register_prefix(TokenType::LParen, Self::parse_grouped_expr);
        ret.register_prefix(TokenType::If, Self::parse_if_expr);
        ret.register_prefix(TokenType::Function, Self::parse_func_literal);

        ret.register_infix(TokenType::Plus, Self::parse_infix_expr);
        ret.register_infix(TokenType::Minus, Self::parse_infix_expr);
        ret.register_infix(TokenType::Asterisk, Self::parse_infix_expr);
        ret.register_infix(TokenType::Slash, Self::parse_infix_expr);
        ret.register_infix(TokenType::LT, Self::parse_infix_expr);
        ret.register_infix(TokenType::GT, Self::parse_infix_expr);
        ret.register_infix(TokenType::EQ, Self::parse_infix_expr);
        ret.register_infix(TokenType::NQ, Self::parse_infix_expr);

        ret.register_infix(TokenType::LParen, Self::parse_call_expr);

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
        let Some(f) = self.prefix_parse_fns.get(self.cur.ttype()) else {
            self.no_prefix_parse_fn_error(*self.cur.ttype());
            return None
        };
        let mut left = f(self)?;

        // NOTE: this precedence check covers more cases, e.g., when we peek
        // a semicolon or eof, since their precedence would be LOWEST.
        while precedence < self.peek_precedence() {
            let Some(&g) = self.infix_parse_fns.get(self.peek.ttype()) else {
                // TODO: maybe we should have a `ParseError::NoInfixParseFn`?
                return Some(left);
            };
            self.next_token();
            left = g(self, left)?;
        }

        Some(left)
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

    fn parse_infix_expr(&mut self, left: Expr) -> Option<Expr> {
        let cur = self.cur.clone();
        let op = cur.literal().to_string();

        let precedence = self.cur_precedence();
        self.next_token();
        let right = self.parse_expr(precedence)?;

        Some(Expr::Infix(InfixExpr {
            token: cur,
            left: left.into(),
            op,
            right: right.into(),
        }))
    }

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

        assert_eq!(errors, vec![]);
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

        assert_eq!(errors, vec![]);
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

        assert_eq!(errors, vec![]);
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

        assert_eq!(errors, vec![]);
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
            assert_eq!(errors, vec![]);
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
            assert_eq!(errors, vec![]);
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

    #[test]
    fn precedence_parsing() {
        let cases = [
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
            ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
            (
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g))",
            ),
        ];

        for (input, expect) in cases {
            let mut parser = Parser::new(Lexer::new(input));
            let program = parser.parse_program();
            assert!(parser.errors.is_empty());
            assert_eq!(program.to_string(), expect);
        }
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
