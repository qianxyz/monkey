// TODO: many fields are made public ATM. When we have a working parser,
// we will be able to construct nodes and compare all fields by deriving `Eq`.
// Before that we can only extract some fields and compare them.

use crate::token::Token;

/// A node in AST.
pub trait Node {
    fn token_literal(&self) -> String;
}

/// Statements
pub enum Stmt {
    Let(LetStmt),
}

impl Node for Stmt {
    fn token_literal(&self) -> String {
        match self {
            Self::Let(s) => s.token_literal(),
        }
    }
}

/// Expressions
pub enum Expr {
    Ident(Identifier),
    // TODO: this is a placeholder variant before we can parse valid expressions
    Dummy,
}

impl Node for Expr {
    fn token_literal(&self) -> String {
        match self {
            Self::Ident(e) => e.token_literal(),
            _ => todo!(),
        }
    }
}

/// The root node of every AST.
/// A program is a series of statements.
pub struct Program {
    pub stmts: Vec<Stmt>,
}

impl Node for Program {
    fn token_literal(&self) -> String {
        match self.stmts.first() {
            Some(stmt) => stmt.token_literal(),
            None => String::new(),
        }
    }
}

/// A `let` statement.
pub struct LetStmt {
    /// This will always be `Token { Let, "let" }`
    pub token: Token,

    /// The `x` in `let x = 5 * 5`
    pub name: Box<Identifier>,

    /// The `5 * 5` in `let x = 5 * 5`
    pub value: Expr,
}

impl Node for LetStmt {
    fn token_literal(&self) -> String {
        self.token.literal().to_string()
    }
}

/// An Identifier (as an expression)
pub struct Identifier {
    /// This will be like `Token { Ident, "x" }`
    pub token: Token,

    /// The name of the identifier
    pub value: String,
}

impl Node for Identifier {
    fn token_literal(&self) -> String {
        self.token.literal().to_string()
    }
}
