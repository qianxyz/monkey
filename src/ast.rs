// TODO: many fields are made public ATM. When we have a working parser,
// we will be able to construct nodes and compare all fields by deriving `Eq`.
// Before that we can only extract some fields and compare them.

use std::fmt;

use crate::token::Token;

/// A node in AST.
pub trait Node: fmt::Display {
    fn token_literal(&self) -> String;
}

/// Statements
pub enum Stmt {
    Let(LetStmt),
    Return(ReturnStmt),
    Expr(ExprStmt),
}

impl Node for Stmt {
    fn token_literal(&self) -> String {
        match self {
            Self::Let(s) => s.token_literal(),
            Self::Return(s) => s.token_literal(),
            Self::Expr(s) => s.token_literal(),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Let(s) => write!(f, "{}", s)?,
            Self::Return(s) => write!(f, "{}", s)?,
            Self::Expr(s) => write!(f, "{}", s)?,
        }
        Ok(())
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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(e) => write!(f, "{}", e)?,
            _ => todo!(),
        }
        Ok(())
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

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for stmt in &self.stmts {
            write!(f, "{}", stmt)?;
        }
        Ok(())
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

impl fmt::Display for LetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} = {};",
            self.token_literal(),
            self.name,
            self.value
        )
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

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// A `return` statement.
pub struct ReturnStmt {
    /// This will always be `Token { Return, "return" }`
    pub token: Token,

    /// The value to return
    pub return_value: Expr,
}

impl Node for ReturnStmt {
    fn token_literal(&self) -> String {
        self.token.literal().to_string()
    }
}

impl fmt::Display for ReturnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {};", self.token_literal(), self.return_value)
    }
}

/// An expression itself can also be an statement. For example,
///     let x = 5;
///     x + 10;
/// The second line is an expression statment.
/// With this wrapper, an expression can be added to the statements
/// of an ast::Program (which is the sole purpose of the wrapper).
pub struct ExprStmt {
    /// The first token of the expression
    pub token: Token,

    /// The actual expression wrapped inside
    pub expr: Expr,
}

impl Node for ExprStmt {
    fn token_literal(&self) -> String {
        self.token.literal().to_string()
    }
}

impl fmt::Display for ExprStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}

#[cfg(test)]
mod tests {
    use crate::token::TokenType;

    use super::*;

    #[test]
    fn display_ast() {
        let token = Token::new(TokenType::Let, "let");
        let name = Identifier {
            token: Token::new(TokenType::Ident, "my_var"),
            value: "my_var".to_string(),
        };
        let value = Identifier {
            token: Token::new(TokenType::Ident, "another_var"),
            value: "another_var".to_string(),
        };

        let stmt = LetStmt {
            token,
            name: name.into(),
            value: Expr::Ident(value),
        };

        let program = Program {
            stmts: vec![Stmt::Let(stmt)],
        };

        assert_eq!(program.to_string(), "let my_var = another_var;");
    }
}
