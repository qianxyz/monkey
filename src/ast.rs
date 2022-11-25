// TODO: many fields are made public ATM. When we have a working parser,
// we will be able to construct nodes and compare all fields by deriving `Eq`.
// Before that we can only extract some fields and compare them.

use std::fmt;

use crate::token::Token;

/// A node in AST.
pub trait Node: fmt::Debug + fmt::Display + PartialEq + Eq {
    fn token_literal(&self) -> &str;
}

/// A wrapper for various statements.
#[derive(Debug, PartialEq, Eq)]
pub enum Stmt {
    Let(LetStmt),
    Return(ReturnStmt),
    Expr(ExprStmt),
    Block(BlockStmt),
}

impl Node for Stmt {
    fn token_literal(&self) -> &str {
        match self {
            Self::Let(s) => s.token_literal(),
            Self::Return(s) => s.token_literal(),
            Self::Expr(s) => s.token_literal(),
            Self::Block(s) => s.token_literal(),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Let(s) => write!(f, "{}", s),
            Self::Return(s) => write!(f, "{}", s),
            Self::Expr(s) => write!(f, "{}", s),
            Self::Block(s) => write!(f, "{}", s),
        }
    }
}

/// A wrapper for various expressions.
#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Ident(Identifier),
    Int(IntLiteral),
    Prefix(PrefixExpr),
    Infix(InfixExpr),
    Bool(Boolean),
    If(IfExpr),
    Fn(FuncLiteral),
    Call(CallExpr),
    // TODO: this is a placeholder variant before we can parse valid expressions
    Dummy,
}

impl Node for Expr {
    fn token_literal(&self) -> &str {
        match self {
            Self::Ident(e) => e.token_literal(),
            Self::Int(e) => e.token_literal(),
            Self::Prefix(e) => e.token_literal(),
            Self::Infix(e) => e.token_literal(),
            Self::Bool(e) => e.token_literal(),
            Self::If(e) => e.token_literal(),
            Self::Fn(e) => e.token_literal(),
            Self::Call(e) => e.token_literal(),
            Self::Dummy => todo!(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(e) => write!(f, "{}", e),
            Self::Int(e) => write!(f, "{}", e),
            Self::Prefix(e) => write!(f, "{}", e),
            Self::Infix(e) => write!(f, "{}", e),
            Self::Bool(e) => write!(f, "{}", e),
            Self::If(e) => write!(f, "{}", e),
            Self::Fn(e) => write!(f, "{}", e),
            Self::Call(e) => write!(f, "{}", e),
            Self::Dummy => todo!(),
        }
    }
}

/// The root node of every AST.
/// A program is a series of statements.
#[derive(Debug, PartialEq, Eq)]
pub struct Program {
    pub stmts: Vec<Stmt>,
}

impl Node for Program {
    fn token_literal(&self) -> &str {
        match self.stmts.first() {
            Some(stmt) => stmt.token_literal(),
            None => "",
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
#[derive(Debug, PartialEq, Eq)]
pub struct LetStmt {
    /// This should always be `Token { type: Let, literal: "let" }`
    pub token: Token,

    /// The `x` in `let x = 5 * 5`
    pub name: Identifier,

    /// The `5 * 5` in `let x = 5 * 5`
    pub value: Expr,
}

impl Node for LetStmt {
    fn token_literal(&self) -> &str {
        self.token.literal()
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
#[derive(Debug, PartialEq, Eq)]
pub struct Identifier {
    /// This should be like `Token { type: Ident, literal: "x" }`
    pub token: Token,

    /// The name of the identifier
    pub value: String,
}

impl Node for Identifier {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// A `return` statement.
#[derive(Debug, PartialEq, Eq)]
pub struct ReturnStmt {
    /// This should always be `Token { type: Return, literal: "return" }`
    pub token: Token,

    /// The value to return
    pub return_value: Expr,
}

impl Node for ReturnStmt {
    fn token_literal(&self) -> &str {
        self.token.literal()
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
#[derive(Debug, PartialEq, Eq)]
pub struct ExprStmt {
    /// The first token of the expression
    pub token: Token,

    /// The actual expression wrapped inside
    pub expr: Expr,
}

impl Node for ExprStmt {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for ExprStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}

/// An integer literal like `5`.
#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteral {
    /// A token like `Token { type: Int, literal: "5" }`
    pub token: Token,

    /// The value of the integer
    pub value: i32,
}

impl Node for IntLiteral {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for IntLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token_literal())
    }
}

/// A prefix expression, like `-15` or `!5`.
#[derive(Debug, PartialEq, Eq)]
pub struct PrefixExpr {
    /// The prefix token like `-` or `!`
    pub token: Token,

    /// The operator as a string
    pub op: String,

    /// The expression at the right
    pub right: Box<Expr>,
}

impl Node for PrefixExpr {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for PrefixExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.op, self.right)
    }
}

/// An infix expression like `5 + 5`.
#[derive(Debug, PartialEq, Eq)]
pub struct InfixExpr {
    /// The operator token, e.g., `+`
    pub token: Token,

    /// The expression on the left
    pub left: Box<Expr>,

    /// The operator
    pub op: String,

    /// The expression on the right
    pub right: Box<Expr>,
}

impl Node for InfixExpr {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for InfixExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.op, self.right)
    }
}

/// A boolean literal.
#[derive(Debug, PartialEq, Eq)]
pub struct Boolean {
    /// The token `true` or `false`.
    pub token: Token,

    /// The literal value.
    pub value: bool,
}

impl Node for Boolean {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token_literal())
    }
}

/// An `if` expression.
#[derive(Debug, PartialEq, Eq)]
pub struct IfExpr {
    /// This should always be `Token { If, "if" }`
    pub token: Token,

    /// The condition controlling which branch to go into.
    pub condition: Box<Expr>,

    /// The block when condition is true.
    pub consequence: BlockStmt,

    /// The optional block when condition is false.
    pub alternative: Option<BlockStmt>,
}

impl Node for IfExpr {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for IfExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "if {} {}", self.condition, self.consequence)?;
        if let Some(s) = &self.alternative {
            write!(f, " else {}", s)?;
        }
        Ok(())
    }
}

/// A block of statements, surrounded by `{}`.
#[derive(Debug, PartialEq, Eq)]
pub struct BlockStmt {
    /// This should always be `{`
    pub token: Token,

    /// A collection of statements
    pub stmts: Vec<Stmt>,
}

impl Node for BlockStmt {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for BlockStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for s in &self.stmts {
            write!(f, "{}", s)?;
        }
        Ok(())
    }
}

/// A function, like `fn(x, y) { return x + y; }`
#[derive(Debug, PartialEq, Eq)]
pub struct FuncLiteral {
    /// This should always be `fn`
    pub token: Token,

    /// The parameters of the function
    pub params: Vec<Identifier>,

    /// The body of the function
    pub body: BlockStmt,
}

impl Node for FuncLiteral {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for FuncLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({}) {}",
            self.token_literal(),
            self.params
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.body
        )
    }
}

/// A function call, like `add(2, 3)`.
#[derive(Debug, PartialEq, Eq)]
pub struct CallExpr {
    /// The `(` token
    pub token: Token,

    /// An Identifier or a FuncLiteral: `add(2, 3)` or
    /// `fn(x, y) { x + y; }(2, 3)`
    pub func: Box<Expr>,

    /// The arguments
    pub args: Vec<Expr>,
}

impl Node for CallExpr {
    fn token_literal(&self) -> &str {
        self.token.literal()
    }
}

impl fmt::Display for CallExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.func,
            self.args
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
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
            name,
            value: Expr::Ident(value),
        };

        let program = Program {
            stmts: vec![Stmt::Let(stmt)],
        };

        assert_eq!(program.to_string(), "let my_var = another_var;");
    }
}
