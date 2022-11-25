use std::fmt;

use crate::token::Token;

/// A program is a list of statements
#[derive(Debug, PartialEq, Eq)]
pub struct Program(pub Vec<Stmt>);

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for stmt in &self.0 {
            writeln!(f, "{}", stmt)?;
        }
        Ok(())
    }
}

/// Statements
#[derive(Debug, PartialEq, Eq)]
pub enum Stmt {
    /// let <ident> = <expr>
    Let(Ident, Expr),

    /// return <expr>
    Ret(Expr),

    /// An expression as a statement, for REPL convenience
    Expr(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Let(i, e) => write!(f, "let {} = {};", i, e),
            Self::Ret(e) => write!(f, "return {};", e),
            Self::Expr(e) => write!(f, "{};", e),
        }
    }
}

/// A block of statements, wrapped in braces
#[derive(Debug, PartialEq, Eq)]
pub struct Block(pub Vec<Stmt>);

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{ {} }}",
            self.0
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

/// Expressions
#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    /// An identifier as an expression
    Ident(Ident),

    /// An int literal
    Int(i32),

    /// A bool literal
    Bool(bool),

    /// A prefix expression
    Prefix {
        op: Token, // `-` or `!`
        right: Box<Expr>,
    },

    /// An infix expression
    Infix {
        op: Token, // `+`, `*`, etc.
        left: Box<Expr>,
        right: Box<Expr>,
    },

    /// if (cond) { consq }
    /// if (cond) { consq } else { alter }
    If {
        cond: Box<Expr>,
        consq: Block,
        alter: Option<Block>,
    },

    /// fn(params) { body }
    Fn { params: Vec<Ident>, body: Block },

    /// A function call
    Call {
        func: Box<Expr>, // identifier or function literal
        args: Vec<Expr>,
    },
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(i) => write!(f, "{}", i),
            Self::Int(n) => write!(f, "{}", n),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Prefix { op, right } => write!(f, "({}{})", op, right),
            Self::Infix { op, left, right } => write!(f, "({} {} {})", left, op, right),
            _ => todo!(),
        }
    }
}

/// An identifier is a string
#[derive(Debug, PartialEq, Eq)]
pub struct Ident(pub String);

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/*
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
    // TODO: strangely, this wrapper is never constructed.
    // everywhere we may have a BlockStmt (the only cases are the branches
    // of `if` expressions and the body of function literals), we explicitly
    // requires a BlockStmt instead of wrapping it in Stmt::Block.
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
*/
