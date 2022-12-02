use std::fmt;

use crate::lexer::Token;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PrefixOp {
    Negate,
    Not,
}

impl TryFrom<&Token> for PrefixOp {
    type Error = ();

    fn try_from(value: &Token) -> Result<Self, Self::Error> {
        match value {
            Token::Minus => Ok(Self::Negate),
            Token::Bang => Ok(Self::Not),
            _ => Err(()),
        }
    }
}

impl fmt::Display for PrefixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Negate => "-",
            Self::Not => "!",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum InfixOp {
    Plus,
    Minus,
    Mult,
    Div,
    EQ,
    NQ,
    LT,
    GT,
}

impl TryFrom<&Token> for InfixOp {
    type Error = ();

    fn try_from(value: &Token) -> Result<Self, Self::Error> {
        match value {
            Token::Plus => Ok(Self::Plus),
            Token::Minus => Ok(Self::Minus),
            Token::Asterisk => Ok(Self::Mult),
            Token::Slash => Ok(Self::Div),
            Token::EQ => Ok(Self::EQ),
            Token::NQ => Ok(Self::NQ),
            Token::LT => Ok(Self::LT),
            Token::GT => Ok(Self::GT),
            _ => Err(()),
        }
    }
}

impl fmt::Display for InfixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Mult => "*",
            Self::Div => "/",
            Self::EQ => "==",
            Self::NQ => "!=",
            Self::LT => "<",
            Self::GT => ">",
        };
        write!(f, "{}", s)
    }
}

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
#[derive(Debug, PartialEq, Eq, Clone)]
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
#[derive(Debug, PartialEq, Eq, Clone)]
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    /// An identifier as an expression
    Ident(Ident),

    /// An int literal
    Int(i32),

    /// A bool literal
    Bool(bool),

    /// A prefix expression
    Prefix { op: PrefixOp, right: Box<Expr> },

    /// An infix expression
    Infix {
        op: InfixOp,
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
            Self::If { cond, consq, alter } => match alter {
                None => write!(f, "if ({}) {}", cond, consq),
                Some(a) => write!(f, "if ({}) {} else {}", cond, consq, a),
            },
            Self::Fn { params, body } => write!(
                f,
                "fn({}) {}",
                params
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                body
            ),
            Self::Call { func, args } => write!(
                f,
                "{}({})",
                func,
                args.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

/// An identifier is a string
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Ident(pub String);

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_ast() {
        let ident = Ident("my_var".to_string());
        let expr = Expr::Ident(Ident("another_var".to_string()));
        let stmt = Stmt::Let(ident, expr);
        let prog = Program(vec![stmt]);

        assert_eq!(prog.to_string(), "let my_var = another_var;\n");
    }
}
