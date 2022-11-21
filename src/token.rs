#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenType {
    Illegal,
    Eof,

    // identifiers and literals
    Ident, // foo, bar, ...
    Int,   // 1, 2, ...

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,

    LT,
    GT,
    EQ,
    NQ,

    // Delimiters
    Comma,
    Semicolon,

    LParen,
    RParen,
    LBrace,
    RBrace,

    // keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

impl TokenType {
    pub fn lookup_ident(ident: &str) -> Self {
        match ident {
            "fn" => Self::Function,
            "let" => Self::Let,
            "true" => Self::True,
            "false" => Self::False,
            "if" => Self::If,
            "else" => Self::Else,
            "return" => Self::Return,
            _ => Self::Ident,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token {
    ttype: TokenType,
    literal: String,
}

impl Token {
    pub fn new(ttype: TokenType, literal: &str) -> Self {
        Self {
            ttype,
            literal: literal.to_string(),
        }
    }

    pub fn literal(&self) -> &str {
        &self.literal
    }
}
