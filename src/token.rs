#[derive(Debug, PartialEq, Eq)]
#[rustfmt::skip]
pub enum Token {
    // Identifiers and int literals
    Ident(String), Int(String),

    // Operators
    Assign, Plus, Minus, Bang, Asterisk, Slash, LT, GT, EQ, NQ,

    // Delimiters
    Comma, Semicolon, LParen, RParen, LBrace, RBrace,

    // keywords
    Function, Let, True, False, If, Else, Return,

    // End of file
    Eof,

    // An illegal byte
    Illegal(u8),
}

impl Token {
    pub fn lookup_ident(ident: &str) -> Self {
        match ident {
            "fn" => Self::Function,
            "let" => Self::Let,
            "true" => Self::True,
            "false" => Self::False,
            "if" => Self::If,
            "else" => Self::Else,
            "return" => Self::Return,
            s => Self::Ident(s.to_string()),
        }
    }
}
