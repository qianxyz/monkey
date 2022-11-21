use std::str;

use crate::token::{Token, TokenType};

struct Lexer {
    /// The input string, stored as a byte array
    input: Vec<u8>,

    /// Current position (points to current char)
    position: usize,

    /// Reading position (after current char)
    read_position: usize,

    /// Current char under examination
    ch: u8,
}

impl Lexer {
    fn new(input: &str) -> Self {
        assert!(input.is_ascii());

        let mut lexer = Self {
            input: input.as_bytes().to_vec(),
            position: 0,
            read_position: 0,
            ch: 0,
        };

        lexer.read_char();

        lexer
    }

    fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let tok = match self.ch {
            b'=' => {
                if self.peek_char() == b'=' {
                    self.read_char();
                    Token::new(TokenType::EQ, "==")
                } else {
                    Token::new(TokenType::Assign, "=")
                }
            }
            b'!' => {
                if self.peek_char() == b'=' {
                    self.read_char();
                    Token::new(TokenType::NQ, "!=")
                } else {
                    Token::new(TokenType::Bang, "!")
                }
            }
            b';' => Token::new(TokenType::Semicolon, ";"),
            b'(' => Token::new(TokenType::LParen, "("),
            b')' => Token::new(TokenType::RParen, ")"),
            b'{' => Token::new(TokenType::LBrace, "{"),
            b'}' => Token::new(TokenType::RBrace, "}"),
            b',' => Token::new(TokenType::Comma, ","),
            b'+' => Token::new(TokenType::Plus, "+"),
            b'-' => Token::new(TokenType::Minus, "-"),
            b'*' => Token::new(TokenType::Asterisk, "*"),
            b'/' => Token::new(TokenType::Slash, "/"),
            b'<' => Token::new(TokenType::LT, "<"),
            b'>' => Token::new(TokenType::GT, ">"),
            0 => Token::new(TokenType::Eof, ""),

            c if is_letter(c) => {
                let literal = self.read_ident();
                let ttype = TokenType::lookup_ident(literal);
                // early return: `read_ident` advances pointers,
                // ending `read_char` should be avoided
                return Token::new(ttype, literal);
            }

            c if is_digit(c) => {
                let ttype = TokenType::Int;
                let literal = self.read_number();
                // early return: see above
                return Token::new(ttype, literal);
            }

            // default: illegal char
            c => Token::new(TokenType::Illegal, str::from_utf8(&[c]).unwrap()),
        };

        self.read_char();

        tok
    }

    fn read_char(&mut self) {
        self.ch = *self.input.get(self.read_position).unwrap_or(&0);
        self.position = self.read_position;
        self.read_position += 1;
    }

    fn peek_char(&self) -> u8 {
        *self.input.get(self.read_position).unwrap_or(&0)
    }

    fn read_ident(&mut self) -> &str {
        let pos = self.position;
        while is_letter(self.ch) {
            self.read_char();
        }

        str::from_utf8(&self.input[pos..self.position]).unwrap()
    }

    fn read_number(&mut self) -> &str {
        let pos = self.position;
        while is_digit(self.ch) {
            self.read_char();
        }

        str::from_utf8(&self.input[pos..self.position]).unwrap()
    }

    fn skip_whitespace(&mut self) {
        while b" \n\t\r".contains(&self.ch) {
            self.read_char();
        }
    }
}

fn is_letter(c: u8) -> bool {
    (b'a'..=b'z').contains(&c) || (b'A'..=b'Z').contains(&c) || c == b'_'
}

fn is_digit(c: u8) -> bool {
    (b'0'..=b'9').contains(&c)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn helper(input: &str, tokens: &[(TokenType, &str)]) {
        let mut lexer = Lexer::new(input);
        for (ttype, literal) in tokens {
            assert_eq!(lexer.next_token(), Token::new(*ttype, literal));
        }
    }

    #[test]
    fn one_char_tokens() {
        let input = "=+(){},;";

        use TokenType::*;
        let tokens = [
            (Assign, "="),
            (Plus, "+"),
            (LParen, "("),
            (RParen, ")"),
            (LBrace, "{"),
            (RBrace, "}"),
            (Comma, ","),
            (Semicolon, ";"),
            (Eof, ""),
        ];

        helper(input, &tokens);
    }

    #[test]
    fn longer_program() {
        let input = "\
let five = 5;
let ten = 10;

let add = fn(x, y) {
    x + y;
};

let result = add(five, ten);
";

        use TokenType::*;
        let tokens = [
            (Let, "let"),
            (Ident, "five"),
            (Assign, "="),
            (Int, "5"),
            (Semicolon, ";"),
            (Let, "let"),
            (Ident, "ten"),
            (Assign, "="),
            (Int, "10"),
            (Semicolon, ";"),
            (Let, "let"),
            (Ident, "add"),
            (Assign, "="),
            (Function, "fn"),
            (LParen, "("),
            (Ident, "x"),
            (Comma, ","),
            (Ident, "y"),
            (RParen, ")"),
            (LBrace, "{"),
            (Ident, "x"),
            (Plus, "+"),
            (Ident, "y"),
            (Semicolon, ";"),
            (RBrace, "}"),
            (Semicolon, ";"),
            (Let, "let"),
            (Ident, "result"),
            (Assign, "="),
            (Ident, "add"),
            (LParen, "("),
            (Ident, "five"),
            (Comma, ","),
            (Ident, "ten"),
            (RParen, ")"),
            (Semicolon, ";"),
            (Eof, ""),
        ];

        helper(input, &tokens);
    }

    #[test]
    fn more_tokens() {
        let input = "!-/*5; 5 < 10 > 5;";

        use TokenType::*;
        let tokens = [
            (Bang, "!"),
            (Minus, "-"),
            (Slash, "/"),
            (Asterisk, "*"),
            (Int, "5"),
            (Semicolon, ";"),
            (Int, "5"),
            (LT, "<"),
            (Int, "10"),
            (GT, ">"),
            (Int, "5"),
            (Semicolon, ";"),
            (Eof, ""),
        ];

        helper(input, &tokens);
    }

    #[test]
    fn more_keywords() {
        let input = "\
if (5 < 10) {
    return true;
} else {
    return false;
}
";

        use TokenType::*;
        let tokens = [
            (If, "if"),
            (LParen, "("),
            (Int, "5"),
            (LT, "<"),
            (Int, "10"),
            (RParen, ")"),
            (LBrace, "{"),
            (Return, "return"),
            (True, "true"),
            (Semicolon, ";"),
            (RBrace, "}"),
            (Else, "else"),
            (LBrace, "{"),
            (Return, "return"),
            (False, "false"),
            (Semicolon, ";"),
            (RBrace, "}"),
            (Eof, ""),
        ];

        helper(input, &tokens);
    }

    #[test]
    fn peek_eq_nq() {
        let input = "\
10 == 10;
10 != 9;
";

        use TokenType::*;
        let tokens = [
            (Int, "10"),
            (EQ, "=="),
            (Int, "10"),
            (Semicolon, ";"),
            (Int, "10"),
            (NQ, "!="),
            (Int, "9"),
            (Semicolon, ";"),
            (Eof, ""),
        ];

        helper(input, &tokens);
    }
}
