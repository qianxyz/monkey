pub mod token;

use std::str;

pub use token::Token;

pub struct Lexer {
    /// The input string, stored as a byte array
    input: Vec<u8>,

    /// Current position
    position: usize,

    /// One after the current position
    read_position: usize,

    /// Current char
    ch: u8,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        // TODO: a nice error notifying the non-ascii chars
        assert!(input.is_ascii());

        let mut lexer = Self {
            input: input.into_bytes(),
            position: 0,
            read_position: 0,
            ch: 0,
        };

        // set ch to first byte, position to 0, read_position to 1
        lexer.read_char();

        lexer
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let tok = match self.ch {
            // single char tokens
            b';' => Token::Semicolon,
            b'(' => Token::LParen,
            b')' => Token::RParen,
            b'{' => Token::LBrace,
            b'}' => Token::RBrace,
            b',' => Token::Comma,
            b'+' => Token::Plus,
            b'-' => Token::Minus,
            b'*' => Token::Asterisk,
            b'/' => Token::Slash,
            b'<' => Token::LT,
            b'>' => Token::GT,
            0 => Token::Eof,

            // look ahead one char for `==` and `!=`
            b'=' => {
                if self.peek_char() == b'=' {
                    self.read_char();
                    Token::EQ
                } else {
                    Token::Assign
                }
            }
            b'!' => {
                if self.peek_char() == b'=' {
                    self.read_char();
                    Token::NQ
                } else {
                    Token::Bang
                }
            }

            // when we find a letter ...
            c if is_letter(c) => {
                // ... advance and consume till no more letters
                let literal = self.read_ident();

                // early return to avoid the `read_char` at the end
                return Token::lookup_ident(literal);
            }

            // when we find a digit ...
            c if is_digit(c) => {
                // ... advance and consume till no more digits
                let literal = self.read_number();

                // early return to avoid the `read_char` at the end
                return Token::Int(literal.to_string());
            }

            // illegal char
            c => Token::Illegal(c),
        };

        self.read_char();

        tok
    }

    /// Advance both pointers, store the current char in `self.ch`.
    fn read_char(&mut self) {
        self.ch = *self.input.get(self.read_position).unwrap_or(&0);
        self.position = self.read_position;
        self.read_position += 1;
    }

    /// Get the next char.
    fn peek_char(&self) -> u8 {
        *self.input.get(self.read_position).unwrap_or(&0)
    }

    /// Read until self.ch is not a letter, return the string covered.
    fn read_ident(&mut self) -> &str {
        let pos = self.position;
        while is_letter(self.ch) {
            self.read_char();
        }

        str::from_utf8(&self.input[pos..self.position]).unwrap()
    }

    /// Read until self.ch is not a digit, return the string covered.
    fn read_number(&mut self) -> &str {
        let pos = self.position;
        while is_digit(self.ch) {
            self.read_char();
        }

        str::from_utf8(&self.input[pos..self.position]).unwrap()
    }

    /// Skip until current char is not whitespace.
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
    use Token::*;

    fn helper(input: &str, tokens: Vec<Token>) {
        let mut lexer = Lexer::new(input.to_string());
        for t in tokens {
            assert_eq!(lexer.next_token(), t);
        }
    }

    #[test]
    fn one_char_tokens() {
        let input = "=+(){},;";

        let tokens = vec![
            Assign, Plus, LParen, RParen, LBrace, RBrace, Comma, Semicolon, Eof,
        ];

        helper(input, tokens);
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

        let five = || Ident("five".to_string());
        let ten = || Ident("ten".to_string());
        let add = || Ident("add".to_string());
        let x = || Ident("x".to_string());
        let y = || Ident("y".to_string());
        let result = || Ident("result".to_string());

        let tokens = vec![
            Let,
            five(),
            Assign,
            Int("5".to_string()),
            Semicolon,
            Let,
            ten(),
            Assign,
            Int("10".to_string()),
            Semicolon,
            Let,
            add(),
            Assign,
            Function,
            LParen,
            x(),
            Comma,
            y(),
            RParen,
            LBrace,
            x(),
            Plus,
            y(),
            Semicolon,
            RBrace,
            Semicolon,
            Let,
            result(),
            Assign,
            add(),
            LParen,
            five(),
            Comma,
            ten(),
            RParen,
            Semicolon,
            Eof,
        ];

        helper(input, tokens);
    }

    #[test]
    fn more_tokens() {
        let input = "!-/*5; 5 < 10 > 5;";

        let tokens = vec![
            Bang,
            Minus,
            Slash,
            Asterisk,
            Int("5".to_string()),
            Semicolon,
            Int("5".to_string()),
            LT,
            Int("10".to_string()),
            GT,
            Int("5".to_string()),
            Semicolon,
            Eof,
        ];

        helper(input, tokens);
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

        let tokens = vec![
            If,
            LParen,
            Int("5".to_string()),
            LT,
            Int("10".to_string()),
            RParen,
            LBrace,
            Return,
            True,
            Semicolon,
            RBrace,
            Else,
            LBrace,
            Return,
            False,
            Semicolon,
            RBrace,
            Eof,
        ];

        helper(input, tokens);
    }

    #[test]
    fn peek_eq_nq() {
        let input = "\
10 == 10;
10 != 9;
";

        let tokens = vec![
            Int("10".to_string()),
            EQ,
            Int("10".to_string()),
            Semicolon,
            Int("10".to_string()),
            NQ,
            Int("9".to_string()),
            Semicolon,
            Eof,
        ];

        helper(input, tokens);
    }
}
