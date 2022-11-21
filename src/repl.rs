use std::io::{self, BufRead, Write};

use crate::lexer::Lexer;
use crate::token::{Token, TokenType};

const PROMPT: &str = "> ";

pub fn run() {
    let stdin = io::stdin();
    let mut it = stdin.lock().lines();

    loop {
        print!("{}", PROMPT);
        io::stdout().flush().unwrap();

        let Some(Ok(input)) = it.next() else { break };

        let mut lexer = Lexer::new(&input);
        loop {
            let token = lexer.next_token();
            println!("{:?}", token);
            if token == Token::new(TokenType::Eof, "") {
                break;
            }
        }
    }
}
