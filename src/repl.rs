use std::io::{self, BufRead, Write};

use crate::lexer::Lexer;
use crate::parser::Parser;

const PROMPT: &str = "> ";

pub fn run() {
    let stdin = io::stdin();
    let mut it = stdin.lock().lines();

    loop {
        print!("{}", PROMPT);
        io::stdout().flush().unwrap();

        let Some(Ok(input)) = it.next() else { break };

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        let errors = parser.errors();

        if !errors.is_empty() {
            for e in errors {
                println!("\t{:?}", e);
            }
            continue;
        }

        println!("{:#?}", program);
    }
}
