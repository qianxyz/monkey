use std::io::{self, BufRead, Write};

use crate::evaluator::Evaluator;
use crate::lexer::Lexer;
use crate::object::Object;
use crate::parser::Parser;

const PROMPT: &str = "> ";

pub fn run() {
    let stdin = io::stdin();
    let mut it = stdin.lock().lines();

    let mut evaluator = Evaluator::new();

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

        let evaluated = evaluator.eval_program(program);
        match evaluated {
            Ok(Object::Null) => continue,
            Ok(obj) => println!("{}", obj),
            Err(e) => println!("\t{:?}", e),
        }
    }
}
