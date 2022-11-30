use std::io::{self, BufRead, Write};

use crate::environment::Environment;
use crate::evaluator::eval_program;
use crate::lexer::Lexer;
use crate::object::Object;
use crate::parser::Parser;

const PROMPT: &str = "> ";

pub fn run() {
    let stdin = io::stdin();
    let mut it = stdin.lock().lines();

    let mut env = Environment::new();

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

        let evaluated = eval_program(program, &mut env);
        match evaluated {
            Ok(Object::Null) => continue,
            Ok(obj) => println!("{}", obj),
            Err(e) => println!("\t{:?}", e),
        }
    }
}
