/*!
 * Simple example of a Read-Print loop (we don't hav eval yet).
 */

const VERSION: &'static str = "0.1.0";

extern crate atoms;

use atoms::{Parser, StringValue, Pretty};
use std::io::{stdin, stdout, Write};

fn main() {
    let mut parser = Parser::reader(stdin());
    let mut sout = stdout();
    let exit = StringValue::symbol("exit").unwrap();

    println!("Atoms RPL version {}.", VERSION);
    println!("Symbol `exit` to exit.\n");

    loop {
        print!("> ");
        sout.flush().unwrap();
        match parser.read() {
            Err(e) => println!("Error: {}", e),
            Ok(v) => 
                if v == exit {
                    return;
                } else {
                    println!("{}", v.pretty().with_spaces(2))
                },
        }
    }
}
