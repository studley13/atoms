//! A lightweight, self-contained s-expression parser and data format.
//! Use `parse` to get an s-expression from its string representation, and the
//! `Display` trait to serialize it, potentially by doing `sexp.to_string()`.
//!
//! **Atoms** is a basic S-expression parser. It parses strings and produces
//! a tree of Cons-cells and atomic values of discrete type. Currently, only
//! the following primitive types are available, and are represented with the
//! `Value` `enum`:
//!
//! * `Nil`
//! * `Cons`
//! * `Symbol`
//! * `String`
//! * `Int`
//! * `Float`
//!
//! The trees are, as expected, formed by `Cons` cells.
//!
//! # Parsing
//!
//! Parsing expressions requires a parser to be attached to the given string.
//!
//! ```rust
//! use atoms::Parser;
//! let text = "(this is a series of symbols)";
//! let parser = Parser::new(&text);
//! let parsed = parser.parse_basic();
//! ```
//!
//! Custom parsing of symbols can be fairly easily defined allowing for
//! restricted symbol sets with parsing errors. See
//! [`Parser::parse`](struct.Parser.html#method.parse) for more.
//!
//! # Rendering
//!
//! To render out an S-expression, simply use `ToString` or display it 
//! directly.
//!
//! ```rust
//! use atoms::StringValue;
//! let value = StringValue::cons(
//!     StringValue::symbol("this").unwrap(),
//!     StringValue::cons(
//!         StringValue::string("is"),
//!         StringValue::cons(
//!             StringValue::int(4),
//!             StringValue::symbol("s-expression").unwrap(),
//!         )
//!     )
//! );
//! println!("{}", value);
//! ```
//!

#![deny(missing_docs)]
#![deny(unsafe_code)]

extern crate unescape;

mod parse;
mod error;
mod value;

pub use value::{Value, StringValue};
pub use parse::Parser;
pub use error::{ParseResult, ParseError};
