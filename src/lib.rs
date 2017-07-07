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
//! use atoms::{Parser, StringValue};
//! let text = "(this is a series of symbols)";
//! let parser = Parser::new(&text);
//! let parsed = parser.parse_basic().unwrap();
//! assert_eq!(
//!     StringValue::into_list(
//!         vec!["this", "is", "a", "series", "of", "symbols"], 
//!         |s| StringValue::symbol(s).unwrap()
//!     ),
//!     parsed
//! );
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
//! assert_eq!(value.to_string(), "(this \"is\" 4 . s-expression)");
//! ```
//!

#![deny(missing_docs)]
#![deny(unsafe_code)]

extern crate unescape;

#[macro_use]
mod value;
mod parse;
mod error;
mod pretty;

pub use value::{Value, StringValue};
pub use parse::Parser;
pub use error::{ParseResult, ParseError};
pub use pretty::{Pretty, Layout};
