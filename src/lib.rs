//! A lightweight, self-contained s-expression parser and data format.
//! Use `parse` to get an s-expression from its string representation, and the
//! `Display` trait to serialize it, potentially by doing `sexp.to_string()`.

#![deny(missing_docs)]
#![deny(unsafe_code)]

extern crate unescape;

mod parse;
mod error;
mod value;

pub use value::Value;
pub use parse::Parser;
pub use error::{ParseResult, ParseError};
