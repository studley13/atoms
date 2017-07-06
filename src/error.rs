//! Errors produced during that parsing of S-expressions

#![warn(missing_docs)]
#![deny(unsafe_code)]

use std::{error, fmt, io};

/**
 * Error that occurs when parsing s-expression.
 */
pub enum ParseError {
    ConsParse(usize, usize),
    EndOfFile(usize, usize),
    TrailingGarbage(usize, usize),
    ClosingBrace(usize, usize),
    NoExtensions(usize, usize),
    JoinWithoutRight(usize, usize),
    ConsWithoutClose(usize, usize),
    StringLiteral(usize, usize),
    EmptySymbol(usize, usize),
    SymbolResolution(usize, usize),
    BufferError(usize, usize, io::Error),
}

impl ParseError {
    pub fn position(&self) -> (usize, usize) {
        match *self {
            ParseError::ConsParse(l, c) => (l, c),
            ParseError::EndOfFile(l, c) => (l, c),
            ParseError::TrailingGarbage(l, c) => (l, c),
            ParseError::ClosingBrace(l, c) => (l, c),
            ParseError::NoExtensions(l, c) => (l, c),
            ParseError::JoinWithoutRight(l, c) => (l, c),
            ParseError::ConsWithoutClose(l, c) => (l, c),
            ParseError::StringLiteral(l, c) => (l, c),
            ParseError::EmptySymbol(l, c) => (l, c),
            ParseError::SymbolResolution(l, c) => (l, c),
            ParseError::BufferError(l, c, _) => (l, c),
        }
    }

    pub fn line(&self) -> usize {
        let (line, _) = self.position();
        line
    }

    pub fn column(&self) -> usize {
        let (_, column) = self.position();
        column
    }
}

impl error::Error for ParseError {
    fn description(&self) -> &str { 
        match *self {
            ParseError::ConsParse(_, _) => 
                "Error parsing cons or list",
            ParseError::EndOfFile(_, _) => 
                "Unexpected end of file",
            ParseError::TrailingGarbage(_, _) => 
                "Trailing garbage text",
            ParseError::ClosingBrace(_, _) => 
                "Unexpected closing brace",
            ParseError::NoExtensions(_, _) => 
                "Extensions have not yet been implemented",
            ParseError::JoinWithoutRight(_, _) => 
                "Cons pair closed without right side",
            ParseError::ConsWithoutClose(_, _) => 
                "Error finding close of cons",
            ParseError::StringLiteral(_, _) => 
                "String literal escape error",
            ParseError::EmptySymbol(_, _) => 
                "Empty symbol error",
            ParseError::SymbolResolution(_, _) => 
                "Error resolving symbol",
            ParseError::BufferError(_, _, _) => 
                "Error buffering text"
        }
    }
    fn cause(&self) -> Option<&error::Error> { 
        match *self {
            ParseError::BufferError(_, _, ref e) => Some(e),
            _ => None
        }
    }
}

/**
 * The result of parsing an s-expression.
 *
 * If something goes wrong, the error should be a `ParseError`, otherwise it's
 * a successful parsing of the s-expression fragment.
 */
pub type ParseResult<T> = Result<T, ParseError>;

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(f, "{}:{}: {}", self.line(), self.column(), self.description())
    }
}

impl fmt::Debug for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

#[test]
fn error_display() {
    let error = ParseError::EndOfFile(1usize, 4usize);

    assert_eq!(format!("{:?}", error), "1:4: Unexpected end of file");
    assert_eq!(format!("{:?}", Box::new(error)), "1:4: Unexpected end of file");
}
