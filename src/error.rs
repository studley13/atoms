//! Errors produced during that parsing of S-expressions

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::{error, fmt, io};

/**
 * Error that occurs when parsing s-expression.
 *
 * All forms of this error have the line and column the error occured on stored
 * in the first two members respectively.
 */
pub enum ParseError {
    /**
     * Unexpected end of file or stream
     *
     * This occurs when no more characters can be read from the input stream.
     */
    EndOfFile(usize, usize),
    /**
     * Trailing characters after end of expression
     *
     * This error is raised when trying to parseinput as a single expression
     * and more characters are available after a full expression has been
     * parsed. Comments after the expression do not cause this error.
     */
    TrailingGarbage(usize, usize),

    /**
     * Unexpected closing paren
     *
     * A closing paren was found as the first character of an expression.
     */
    ClosingParen(usize, usize),

    /**
     * Extensions not in use
     *
     * An extension expression was used where an extension type has not been
     * provided.
     */
    NoExtensions(usize, usize),

    /**
     * Cons pair without right element
     *
     * A cons pair was closed before a right side was declared, 
     * for example `(a . )`.
     */
    ConsWithoutRight(usize, usize),

    /**
     * Cons pair not closed after right expression
     *
     * A cons pair was not closed after the right side was declared, 
     * for example `(a . b c)`.
     */
    ConsWithoutClose(usize, usize),

    /**
     * An error occured when trying to parse a string literal.
     *
     * This is caused when the parser is unable to properly unescape a string
     * literal.
     */
    StringLiteral(usize, usize),

    /**
     * A symbol without any length was used.
     *
     * This probably caused by a quote not being attached to an expression,
     * for example ```( ` , or ' )```
     */
    EmptySymbol(usize, usize),

    /**
     * Symbol could not be encoded
     *
     * This error is produced when a the type the represents symbols is unable
     * to encode the given symbol.
     */
    SymbolEncode(usize, usize),

    /**
     * Error occured when trying to buffer text from input.
     */
    BufferError(usize, usize, io::Error),
}

impl ParseError {

    /**
     * Get the location that an error occured on
     *
     * Gets the location in the form of `(line, column)`.
     */
    pub fn position(&self) -> (usize, usize) {
        match *self {
            ParseError::EndOfFile(l, c) => (l, c),
            ParseError::TrailingGarbage(l, c) => (l, c),
            ParseError::ClosingParen(l, c) => (l, c),
            ParseError::NoExtensions(l, c) => (l, c),
            ParseError::ConsWithoutRight(l, c) => (l, c),
            ParseError::ConsWithoutClose(l, c) => (l, c),
            ParseError::StringLiteral(l, c) => (l, c),
            ParseError::EmptySymbol(l, c) => (l, c),
            ParseError::SymbolEncode(l, c) => (l, c),
            ParseError::BufferError(l, c, _) => (l, c),
        }
    }

    /**
     * Get the line of input that the error occured on.
     */
    pub fn line(&self) -> usize {
        let (line, _) = self.position();
        line
    }

    /**
     * Get the column on the line of input that the error occured on.
     */
    pub fn column(&self) -> usize {
        let (_, column) = self.position();
        column
    }
}

impl error::Error for ParseError {
    fn description(&self) -> &str { 
        match *self {
            ParseError::EndOfFile(_, _) => 
                "Unexpected end of file",
            ParseError::TrailingGarbage(_, _) => 
                "Trailing garbage text",
            ParseError::ClosingParen(_, _) => 
                "Unexpected closing paren",
            ParseError::NoExtensions(_, _) => 
                "Extensions are not currently in use",
            ParseError::ConsWithoutRight(_, _) => 
                "Cons pair closed without right side",
            ParseError::ConsWithoutClose(_, _) => 
                "Cons pair not closed after right side",
            ParseError::StringLiteral(_, _) => 
                "Error unescaping string literal",
            ParseError::EmptySymbol(_, _) => 
                "Encountered symbol with zero length",
            ParseError::SymbolEncode(_, _) => 
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
