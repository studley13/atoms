//! Errors produced during that parsing of S-expressions

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::error;
use std::fmt;

/// SHorthand to create an error result for a given error
fn err<T>(message: &'static str, s: &str, pos: &usize) -> ERes<T> {
  Err(err_impl(message, s, pos))
}

/// The representation of an s-expression parse error.
pub struct ParseError {
    /// The error message.
    pub message: &'static str,
    /// The line number on which the error occurred.
    pub line:    usize,
    /// The column number on which the error occurred.
    pub column:  usize,
    /// The index in the given string which caused the error.
    pub index:   usize,
}

impl ParseError {
    /**
     * Produce a new boxed error. Errors are always used in a boxed form so
     * there is no raw error constructor
     */
    #[cold]
    pub fn new(message: &'static str, source: &str, pos: usize) -> Err {
        let (line, column) = ParseError::get_location(source, pos);
        Box::new(Error {
            message: message,
            line:    line,
            column:  column,
            index:   pos,
        })
    }

    /// Directly create an `ParseResult`
    pub fn err<T>(message: &'static str, source: &str, pos: usize) -> ParseResult<T> {
        Err(ParseError::new(message, source, pos))
    }

    /**
     * Get the specified line and column in the given text that the error
     * occurred at as a tuple.
     *
     * Tuple is in the form `(line, column)`.
     */
    fn get_location(s: &str, pos: usize) -> (usize, usize) {
        let mut line: usize = 1;
        let mut col:  isize = -1;
        for c in s.chars().take(pos+1) {
            if c == '\n' {
                line +=  1;
                col   = -1;
            } else {
                col  +=  1;
            }
        }
        (line, cmp::max(col, 0) as usize)
    }
}

impl error::Error for Error {
    fn description(&self) -> &str { self.message }
    fn cause(&self) -> Option<&error::Error> { None }
}

/// Since errors are the uncommon case, they're boxed. This keeps the size of
/// structs down, which helps performance in the common case.
///
/// For example, an `ERes<()>` becomes 8 bytes, instead of the 24 bytes it would
/// be if `Err` were unboxed.
type Err = Box<ParseError>;

/// The result of parsing an s-expression
type ParseResult<T> = Result<T, Err>;

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

impl fmt::Debug for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

#[test]
fn error_display() {
    let error = ParseError {
        message: "Unexpected eof",
        line:    4usize,
        column:  1usize,
        index:   4usize
    };

    assert_eq!(format!("{:?}", error), "1:4: Unexpected eof");
    assert_eq!(format!("{:?}", Box::new(error)), "1:4: Unexpected eof");
}

#[test]
fn error_location() {
  let s = "0123456789\n0123456789\n\n6";
  assert_eq!(ParseError::get_location(s, 4), (1, 4));

  assert_eq!(ParseError::get_location(s, 10), (2, 0));
  assert_eq!(ParseError::get_location(s, 11), (2, 0));
  assert_eq!(ParseError::get_location(s, 15), (2, 4));

  assert_eq!(ParseError::get_location(s, 21), (3, 0));
  assert_eq!(ParseError::get_location(s, 22), (4, 0));
  assert_eq!(ParseError::get_location(s, 23), (4, 0));
  assert_eq!(ParseError::get_location(s, 500), (4, 0));
}
