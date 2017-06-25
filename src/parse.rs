//! Functions related to parsing of input

use error::{ParseError, ParseResult};
use value::{Value, self};

use std::str::{Chars, FromStr};
use std::iter::{Enumerate, Peekable};

type CharSource<'a> = Peekable<Enumerate<Chars<'a>>>;

/**
 * A parser for a particular string.
 */
pub struct Parser<'a> {
    source: &'a str,
}

impl<'a> Parser<'a> {
    /**
     * Create a new parser for a given string
     */
    pub fn new(source: &'a AsRef<str>) -> Parser<'a> {
        let source_ref = source.as_ref();

        Parser {
            source: source_ref,
        }
    }

    /**
     * Parse the given string. Consumes the parser.
     */
    pub fn parse<Sym: Sized + ToString + FromStr>(self) -> ParseResult<Value<Sym>> {
        let mut chars = self.source.chars().enumerate().peekable();
        
        // Remove leading whitespace
        consume_whitespace(&mut chars);

        let result = self.parse_expression(&mut chars);

        // Remove trailing whitespace
        consume_whitespace(&mut chars);

        if let Some((pos, _)) = chars.next() {
            ParseError::err("Trailing garbage text", self.source, pos)
        } else {
            result
        }
    }

    /**
     * Parse a single sexpression
     */
    fn parse_expression<Sym: Sized + ToString + FromStr>(&self, chars: &mut CharSource) 
        -> ParseResult<Value<Sym>> {
        // Consume leading brace
        let (pos, c) = chars.next().unwrap();
        if c != '(' {
            return ParseError::err("Error parsing s-expression", self.source, pos);
        }
        
        // Values in the list
        let mut values: Vec<Value<Sym>> = Vec::new();

        consume_whitespace(chars);

        while let Some(&(pos, c)) = chars.peek() {
            match c {
                // Remove comment lines
                ';' => consume_line(chars),
                // String literal
                '"' => values.push(try!(self.parse_quoted(chars))),
                // Child expression
                '(' => values.push(try!(self.parse_expression(chars))),
                // End of expression
                ')' => {
                    chars.next();
                    return Ok(Value::list(values))
                },
                // Automatic value
                _   => values.push(try!(self.parse_value(chars))),
            }

            consume_whitespace(chars);
        }

        // End of expression not found
        ParseError::err("Missing end of s-expression", self.source, self.source.len())
    }

    /**
     * Extract a value up until the given delimiter. Does not consume delimiter.
     */
    fn extract_delimited(&self, chars: &mut CharSource, delimiter: &Fn(char) -> bool, allow_eof: bool) 
        -> ParseResult<String> {
        let mut value = String::new();

        // Push each following character into the parsed string
        while let Some(&(pos, preview)) = chars.peek() {
            if preview == '\\' {
                let (_, c) = chars.next().unwrap();
                value.push(c);
                if let Some((follower_pos, follower)) = chars.next() {
                    value.push(follower);
                } else {
                    return ParseError::err("Unexpected end of escape sequence", self.source, pos);
                }
            } else if delimiter(preview) {
                return Ok(value);
            } else {
                let (_, c) = chars.next().unwrap();
                value.push(c);
            }
        }

        // Throw an error if we aren't expecting an end of file
        if allow_eof {
            Ok(value)
        } else {
            ParseError::err("Unexpected end of file", self.source, self.source.len())
        }
    }

    /**
     * Parse a quoted value
     */
    fn parse_quoted<Sym: Sized + ToString + FromStr>(&self, chars: &mut CharSource) 
        -> ParseResult<Value<Sym>> {
        // remove leading quote
        let (start_pos, _) = chars.next().unwrap();

        // parsed string value
        let unquoted = try!(self.extract_delimited(chars, &(|c| c == '"'), false));

        // remove trailing quote
        chars.next().unwrap();

        Ok(Value::string(try!(self.parse_text(&unquoted, start_pos))))
    }

    /**
     * Extract a single string escaped value
     */
    fn unescape_value(&self, chars: &mut CharSource) -> ParseResult<String> {
        let &(pos, _) = chars.peek().unwrap();
        self.parse_text(&try!(self.extract_delimited(chars, &default_delimit, true)), pos)
    }

    /**
     * Parse a an escaped text (symbol or string)
     */
    fn parse_text(&self, s: &AsRef<str>, start_pos: usize) -> ParseResult<String> {
        if let Some(parsed) = unescape(s) {
            Ok(parsed)
        } else {
            ParseError::err("String literal escape error", self.source, start_pos)
        }
    }

    /**
     * Parse the next value into a type
     */
    fn parse_value<Sym: Sized + ToString + FromStr>(&self, chars: &mut CharSource) 
        -> ParseResult<Value<Sym>> {
        let &(pos, _) = chars.peek().unwrap();
        let text = try!(self.unescape_value(chars));

        // Try make an integer
        match i64::from_str(&text) {
            Ok(i) => return Ok(Value::int(i)),
            _     => {},
        }

        // Try make a float
        match f64::from_str(&text) {
            Ok(f) => return Ok(Value::float(f)),
            _     => {},
        }

        // Try make a symbol
        if let Some(sym) = Value::symbol(&text) {
            Ok(sym)
        } else {
            ParseError::err("Error resolving symbol", self.source, pos)
        }
    }
}

/**
 * Default predicate for delimitation is whitespace
 */
fn default_delimit(c: char) -> bool { 
    c.is_whitespace() || c == ';' || c == '(' || c == ')' || c == '"'
}

/**
 * Consume whitespace
 */
fn consume_whitespace(chars: &mut CharSource) {
    while let Some(&(_, c)) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            return;
        }
    }
}

/**
 * Consume the remaining line of text
 */
fn consume_line(chars: &mut CharSource) {
    while let Some((_, c)) = chars.next() {
        if c == '\n' { return; }
    }
}

/**
 * Unescape raw text
 */
fn unescape(src: &AsRef<str>) -> Option<String> {
    Some(src.as_ref().to_owned())
}

#[test]
fn integer_test() {
    let text = "(1 2 3 4 5)";
    let nums = vec![1, 2, 3, 4, 5].iter().map(|i| Value::int(*i)).collect();
    let output = Value::list(nums);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn float_test() {
    let text = "(1.0 2.0 3.0 4.0 5.0)";
    let nums = vec![1.0, 2.0, 3.0, 4.0, 5.0].iter().map(|f| Value::float(*f)).collect();
    let output = Value::list(nums);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn string_test() {
    let text = "(\"one\" \"two\" \"three\" \"four\" \"five\")";
    let nums = vec!["one", "two", "three", "four", "five"].iter().map(|s| Value::string(*s)).collect();
    let output = Value::list(nums);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn symbol_test() {
    let text = "(one two three four five)";
    let nums = vec!["one", "two", "three", "four", "five"].iter().map(|s| Value::symbol(*s).unwrap()).collect();
    let output = Value::list(nums);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn nesting_test() {
    let text = "(one (two three) (four five))";
    let inner_one = Value::list(vec!["two", "three"].iter().map(|s| Value::symbol(*s).unwrap()).collect());
    let inner_two = Value::list(vec!["four", "five"].iter().map(|s| Value::symbol(*s).unwrap()).collect());
    let output = Value::list(vec![Value::symbol("one").unwrap(), inner_one, inner_two]);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
#[ignore]
fn space_escape_test() {
    let text = "(one\\ two\\ three\\ four\\ five)";
    let output = Value::list(vec![Value::symbol("one two three four five").unwrap()]);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn skip_whitespace_test() {
    let text = "   \n  \t (  \n\t   one    two   \n\t    three    \n\t   four five    \t   \n )   \n   \t";
    let nums = vec!["one", "two", "three", "four", "five"].iter().map(|s| Value::symbol(*s).unwrap()).collect();
    let output = Value::list(nums);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn trailing_garbage_test() {
    let text = "(one two three four five) garbage";
    let parser = Parser::new(&text);
    assert!(parser.parse::<String>().is_err());
}
