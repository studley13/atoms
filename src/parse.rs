//! Functions related to parsing of input

use error::{ParseError, ParseResult};
use value::{Value, StringValue};

use unescape::unescape;

use std::str::{Chars, FromStr};
use std::iter::{Enumerate, Peekable};

type CharSource<'a> = Peekable<Enumerate<Chars<'a>>>;

macro_rules! cons_side {
    ( $me:ident, $chars:ident, $default:block, $($catch:pat => $catch_result:block),*) => {{
        consume_comments($chars);
        if let Some(&(_, c)) = $chars.peek() {
            match c {
                $($catch => $catch_result),*
                _ => $default,
            }
        } else {
            ParseError::err("Error parsing cons or list", $me.source, $me.source.len())
        }
    }}
}

macro_rules! cons_err {
    ( $me:ident, $chars:ident, $($err:pat => $err_text:expr),*) => {{
        consume_comments($chars);
        if let Some(&(pos, c)) = $chars.peek() {
            match c {
                $($err => ParseError::err($err_text, $me.source, pos),),*
                _ => $me.parse_expression($chars),
            }
        } else {
            ParseError::err("Error parsing cons or list", $me.source, $me.source.len())
        }
    }}
}

macro_rules! end_of_file {
    ( $me:ident ) => {ParseError::err("Unexpected end of file", $me.source, $me.source.len())}
}

/**
 * A parser for a particular `str`
 *
 * Parsing expressions requires a parser to be attached to the given string.
 * 
 * ```rust
 * use atoms::{Parser, StringValue};
 * let text = "(this is a series of symbols)";
 * let parser = Parser::new(&text);
 * let parsed = parser.parse_basic().unwrap();
 * assert_eq!(
 *     StringValue::into_list(
 *         vec!["this", "is", "a", "series", "of", "symbols"], 
 *         |s| StringValue::symbol(s).unwrap()
 *     ),
 *     parsed
 * );
 * ```
 * 
 * The type parameter given to `Parser::parse` is to inform the parser of 
 * how to evaluate symbols. Any type that implements `ToString` and `FromStr`
 * reflexively can be used here. `String` is just one such, however it would 
 * be trivial to create an `enum` that restricted parsing to pre-defined
 * symbols.
 *
 * A parser has to be attached to a particular `str` to parse it. Really, this
 * is to allow us to make sane error messages.
 */
pub struct Parser<'a> {
    source: &'a str,
}

impl<'a> Parser<'a> {
    /**
     * Create a new parser for a specific `str`
     */
    pub fn new(source: &'a AsRef<str>) -> Parser<'a> {
        let source_ref = source.as_ref();

        Parser {
            source: source_ref,
        }
    }

    /**
     * Parse the given `str`. Consumes the parser.
     * 
     * ```rust
     * use atoms::{Parser, Value};
     * let text = "(this is a series of symbols)";
     * let parser = Parser::new(&text);
     * let parsed = parser.parse::<String>().unwrap();
     * assert_eq!(
     *     Value::into_list(
     *         vec!["this", "is", "a", "series", "of", "symbols"], 
     *         |s| Value::symbol(s).unwrap()
     *     ),
     *     parsed
     * );
     * ```
     *
     * This parser must be informed of how to represent symbols when they are
     * parsed. The `Sym` type parameter must implement `FromStr` and `ToString`
     * reflexively (i.e. the output of `ToString::to_string` for a given value
     * **must** produce the same value when used with `FromStr::from_str` and
     * visa versa such that the value can be encoded and decoded the same way).
     * If no special treatment of symbols is required, `parse_basic` should be
     * used.
     *
     * This will produce parsing errors when `FromStr::from_str` fails.
     */
    pub fn parse<Sym: Sized + ToString + FromStr>(self) -> ParseResult<Value<Sym>> {
        let mut chars = self.source.chars().enumerate().peekable();
        
        // Remove leading whitespace
        consume_comments(&mut chars);

        let result = self.parse_expression(&mut chars);

        // Remove trailing whitespace
        consume_comments(&mut chars);

        if let Some((pos, _)) = chars.next() {
            ParseError::err("Trailing garbage text", self.source, pos)
        } else {
            result
        }
    }

    /**
     * Parse the given `str` storing symbols as `String`s. Consumes the parser.
     * 
     * ```rust
     * use atoms::{Parser, StringValue};
     * let text = "(this is a series of symbols)";
     * let parser = Parser::new(&text);
     * let parsed = parser.parse::<String>().unwrap();
     * assert_eq!(
     *     StringValue::into_list(
     *         vec!["this", "is", "a", "series", "of", "symbols"], 
     *         |s| StringValue::symbol(s).unwrap()
     *     ),
     *     parsed
     * );
     * ```
     *
     * In cases where no special behaviour for symbols is needed, `parse_basic`
     * will resolve all symbols as `String`s.
     */
    pub fn parse_basic(self) -> ParseResult<StringValue> {
        self.parse::<String>()
    }

    /**
     * Parse a single sexpression
     */
    fn parse_expression<Sym: Sized + ToString + FromStr>(&self, chars: &mut CharSource) 
        -> ParseResult<Value<Sym>> {
        
        // Consume leading comments
        consume_comments(chars);

        if let Some(&(pos, c)) = chars.peek() {
            match c {
                // String literal
                '"' => self.parse_quoted(chars),
                // Start of cons 
                '(' => {
                    chars.next();
                    self.parse_cons(chars)
                },
                // End of Cons
                ')' => ParseError::err("Unexpected close brace", self.source, pos),
                // Extension
                '#' => ParseError::err("Extensions are not yet implemented", self.source, pos),
                // Quoting
                '`' => ParseError::err("Code/data distinction is not yet implemented", self.source, pos),
                ',' => ParseError::err("Code/data distinction is not yet implemented", self.source, pos),
                '\'' => ParseError::err("Code/data distinction is not yet implemented", self.source, pos),
                // Automatic value
                _   => self.parse_value(chars),
            }
        } else {
            end_of_file!(self)
        }
    }

    /**
     * Parse a Cons
     */
    fn parse_cons<Sym: Sized + ToString + FromStr>(&self, chars: &mut CharSource)
        -> ParseResult<Value<Sym>> {
        let left = try!(cons_side!(self, chars, {self.parse_expression(chars)}, ')' => {
            chars.next();
            Ok(Value::Nil)
        }));

        if left.is_nil() {
            Ok(left)
        } else {
            let right = try!(cons_side!(self, chars, {self.parse_cons(chars)},
                ')' => {
                    chars.next();
                    Ok(Value::Nil)
                },
                '.' => {
                    self.parse_cons_rest(chars)
                }
            ));

            Ok(Value::cons(left, right))
        }
    }

    fn parse_cons_rest<Sym: Sized + ToString + FromStr>(&self, chars: &mut CharSource)
        -> ParseResult<Value<Sym>> {
        let &(pos, _) = chars.peek().unwrap();
        let next_val = try!(self.unescape_value(chars));

        if next_val == "." {
            // Cons join
            consume_comments(chars);
            let value = cons_err!(self, chars, 
                ')' => "Cons closed without right side"
            );
            if let Some((pos, c)) = chars.next() {
                if c != ')' {
                    ParseError::err("Error finding close of cons", self.source, pos)
                } else {
                    value
                }
            } else {
                end_of_file!(self)
            }
        } else {
            // List
            Ok(Value::cons(
                try!(self.value_from_string(&next_val, pos)),
                try!(self.parse_cons(chars))
            ))
        }
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
                if let Some((_, follower)) = chars.next() {
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
            end_of_file!(self)
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
        self.parse_text(&try!(self.extract_delimited(chars, &default_delimit, true)).replace("\\ ", " "), pos)
    }

    /**
     * Parse a an escaped text (symbol or string)
     */
    fn parse_text(&self, s: &AsRef<str>, start_pos: usize) -> ParseResult<String> {
        if let Some(parsed) = unescape(s.as_ref()) {
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
        self.value_from_string(&text, pos)
    }

    /**
     * Parse a string into a value
     */
    fn value_from_string<Sym: Sized + ToString + FromStr>(&self, text: &str, pos: usize) 
        -> ParseResult<Value<Sym>> {
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
 * Consume blocks of comments
 */
fn consume_comments(chars: &mut CharSource) {
    consume_whitespace(chars);
    while let Some(&(_, c)) = chars.peek() {
        if c == ';' {
            consume_line(chars);
        } else if c.is_whitespace() {
            consume_whitespace(chars);
        } else {
            return;
        }
    }
}

#[test]
fn single_element() {
    let text = "(one)";
    let output = Value::list(vec![Value::symbol("one").unwrap()]);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn unary_test() {
    fn unary(text: &'static str, output: Value<String>) {
        let parser = Parser::new(&text);
        assert_eq!(parser.parse().unwrap(), output);
    }
    unary("()", Value::Nil);
    unary("one", Value::symbol("one").unwrap());
    unary("2", Value::int(2));
    unary("3.0", Value::float(3.0));
    unary("\"four\"", Value::string("four"));
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
fn space_escape_test() {
    let text = "(one\\ two\\ three\\ four\\ five)";
    let output = Value::list(vec![Value::symbol("one two three four five").unwrap()]);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn comment_test() {
    let text = "  ;comment\n (one;comment\n two ;;;comment with space\n three four five) ;trailing comment\n ;end";
    let nums = vec!["one", "two", "three", "four", "five"].iter().map(|s| Value::symbol(*s).unwrap()).collect();
    let output = Value::list(nums);
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
    let text = "(one two three four five) ;not garbage\n garbage";
    let parser = Parser::new(&text);
    assert!(parser.parse::<String>().is_err());
}

#[test]
fn escape_parsing_test() {
    let text = "(one\\ two 3 4 \"five\\\\is\\ta\\rless\\nmagic\\\'number\\\"\")";
    let output = Value::list(vec![
        Value::symbol("one two").unwrap(),
        Value::int(3),
        Value::int(4),
        Value::string("five\\is\ta\rless\nmagic\'number\"")
    ]);
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn cons_parsing() {
    let text = "(one . (two . (three . four)))";
    let output = Value::cons(
        Value::symbol("one").unwrap(), 
        Value::cons(
            Value::symbol("two").unwrap(),
            Value::cons(
                Value::symbol("three").unwrap(),
                Value::symbol("four").unwrap(),
            ),
        ),
    );
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn trailing_cons() {
    let text = "(one two three . four)";
    let output = Value::cons(
        Value::symbol("one").unwrap(), 
        Value::cons(
            Value::symbol("two").unwrap(),
            Value::cons(
                Value::symbol("three").unwrap(),
                Value::symbol("four").unwrap(),
            ),
        ),
    );
    let parser = Parser::new(&text);
    assert_eq!(parser.parse::<String>().unwrap(), output);
}

#[test]
fn split_cons() {
    let text = "(one . two . three . four)";
    let parser = Parser::new(&text);
    assert!(parser.parse::<String>().is_err());
}
