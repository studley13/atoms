//! Functions related to parsing of input

use value::{Value, StringValue};
use error::{ParseError, ParseResult};
use std::io::{Read, BufRead, BufReader};
use std::str::FromStr;
use std::cmp::max;
use std::collections::VecDeque;

use unescape::unescape;

macro_rules! parse_err {
    ( $msg:expr, $me:ident ) => {
        ParseError::err($msg, $me.line, max($me.col, 0) as usize)
    }
}

macro_rules! cons_side {
    ( $me:ident, $default:block, $($catch:pat => $catch_result:block),*) => {{
        $me.consume_comments();
        if let Some(&c) = $me.peek() {
            match c {
                $($catch => $catch_result),*
                _ => $default,
            }
        } else {
            parse_err!("Error parsing cons or list", $me)
        }
    }}
}

macro_rules! cons_err {
    ( $me:ident, $($err:pat => $err_text:expr),*) => {{
        $me.consume_comments();
        if let Some(&c) = $me.peek() {
            match c {
                $($err => parse_err!($err_text, $me),),*
                _ => $me.parse_expression(),
            }
        } else {
            parse_err!("Error parsing cons or list", $me)
        }
    }}
}

macro_rules! end_of_file {
    ( $me:ident ) => {parse_err!("Unexpected end of file", $me)}
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
pub struct Parser<R> {
    reader: BufReader<R>,
    buffer: VecDeque<char>,
    line: usize,
    col: isize,
}

impl<'a> Parser<&'a [u8]> {
    /**
     * Create a new parser for a single expression
     */
    pub fn new<'b>(source: &'b AsRef<[u8]>) -> Parser<&'b [u8]> {
        Parser::reader(source.as_ref())
    }
}

impl<R: Read> Parser<R> {
    /**
     * Create a new parser for a reader.
     *
     * The reader can can be a source of series of discrete expressions,
     * each to be read one at a time.
     */
    pub fn reader(source: R) -> Parser<R> {
        Parser {
            reader: BufReader::new(source),
            buffer: VecDeque::new(),
            line: 1usize,
            col: -1isize,
        }
    }

    /**
     * Read the next expression.
     * 
     * ```rust
     * use atoms::{Parser, Value};
     * let text = r#"
     *     (this is a series of symbols)
     *     (this is another sexpression)
     *     mono ;Single expression on its own line
     *     (this expression
     *           spans lines)
     *     (these expressions) (share lines)
     * "#;
     * let mut parser = Parser::new(&text);
     * assert_eq!(
     *     parser.read::<String>().unwrap(),
     *     Value::into_list(
     *         vec!["this", "is", "a", "series", "of", "symbols"], 
     *         |s| Value::symbol(s).unwrap()
     *     )
     * );
     * assert_eq!(
     *     parser.read::<String>().unwrap(),
     *     Value::into_list(
     *         vec!["this", "is", "another", "sexpression"], 
     *         |s| Value::symbol(s).unwrap()
     *     )
     * );
     * assert_eq!(
     *     parser.read::<String>().unwrap(),
     *     Value::symbol("mono").unwrap()
     * );
     * assert_eq!(
     *     parser.read::<String>().unwrap(),
     *     Value::into_list(
     *         vec!["this", "expression", "spans", "lines"], 
     *         |s| Value::symbol(s).unwrap()
     *     )
     * );
     * assert_eq!(
     *     parser.read::<String>().unwrap(),
     *     Value::into_list(
     *         vec!["these", "expressions"], 
     *         |s| Value::symbol(s).unwrap()
     *     )
     * );
     * assert_eq!(
     *     parser.read::<String>().unwrap(),
     *     Value::into_list(
     *         vec!["share", "lines"], 
     *         |s| Value::symbol(s).unwrap()
     *     )
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
     * This will produce parsing errors when `FromStr::from_str` fails when
     * being used to create symbols.
     */
    pub fn read<Sym: FromStr>(&mut self) -> ParseResult<Value<Sym>> {
        // Consume the comments
        self.consume_comments();
        self.parse_expression()
    }

    /**
     * Parse the given expression. Consumes the parser.
     *
     * If you want to pass a series of expressions, use `read` instead.
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
     * Similar to `read`, the parser must be informed of the type to be used
     * for expressing symbols.
     */
    pub fn parse<Sym: FromStr>(mut self) -> ParseResult<Value<Sym>> {

        // Remove leading whitespace
        self.consume_comments();

        let result = try!(self.parse_expression());

        // Remove trailing whitespace
        self.consume_comments();

        if let Some(_) = self.next() {
            parse_err!("Trailing garbage text", self)
        } else {
            Ok(result)
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
     * Peek at the next value in the buffer
     */
    pub fn peek(&mut self) -> Option<&char> {
        if self.buffer.len() <= 0 {
            self.extend_buffer();
        } 

        self.buffer.get(0)
    }

    /**
     * Get the next value
     */
    pub fn next(&mut self) -> Option<char> {
        if self.buffer.len() <= 0 {
            self.extend_buffer();
        } 

        let next_c = self.buffer.pop_front();

        // Advance position if possible
        if let Some(c) = next_c {
            if c == '\n' {
                self.line +=  1;
                self.col   = -1;
            } else {
                self.col  +=  1;
            }
            Some(c)
        } else {
            None
        }
    }

    /**
     * Get the next line and add to queue
     */
    pub fn extend_buffer(&mut self) {
        let mut line = String::new();
        if let Ok(_) = self.reader.read_line(&mut line) {
            for t in line.chars() {
                self.buffer.push_back(t);
            }
        }
    }

    /**
     * Parse a single sexpression
     */
    fn parse_expression<Sym: FromStr>(&mut self) 
        -> ParseResult<Value<Sym>> {
        
        // Consume leading comments
        self.consume_comments();

        self.parse_immediate()
    }

    /**
     * Parse the next immediate expression
     */
    fn parse_immediate<Sym: FromStr>(&mut self) -> ParseResult<Value<Sym>> {
        if let Some(&c) = self.peek() {
            match c {
                // String literal
                '"' => self.parse_quoted(),
                // Start of cons 
                '(' => {
                    self.next();
                    self.parse_cons()
                },
                // End of Cons
                ')' => parse_err!("Unexpected close brace", self),
                // Extension
                '#' => parse_err!("Extensions are not yet implemented", self),
                // Quoting
                '\'' => {
                    self.next();
                    Ok(Value::data(try!(self.parse_immediate())))
                },
                '`' => {
                    self.next();
                    Ok(Value::data(try!(self.parse_immediate())))
                },
                ',' => {
                    self.next();
                    Ok(Value::code(try!(self.parse_immediate())))
                },
                // Automatic value
                _   => self.parse_value(),
            }
        } else {
            end_of_file!(self)
        }
    }

    /**
     * Parse a Cons
     */
    fn parse_cons<Sym: FromStr>(&mut self) -> ParseResult<Value<Sym>> {
        let left = try!(cons_side!(self, {self.parse_expression()}, ')' => {
            self.next();
            Ok(Value::Nil)
        }));

        if left.is_nil() {
            Ok(left)
        } else {
            let right = try!(cons_side!(self, {self.parse_cons()},
                ')' => {
                    self.next();
                    Ok(Value::Nil)
                },
                '.' => {
                    self.parse_cons_rest()
                }
            ));

            Ok(Value::cons(left, right))
        }
    }

    fn parse_cons_rest<Sym: FromStr>(&mut self) -> ParseResult<Value<Sym>> {
        let next_val = try!(self.unescape_value());

        if next_val == "." {
            // Cons join
            self.consume_comments();
            let value = cons_err!(self, 
                ')' => "Cons closed without right side"
            );
            if let Some(c) = self.next() {
                if c != ')' {
                    parse_err!("Error finding close of cons", self)
                } else {
                    value
                }
            } else {
                end_of_file!(self)
            }
        } else {
            // List
            Ok(Value::cons(
                try!(self.value_from_string(&next_val)),
                try!(self.parse_cons())
            ))
        }
    }

    /**
     * Extract a value up until the given delimiter. Does not consume delimiter.
     */
    fn extract_delimited(&mut self, delimiter: &Fn(char) -> bool, allow_eof: bool) 
        -> ParseResult<String> {
        let mut value = String::new();

        // Push each following character into the parsed string
        while let Some(&preview) = self.peek() {
            if preview == '\\' {
                let c = self.next().unwrap();
                value.push(c);
                if let Some(follower) = self.next() {
                    value.push(follower);
                } else {
                    return parse_err!("Unexpected end of escape sequence", self);
                }
            } else if delimiter(preview) {
                return Ok(value);
            } else {
                let c = self.next().unwrap();
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
    fn parse_quoted<Sym: FromStr>(&mut self) -> ParseResult<Value<Sym>> {
        // remove leading quote
        self.next().unwrap();

        // parsed string value
        let unquoted = try!(self.extract_delimited(&(|c| c == '"'), false));

        // remove trailing quote
        self.next().unwrap();

        Ok(Value::string(try!(self.parse_text(&unquoted))))
    }

    /**
     * Extract a single string escaped value
     */
    fn unescape_value(&mut self) -> ParseResult<String> {
        let text = try!(self.extract_delimited(&default_delimit, true)).escape_special();
        self.parse_text(&text)
    }

    /**
     * Parse a an escaped text (symbol or string)
     */
    fn parse_text(&mut self, s: &AsRef<str>) -> ParseResult<String> {
        if let Some(parsed) = unescape(s.as_ref()) {
            Ok(parsed)
        } else {
            parse_err!("String literal escape error", self)
        }
    }

    /**
     * Parse the next value into a type
     */
    fn parse_value<Sym: FromStr>(&mut self) -> ParseResult<Value<Sym>> {
        let text = try!(self.unescape_value());
        self.value_from_string(&text)
    }

    /**
     * Parse a string into a value
     */
    fn value_from_string<Sym: FromStr>(&mut self, text: &str) -> ParseResult<Value<Sym>> {
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
        if text.len() == 0usize {
            parse_err!("Empty symbol error", self)
        } else if let Some(sym) = Value::symbol(&text) {
            Ok(sym)
        } else {
            parse_err!("Error resolving symbol", self)
        }
    }

    /**
     * Consume whitespace
     */
    fn consume_whitespace(&mut self) {
        while let Some(&c) = self.peek() {
            if c.is_whitespace() {
                self.next();
            } else {
                return;
            }
        }
    }
    
    /**
     * Consume the remaining line of text
     */
    fn consume_line(&mut self) {
        while let Some(c) = self.next() {
            if c == '\n' { return; }
        }
    }
    
    /**
     * Consume blocks of comments
     */
    fn consume_comments(&mut self) {
        self.consume_whitespace();
        while let Some(&c) = self.peek() {
            if c == ';' {
                self.consume_line();
            } else if c.is_whitespace() {
                self.consume_whitespace();
            } else {
                return;
            }
        }
    }
}

/**
 * Additional characters to escape in strings
 */
trait EscapeSpecial {
    fn escape_special(self) -> Self;
}

impl EscapeSpecial for String {
    fn escape_special(self) -> String {
        self.replace("\\ ", " ")
            .replace("\\;", ";")
            .replace("\\(", "(")
            .replace("\\)", ")")
            .replace("\\\"", "\"")
            .replace("\\\'", "\'")
            .replace("\\`", "`")
            .replace("\\,", ",")
            .replace("\\\\", "\\")
    }
}

/**
 * Default predicate for delimitation is whitespace
 */
fn default_delimit(c: char) -> bool { 
    c.is_whitespace() || c == ';' || c == '(' || c == ')' || c == '"' 
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
    let two = StringValue::symbol("one").unwrap();
    let output_short = s_tree!(StringValue: (two . ([two] . ([three] . [four]))));
    let parsed = Parser::new(&text).parse::<String>().unwrap();
    assert_eq!(parsed, output);
    assert_eq!(parsed, output_short);
}

#[test]
fn split_cons() {
    let text = "(one . two . three . four)";
    let parser = Parser::new(&text);
    assert!(parser.parse::<String>().is_err());
}

#[test]
fn github_issues() {
    fn parse_text(text: &'static str) -> ParseResult<StringValue> {
        let parser = Parser::new(&text);
        parser.parse::<String>()
    }
    assert!(parse_text("(a #;(c d) e)").is_err());
}

#[test]
fn quasiquoting() {
    fn parse_text(text: &'static str) -> StringValue {
        let parser = Parser::new(&text);
        parser.parse::<String>().unwrap()
    }

    assert_eq!(
        parse_text("(this is 'data)"), 
        s_tree!(StringValue: ([this] [is] [d:[data]]))
    );
    assert_eq!(
        parse_text("'(this is 'data)"), 
        s_tree!(StringValue: [d:([this] [is] [d:[data]])])
    );
    assert_eq!(
        parse_text("'(this is ,quasiquoted ,(data that is '2 layers 'deep))"), 
        s_tree!(StringValue: 
            [d:([this] [is] [c:[quasiquoted]] [c:(
                [data] [that] [is] [d:2] [layers] [d:[deep]]
            )])]
        )
    );
    assert_eq!(
        parse_text("('this \n;comment here for effect\nshould probably work...)"), 
        s_tree!(StringValue: ([d:[this]] [should] [probably][s:"work..."]))
    );
    assert_eq!(
        parse_text("('\\;comment \nshould probably work...)"), 
        s_tree!(StringValue: ([d:[s:";comment"]] [should] [probably] [s:"work..."]))
    );
    assert_eq!(
        parse_text("`,`,`,`,`,data"), 
        s_tree!(StringValue: [d:[c:[d:[c:[d:[c:[d:[c:[d:[c:[data]]]]]]]]]]])
    );
    assert_eq!(
        parse_text("`,`,`,`,`,data").unwrap_full(), 
        s_tree!(StringValue: [data])
    );
    assert_eq!(
        parse_text("`(,(left `right . `last) ,middle end)").unwrap_full(), 
        s_tree!(StringValue: (([left] . ([right] . [last])) [middle] [end]))
    );
}

#[test]
fn symmetric_encoding() {
    fn check(text: &'static str) {
        assert_eq!(
            Parser::new(&text).parse::<String>().unwrap().to_string(),
            text
        );
    }
    check("one");
    check("12");
    check("3.152");
    check("3.0");
    check("-1.0");
    check("(a b c d)");
    check("(a b c . d)");
    check("this\\;uses\\\"odd\\(chars\\)\\ space");
}
