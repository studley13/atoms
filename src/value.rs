//! Representation of the S-expression tree.

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::str::FromStr;
use std::fmt::{self, Display, Debug, Formatter};

/**
 * This is a simple representation of values, using String to represent all
 * symbols.
 */
#[allow(dead_code)]
pub type StringValue = Value<String>;

/** 
 * A single data element in an s-expression. Floats are excluded to ensure
 * atoms may be used as keys in ordered and hashed data structures.
 *
 * All strings must be valid utf-8.
 */
#[derive(PartialEq, Clone, PartialOrd)]
pub enum Value<Sym: Sized + ToString + FromStr> {
    /// A quoted UTF-8 string value
    Str(String),
    /// An unquoted, case-sensitive symbol
    Symbol(Sym),
    /// An integer value
    Int(i64),
    /// A floating point value
    Float(f64),
    /// A Cons cell
    Cons(Box<Value<Sym>>, Box<Value<Sym>>),
    /// A Nil value
    Nil,
}

impl<Sym: Sized + ToString + FromStr> Value<Sym> {
    /** 
     * Create a new symbol from a string.
     *
     * Depending on the type used to represent the symbol, this may fail to
     * produce a symbol and return a null. This will be presented as an error
     * by the parser.
     */
    pub fn symbol(s: &str) -> Option<Value<Sym>> {
        let sym = Sym::from_str(s);
        match sym {
            Ok(sym) => Some(Value::Symbol(sym)),
            Err(_) => None,
        }
    }

    /// Create a new string
    pub fn string<S: Into<String>>(s: S) -> Value<Sym> {
        Value::Str(s.into())
    }

    /// Create a new integer
    pub fn int<I: Into<i64>>(i: I) -> Value<Sym> {
        Value::Int(i.into())
    }

    /// Create a new float
    pub fn float<F: Into<f64>>(f: F) -> Value<Sym> {
        Value::Float(f.into())
    }

    /// Create a new list
    pub fn list<V: Into<Value<Sym>>>(mut source_vec: Vec<V>) -> Value<Sym> {

        // Convert all members into values
        let mut result = Value::Nil;

        while let Some(value) = source_vec.pop() {
            result = Value::cons(value.into(), result)
        }

        result
    }

    /// Crate a cons cell
    pub fn cons<V: Into<Value<Sym>>>(left: V, right: V) -> Value<Sym> {
        Value::Cons(Box::new(left.into()), Box::new(right.into()))
    }

    /// Check if a value is a nill
    pub fn is_nil(&self) -> bool {
        match *self {
            Value::Nil => true,
            _ => false,
        }
    }
}

impl<Sym> Display for Value<Sym> where Sym: ToString + FromStr + Sized {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            Value::Cons(ref left, ref right) => display_cons(left, right, true, f),
            Value::Str(ref text) => write!(f, "\"{}\"", escape_string(&text)),
            Value::Symbol(ref sym) => write!(f, "{}", escape_string(&sym.to_string().replace(" ", "\\ "))),
            Value::Int(ref i) => write!(f, "{}", i),
            Value::Float(ref fl) => format_float(f, *fl),
            Value::Nil => write!(f, "()"),
        }
    }
}

impl<Sym> Debug for Value<Sym> where Sym: ToString + FromStr + Sized {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

fn display_cons<Sym: ToString + FromStr + Sized>(left: &Value<Sym>, 
                                                 right: &Value<Sym>, 
                                                 root: bool, f: &mut Formatter) 
    -> Result<(), fmt::Error> {
    if root {
        try!(write!(f, "("));
    }

    // Write the left value
    try!(write!(f, "{}", left));

    // Write the right value
    match *right {
        Value::Nil => write!(f, ")"),
        Value::Cons(ref left, ref right) => {
            try!(write!(f, " "));
            display_cons(left, right, false, f)
        }
        _ => write!(f, " . {})", right)
    }
}

fn escape_string(text: &AsRef<str>) -> String {
    text.as_ref().chars().map(
        |c| -> String { c.escape_default().collect() }
    ).collect()
}

fn format_float<F: Into<f64>>(f: &mut Formatter, fl: F) -> Result<(), fmt::Error> {
    let float = fl.into();
    match float.fract() {
        0f64 => write!(f, "{:.1}", float),
        _ => write!(f, "{}", float),
    }
}

#[test]
fn value_fmt_test() {
    assert_eq!(format!("{:?}", Value::<String>::int(13)), "13");
    assert_eq!(format!("{:?}", Value::<String>::int(-13)), "-13");
    assert_eq!(format!("{:?}", Value::<String>::float(13.0)), "13.0");
    assert_eq!(format!("{:?}", Value::<String>::float(13.125)), "13.125");
    assert_eq!(format!("{:?}", Value::<String>::float(13.333)), "13.333");
    assert_eq!(format!("{:?}", Value::<String>::float(-13.333)), "-13.333");
    assert_eq!(format!("{:?}", Value::<String>::string("text")), "\"text\"");
    assert_eq!(format!("{:?}", Value::<String>::string("hello\tthere\nfriend")), "\"hello\\tthere\\nfriend\"");
    assert_eq!(format!("{:?}", Value::<String>::symbol("text").unwrap()), "text");
    assert_eq!(format!("{:?}", Value::<String>::symbol("hello\tthere\nfriend").unwrap()), "hello\\tthere\\nfriend");
    assert_eq!(format!("{:?}", Value::<String>::list(vec![
        Value::<String>::int(13),
        Value::<String>::float(13.333),
        Value::<String>::string("text"),
        Value::<String>::symbol("symbol").unwrap(),
    ])), "(13 13.333 \"text\" symbol)");
}
