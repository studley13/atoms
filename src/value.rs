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
    /// A list of values
    List(Vec<Value<Sym>>)
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
    pub fn list<V: Into<Value<Sym>>>(source_vec: Vec<V>) -> Value<Sym> {

        // Convert all members into values
        let mut val_vec: Vec<Value<Sym>> = Vec::new();
        for value in source_vec {
            val_vec.push(value.into());
        }

        Value::List(val_vec)
    }

    /// Create a new empty list
    pub fn empty_list() -> Value<Sym> {
        Value::List(Vec::new())
    }
}

impl<Sym> Display for Value<Sym> where Sym: ToString + FromStr + Sized {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            Value::List(ref values) => display_list(&values, f),
            Value::Str(ref text) => write!(f, "\"{}\"", escape_string(&text)),
            Value::Symbol(ref sym) => write!(f, "{}", escape_string(&sym.to_string().replace(" ", "\\ "))),
            Value::Int(ref i) => write!(f, "{}", i),
            Value::Float(ref fl) => format_float(f, *fl),
        }
    }
}

impl<Sym> Debug for Value<Sym> where Sym: ToString + FromStr + Sized {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

fn display_list<Sym: ToString + FromStr + Sized>(values: &Vec<Value<Sym>>, f: &mut Formatter) 
    -> Result<(), fmt::Error> {
    try!(write!(f, "("));
    for (i, value) in values.iter().enumerate() {
        let space = if i == 0 { "" } else { " " };
        try!(write!(f, "{}{}", space, value));
    }
    write!(f, ")")
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
