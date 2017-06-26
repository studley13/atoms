//! Representation of the S-expression tree.

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::str::FromStr;
use std::fmt::{self, Display, Debug, Formatter};

/**
 * A single values with symbols represented using `String`.
 *
 * ```rust
 * use atoms::StringValue;
 *
 * let int = StringValue::int(12);
 * let float = StringValue::float(13.0);
 * let string = StringValue::string("fourteen");
 * // Symbols may not always be valid
 * let symbol = StringValue::symbol("fifteen").unwrap();
 *
 * // A list
 * let cons = StringValue::cons(
 *     int,
 *     StringValue::cons(
 *         float,
 *         StringValue::cons(
 *             string,
 *             StringValue::final_cons(
 *                 symbol
 *             )
 *         )
 *     )
 * );
 * ```
 */
#[allow(dead_code)]
pub type StringValue = Value<String>;

/** 
 * A single value with a variable representation of symbols.
 *
 * ```rust
 * use atoms::Value;
 *
 * // Represent symbols as `String`
 * let int = Value::<String>::int(12);
 * let float = Value::<String>::float(13.0);
 * let string = Value::<String>::string("fourteen");
 * // Symbols may not always be valid
 * let symbol = Value::<String>::symbol("fifteen").unwrap();
 *
 * // A list
 * let cons = Value::<String>::cons(
 *     int,
 *     Value::<String>::cons(
 *         float,
 *         Value::<String>::cons(
 *             string,
 *             Value::<String>::cons(
 *                 symbol,
 *                 Value::<String>::nil()
 *             )
 *         )
 *     )
 * );
 * ```
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
     * ```rust
     * use atoms::StringValue;
     * let symbol = StringValue::symbol("symbol").unwrap();
     * assert_eq!(symbol.to_string(), "symbol");
     * ```
     *
     * Depending on the type used to represent the symbol, this may fail to
     * produce a symbol and return a `None`. This will be presented as an error
     * by the parser.
     */
    pub fn symbol(s: &str) -> Option<Value<Sym>> {
        let sym = Sym::from_str(s);
        match sym {
            Ok(sym) => Some(Value::Symbol(sym)),
            Err(_) => None,
        }
    }

    /**
     * Create a new string
     *
     * ```rust
     * use atoms::StringValue;
     * let string = StringValue::string("string");
     * assert_eq!(string.to_string(), "\"string\"");
     * ```
     */
    pub fn string<S: Into<String>>(s: S) -> Value<Sym> {
        Value::Str(s.into())
    }

    /**
     * Create a new string
     *
     * ```rust
     * use atoms::StringValue;
     * let int = StringValue::int(42);
     * assert_eq!(int.to_string(), "42");
     * ```
     */
    pub fn int<I: Into<i64>>(i: I) -> Value<Sym> {
        Value::Int(i.into())
    }

    /**
     * Create a new float
     *
     * ```rust
     * use atoms::StringValue;
     * let float = StringValue::float(13.0);
     * assert_eq!(float.to_string(), "13.0");
     * ```
     */
    pub fn float<F: Into<f64>>(f: F) -> Value<Sym> {
        Value::Float(f.into())
    }

    /**
     * Shorthand from creating cons-cell lists out of `Vec`s.
     *
     * ```rust
     * use atoms::StringValue;
     * let ints = vec![
     *     StringValue::int(1), 
     *     StringValue::int(2), 
     *     StringValue::int(3), 
     *     StringValue::int(4), 
     *     StringValue::int(5), 
     *     StringValue::int(6)
     *  ];
     * let list = StringValue::list(ints);
     * assert_eq!(list.to_string(), "(1 2 3 4 5 6)");
     * ```
     */
    pub fn list<V: Into<Value<Sym>>>(mut source_vec: Vec<V>) -> Value<Sym> {

        // The end of the list is a nil
        let mut result = Value::Nil;

        while let Some(value) = source_vec.pop() {
            result = Value::cons(value.into(), result)
        }

        result
    }

    /**
     * Shorthand to convert a vec into a cons-cell list with a given map.
     *
     * ```rust
     * use atoms::StringValue;
     * let ints = vec![1, 2, 3, 4, 5, 6];
     * let list = StringValue::into_list(ints, |c| StringValue::int(*c));
     * assert_eq!(list.to_string(), "(1 2 3 4 5 6)");
     * ```
     */
    pub fn into_list<A, V: Into<Value<Sym>>, F>(source_vec: Vec<A>, map: F) -> Value<Sym>
        where F: Fn(&A) -> V {

        // Convert all members into values
        let converted = source_vec.iter().map(map).collect();
        
        Value::list(converted)
    }

    /**
     * Create a cons cell.
     *
     * ```rust
     * use atoms::StringValue;
     * let cons = StringValue::cons(
     *     StringValue::int(12),
     *     StringValue::string("13")
     * );
     * assert_eq!(cons.to_string(), "(12 . \"13\")");
     * ```
     */
    pub fn cons<V: Into<Value<Sym>>>(left: V, right: V) -> Value<Sym> {
        Value::Cons(Box::new(left.into()), Box::new(right.into()))
    }

    /**
     * Create a cons cell with only a left element.
     *
     * This creates a cons cell with the right element being a nil. This is
     * useful it you are manually constructing lists.
     *
     * ```rust
     * use atoms::StringValue;
     * let cons = StringValue::final_cons(
     *     StringValue::int(12),
     * );
     * assert_eq!(cons.to_string(), "(12)");
     * ```
     */
    pub fn final_cons<V: Into<Value<Sym>>>(left: V) -> Value<Sym> {
        Value::cons(left.into(), Value::Nil)
    }

    /**
     * Create a nil.
     *
     * ```rust
     * use atoms::StringValue;
     * assert_eq!(StringValue::nil().to_string(), "()");
     * ```
     */
    pub fn nil() -> Value<Sym> {
        Value::Nil
    }

    /**
     * Check if a value is a nil
     *
     * ```rust
     * use atoms::StringValue;
     * assert!(StringValue::nil().is_nil());
     * assert!(!StringValue::final_cons(StringValue::nil()).is_nil());
     * ```
     */
    pub fn is_nil(&self) -> bool {
        match *self {
            Value::Nil => true,
            _ => false,
        }
    }

    /**
     * Check if a value is a valid list.
     *
     * A value is a list if:
     * * it is a `Value::Nil`, or
     * * it is a `Value::Cons` with a rightmost element this is a list.
     *
     * ```rust
     * use atoms::StringValue;
     *
     * // `Nil` is a valid list
     * assert!(StringValue::nil().is_list());
     *
     * // `final_cons` ensures we get a valid list
     * assert!(StringValue::cons(
     *     StringValue::int(12),
     *     StringValue::final_cons(
     *         StringValue::float(13.0)
     *     )
     * ).is_list());
     *
     * // Manually terminated lists are valid
     * assert!(StringValue::cons(
     *     StringValue::int(12),
     *     StringValue::cons(
     *         StringValue::float(13.0),
     *         StringValue::nil()
     *     )
     * ).is_list());
     *
     * // These are not lists
     * assert!(!StringValue::int(12).is_list());
     * assert!(!StringValue::float(12.0).is_list());
     * assert!(!StringValue::string("12").is_list());
     * assert!(!StringValue::symbol("sym").unwrap().is_list());
     * assert!(!StringValue::cons(
     *     StringValue::nil(),
     *     StringValue::symbol("sym").unwrap()
     * ).is_list());
     * ```
     */
    pub fn is_list(&self) -> bool {
        match *self {
            Value::Nil => true,
            Value::Cons(_, ref right) => right.is_list(),
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
        _ => write!(f, " . {})", right),
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
    assert_eq!(format!("{:?}", Value::<String>::cons(
        Value::int(13),
        Value::cons(
            Value::float(13.333),
            Value::cons(
                Value::string("text"),
                Value::symbol("symbol").unwrap()
            )
        )
    )), "(13 13.333 \"text\" . symbol)");
}
