//! Representation of the S-expression tree.

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::str::FromStr;
use std::fmt::{self, Display, Debug, Formatter};
use std::ops::Deref;

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
pub enum Value<Sym> {
    /// S-expression in data mode
    Data(Box<Value<Sym>>),
    /// S-expression in code mode
    Code(Box<Value<Sym>>),
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

impl<Sym: FromStr> Value<Sym> {

    /**
     * Automatically convert value
     *
     * This automatically creates the most sensible value for the types:
     *
     * * `i64`
     * * `f64`
     * * `String`
     *
     * ```rust
     * use atoms::StringValue;
     * assert_eq!(StringValue::auto(13), StringValue::int(13));
     * assert_eq!(StringValue::auto(3.1415), StringValue::float(3.1415));
     * assert_eq!(StringValue::auto("Text"), StringValue::string("Text"));
     * ```
     */
    pub fn auto<T>(value: T) -> Value<Sym> where T: AutoValue<Sym> {
        value.auto()
    }

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
     * Mark a value as code
     *
     * When using mixed-mode data, this marks an s-expression as code.
     *
     * ```rust
     * use atoms::StringValue;
     * StringValue::code(StringValue::symbol("map").unwrap()).to_string();
     * ```
     */
    pub fn code<V: Into<Value<Sym>>>(value: V) -> Value<Sym> {
        Value::Code(Box::new(value.into()))
    }

    /**
     * Mark a value as data
     *
     * When using mixed-mode data, this marks an s-expression as data.
     *
     * ```rust
     * use atoms::StringValue;
     * assert_eq!(
     *     StringValue::data(StringValue::symbol("apple").unwrap()).to_string(),
     *     "'apple"
     * )
     * ```
     */
    pub fn data<V: Into<Value<Sym>>>(value: V) -> Value<Sym> {
        Value::Data(Box::new(value.into()))
    }

    /**
     * Check if a value is a cons
     *
     * ```rust
     * use atoms::StringValue;
     * assert!(StringValue::cons(
     *     StringValue::nil(),
     *     StringValue::nil()
     * ).is_cons());
     * assert!(!StringValue::nil().is_cons());
     * ```
     */
    pub fn is_cons(&self) -> bool {
        match *self {
            Value::Cons(_, _) => true,
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

    /**
     * Returns if is a wrapped data value
     *
     * ```rust
     * use atoms::StringValue;
     * assert!(
     *     StringValue::data(StringValue::symbol("apple").unwrap()).is_data()
     * );
     * assert!(
     *     !StringValue::code(StringValue::symbol("apple").unwrap()).is_data()
     * );
     * assert!(
     *     !StringValue::symbol("apple").unwrap().is_code()
     * );
     * ```
     */
    pub fn is_data(&self) -> bool {
        match *self {
            Value::Data(_) => true,
            _ => false,
        }
    }

    /**
     * Returns if is a wrapped code value
     *
     * ```rust
     * use atoms::StringValue;
     * assert!(
     *     StringValue::code(StringValue::symbol("map").unwrap()).is_code()
     * );
     * assert!(
     *     !StringValue::data(StringValue::symbol("map").unwrap()).is_code()
     * );
     * assert!(
     *     !StringValue::symbol("map").unwrap().is_code()
     * );
     * ```
     */
    pub fn is_code(&self) -> bool {
        match *self {
            Value::Code(_) => true,
            _ => false,
        }
    }

    /**
     * Unwrap code and data values.
     *
     * Code and data values are really only tagging their contents. To get the
     * actual value of any `Value`, you can always `unwrap` it. Note that
     * `unwrap` only unwraps a single layer, to completey unwrap an entire
     * s-expression use `unwrap_all`.
     *
     * ```rust
     * use atoms::StringValue;
     * assert_eq!(
     *     StringValue::code(StringValue::symbol("inner").unwrap()).unwrap(),
     *     StringValue::symbol("inner").unwrap()
     * );
     * assert_eq!(
     *     StringValue::data(StringValue::symbol("inner").unwrap()).unwrap(),
     *     StringValue::symbol("inner").unwrap()
     * );
     * assert_eq!(
     *     StringValue::symbol("inner").unwrap().unwrap(),
     *     StringValue::symbol("inner").unwrap()
     * );
     * ```
     */
    pub fn unwrap(self) -> Value<Sym> {
        match self {
            Value::Code(code) => code.unwrap(),
            Value::Data(data) => data.unwrap(),
            other => other,
        }
    }

    /**
     * Fully unwrap tree. Unwraps all data and code values.
     *
     * This will recursively unwrap an entire s-expression, removing any
     * information about data or code. To only unwrap the outermost layer,
     * use `unwrap`.
     *
     * ```rust
     * use atoms::StringValue;
     * assert_eq!(
     *     StringValue::code(StringValue::list(vec![
     *         StringValue::data(StringValue::auto(14)),
     *         StringValue::data(StringValue::auto(13.000)),
     *         StringValue::auto("twelve"),
     *     ])).unwrap_full(),
     *     StringValue::list(vec![
     *         StringValue::auto(14),
     *         StringValue::auto(13.000),
     *         StringValue::auto("twelve"),
     *     ])
     * );
     * ```
     */
    pub fn unwrap_full(self) -> Value<Sym> {
        match self {
            Value::Code(code) => code.unwrap_full(),
            Value::Data(data) => data.unwrap_full(),
            Value::Cons(left, right) => 
                Value::cons(
                    left.unwrap_full(), 
                    right.unwrap_full()
                ),
            _ => self,
        }
    }

    /**
     * Is a multimode data s-expression
     *
     * This will return true if the given value is explicitly tagged as data
     * and contains children at any level that are code.
     *
     * ```rust
     * use atoms::StringValue;
     * assert!(
     *     StringValue::data(StringValue::list(vec![
     *         StringValue::code(StringValue::auto(14)),
     *         StringValue::code(StringValue::auto(13.000)),
     *         StringValue::auto("twelve"),
     *     ])).is_multimode()
     * );
     * assert!(
     *     !StringValue::data(StringValue::list(vec![
     *         StringValue::auto(14),
     *         StringValue::auto(13.000),
     *         StringValue::auto("twelve"),
     *     ])).is_multimode()
     * );
     * ```
     */
    pub fn is_multimode(&self) -> bool {
        match *self {
            Value::Data(ref contents) => contents.code_children(),
            _ => false
        }
    }

    /**
     * Finds any child in code mode
     */
    fn code_children(&self) -> bool {
        match *self {
            Value::Code(_) => true,
            Value::Data(ref child) => 
                child.code_children(),
            Value::Cons(ref left, ref right) => 
                left.code_children() || right.code_children(),
            _ => false
        }
    }
}

impl<Sym> AsRef<Value<Sym>> for Value<Sym> {
    fn as_ref(&self) -> &Self {
        match *self {
            Value::Data(ref data) => data,
            Value::Code(ref code) => code,
            _ => self
        }
    }
}

impl<Sym> Display for Value<Sym> where Sym: ToString + FromStr {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            Value::Cons(ref left, ref right) => display_cons(left, right, true, f),
            Value::Str(ref text) => write!(f, "\"{}\"", escape_string(&text)),
            Value::Symbol(ref sym) => write!(f, "{}", escape_string(&sym.to_string().replace(" ", "\\ "))),
            Value::Int(ref i) => write!(f, "{}", i),
            Value::Float(ref fl) => format_float(f, *fl),
            Value::Nil => write!(f, "()"),
            // TODO: Apply quoting
            Value::Data(ref data) => 
                if self.is_multimode() {
                    write!(f, "{}", MultiMode::new(self))
                } else {
                    write!(f, "'{}", data)
                },
            Value::Code(ref code) => write!(f, "{}", code),
        }
    }
}

impl<Sym> Debug for Value<Sym> where Sym: ToString + FromStr {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

fn display_cons<Sym>(left: &Value<Sym>, right: &Value<Sym>, root: bool, f: &mut Formatter) 
    -> Result<(), fmt::Error> where Sym: ToString + FromStr {

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
    if float.fract() == 0f64 {
        write!(f, "{:.1}", float)
    } else {
        write!(f, "{}", float)
    }
}

/**
 * A helper struct that wraps a value to assist in multimode rendering, i.e.
 * ensures that quasiqutoing is rendered properly
 */
#[derive(PartialEq, PartialOrd)]
struct MultiMode<'a, Sym: 'a + ToString + FromStr> {
    value: &'a Value<Sym>,
    is_data: bool,
    declare_mode: bool,
}

impl<'a, Sym: 'a + FromStr + ToString> MultiMode<'a, Sym> {
    /**
     * Create a new nultimode-tagged value. We assume that this is
     * only used to the root of a data expression that contains code
     * expressions.
     */
    fn new(data: &'a Value<Sym>) -> Self {
        match *data {
            Value::Data(_) => MultiMode {
                value: data,
                is_data: true,
                declare_mode: true
            },
            _ => panic!("Multimode::new only to be used on Value::Data"),
        }
    }

    /**
     * Used to wrap a child value dependent on the mode of parent
     */
    fn wrap_child<'b>(&self, child: &'b Value<Sym>) -> MultiMode<'b, Sym> {
        let mode_flip = match *child {
            Value::Data(_) => !self.is_data,
            Value::Code(_) => self.is_data,
            _ => false,
        };

        MultiMode {
            value: child,
            is_data: self.is_data ^ mode_flip,
            declare_mode: mode_flip,
        }
    }
}

impl<'a, Sym: 'a + ToString + FromStr> Display for MultiMode<'a, Sym> {

    /*
     * This is implemented such that once we are displaying something tagged as 
     * multimode, we will never call the `Display` on a `Value::Data` or 
     * `Value::Code` directly but will always unwrap them. This ensures that we
     * never end up with multiple layers of multi-mode.
     */
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        if self.declare_mode {
            // Explicitly display the mode switch
            match *self.value {
                Value::Data(ref data) =>
                    write!(f, "`{}", self.wrap_child(data)),
                Value::Code(ref code) => 
                    write!(f, ",{}", self.wrap_child(code)),
                _ => unreachable!(),
            }
        } else if let Value::Cons(ref left, ref right) = *self.value {
            // Render out a cons
            display_cons_multimode(
                self.wrap_child(left), 
                self.wrap_child(right), 
                true, 
                f
            )
        } else {
            // Display all other simple values
            match *self.value {
                Value::Data(ref data) =>
                    write!(f, "{}", self.wrap_child(data)),
                Value::Code(ref code) => 
                    write!(f, "{}", self.wrap_child(code)),
                _ => write!(f, "{}", self.value),
            }
        }
    }
}

impl<'a, Sym: 'a + ToString + FromStr> Debug for MultiMode<'a, Sym> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

fn display_cons_multimode<Sym>(left: MultiMode<Sym>, right: MultiMode<Sym>, root: bool, f: &mut Formatter) 
    -> Result<(), fmt::Error> where Sym: ToString + FromStr {

    if root {
        try!(write!(f, "("));
    }

    // Write the left value
    try!(write!(f, "{}", left));

    // Write the right value
    match *right {
        Value::Nil => write!(f, ")"),
        Value::Cons(ref i_left, ref i_right) => {
            try!(write!(f, " "));
            display_cons_multimode(
                right.wrap_child(i_left), 
                right.wrap_child(i_right), 
                false, 
                f
            )
        }
        _ => write!(f, " . {})", right),
    }
}

impl<'a, Sym: FromStr + ToString + Sized> Deref for MultiMode<'a, Sym> {
    type Target = Value<Sym>;

    fn deref(&self) -> &Value<Sym> {
        self.value
    }
}

///Automatic Conversion
pub trait AutoValue<Sym> {
    fn auto(self) -> Value<Sym>;
}

impl<Sym: FromStr> AutoValue<Sym> for Value<Sym> {
    fn auto(self) -> Value<Sym> {
       self 
    }
}

impl<Sym: FromStr> AutoValue<Sym> for i64 {
    fn auto(self) -> Value<Sym> {
        Value::int(self)
    }
}

impl<Sym: FromStr> AutoValue<Sym> for f64 {
    fn auto(self) -> Value<Sym> {
        Value::float(self)
    }
}

impl<'a, Sym: FromStr> AutoValue<Sym> for &'a str {
    fn auto(self) -> Value<Sym> {
        Value::string(self)
    }
}

impl<Sym: FromStr> AutoValue<Sym> for String {
    fn auto(self) -> Value<Sym> {
        Value::string(self)
    }
}

/**
 * Inlining s-expressions
 *
 * This macro makes it trivial to inline s-expressions. For example, to inline
 * the s-expression:
 *
 * ```lisp
 * (the 'quick brown `(fox ,jumped over the 3 "lazy"  dogs ,(aged 42.5)))
 * ```
 *
 * The following macro could be used (in this case we are using `StringValue`
 * as the value type):
 *
 * ```rust
 * #[macro_use]
 * extern crate atoms;
 *
 * use atoms::{StringValue, Parser};
 *
 * fn main() {
 *     let val = Parser::new(
 *         &"(the 'quick brown `(fox ,jumped over the 3 \"lazy\"  dogs ,(aged 42.5)))"
 *     ).parse::<String>().unwrap();
 *     let inline = s_tree!(StringValue:
 *         ([the] [d:[quick]] [brown] [d:(
 *             [fox] [c:[jumped]] [over] [the] 3 "lazy" [dogs] [c:(
 *                 [aged] 42.5
 *             )]
 *         )])
 *     );
 *     assert_eq!(val, inline);
 * }
 * ```
 *
 * # Structure
 *
 * The first part of the macro tells it what type to load the expression as and
 * must be some kind of `Value`. This is followed by a literal `:` and then the
 * expressions itself.
 *
 * ```rust
 * #[macro_use]
 * extern crate atoms;
 *
 * use atoms::StringValue;
 *
 * fn main() {
 *     s_tree!(StringValue: (1 2 3 4 5 6));
 * }
 * ```
 *
 * # Automatic Conversion
 *
 * The following types get automatically converted, whether they are literals or 
 * variables:
 *
 * * `String`
 * * `i64`
 * * `f64`
 *
 * This means you can just place them in your expression as-is.
 *
 * ```rust
 * #[macro_use]
 * extern crate atoms;
 *
 * use atoms::StringValue;
 *
 * fn main() {
 *     s_tree!(StringValue: (13 "text" 3.1415));
 * }
 * ```
 * 
 * # Cons, List, and Nil
 *
 * These all work much the same way they do in Lisp. Cons are joined with a `.`,
 * lists and cons are bound between '(' and ')', and nil is simply `()`. One
 * important thing to note is that constructs like `(1 2 3 . 4)` have to be
 * constructed from explicit cons cells.
 *
 * ```rust
 * #[macro_use]
 * extern crate atoms;
 *
 * use atoms::StringValue;
 *
 * fn main() {
 *     s_tree!(StringValue: ());
 *     s_tree!(StringValue: (1 2 3 4 5));
 *     s_tree!(StringValue: ((1 . 2) . ((3 . 4) . 5)));
 *     assert_eq!(
 *         s_tree!(StringValue: (1 2 3 4 5)),
 *         s_tree!(StringValue: (1 . (2 . (3 . (4 . (5 . ()))))))
 *     );
 * }
 * ```
 *
 * # Symbols
 *
 * Symbols can be used in 2 ways. The first is the conversion method, which is
 * for more complex symbols, is used with a `&str` and involves wrapping it in
 * a `[s:]` construct. The second form is *quoting* and simply involves
 * wrapping a series of tokens in `[]`.
 *
 * ```rust
 * #[macro_use]
 * extern crate atoms;
 *
 * use atoms::StringValue;
 *
 * fn main() {
 *     s_tree!(StringValue: ([one] [s:"two"] [s:"compleχex"]));
 * }
 * ```
 *
 * # Data and Code
 *
 * Any value can be tagged as being data or code by wrapping it in the relevant
 * construct, which are `[d:]` and `[c:]` respectively. 
 *
 * ```rust
 * #[macro_use]
 * extern crate atoms;
 *
 * use atoms::{StringValue, Parser};
 *
 * fn main() {
 *     assert_eq!(
 *         Parser::new(&"'(this is ,quasiquoted ,(data `0 `12.3))")
 *             .parse::<String>().unwrap(),
 *         s_tree!(StringValue: 
 *             [d:([this] [is] [c:[quasiquoted]] [c:(
 *                 [data] [d:0] [d:12.3]
 *             )])]
 *         )
 *     );
 * }
 * ```
 *
 */
#[macro_export]
macro_rules! s_tree {
    ($t:ident: ()) => {
        $t::nil();
    };
    ($t:ident: ($l:tt . $r:tt)) => {
        $t::cons(s_tree!($t: $l), s_tree!($t: $r))
    };
    ($t:ident: ($($i:tt)*)) => {
        $t::list(vec![
            $(s_tree!($t: $i)),*
        ])
    };
    ($t:ident: [d:$v:tt]) => {
        $t::data(s_tree!($t: $v))
    };
    ($t:ident: [c:$v:tt]) => {
        $t::code(s_tree!($t: $v))
    };
    ($t:ident: [s:$v:tt]) => {
        $t::symbol($v).unwrap()
    };
    ($t:ident: [$v:tt]) => {
        $t::symbol(stringify!($v)).unwrap()
    };
    ($t:ident: [$k:ident:$v:expr]) => {
        $t::$k($v)
    };
    ($t:ident: $v:expr) => {
        $t::auto($v)
    };
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
    assert_eq!(
        format!("{:?}", s_tree!(StringValue: (13 13.333 "text" [symbol]))), 
        "(13 13.333 \"text\" symbol)"
    );
    assert_eq!(
        format!("{:?}", s_tree!(StringValue: (13 . (13.333 . ("text" . [symbol]))))),
        "(13 13.333 \"text\" . symbol)"
    );
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

#[test]
fn render_multimode() {
    assert_eq!(format!(
        "{:?}", 
        StringValue::code(StringValue::list(vec![
            StringValue::data(StringValue::symbol("test").unwrap()),
            StringValue::data(StringValue::list(vec![
                StringValue::symbol("this").unwrap(),
                StringValue::symbol("is").unwrap(),
                StringValue::code(StringValue::symbol("not").unwrap()),
                StringValue::symbol("data").unwrap(),
            ])),
            StringValue::symbol("code?").unwrap(),
        ]))
    ), "('test `(this is ,not data) code?)");
    assert_eq!(format!(
        "{:?}", 
        s_tree!(StringValue: (
            [d:[test]] 
            [d:([this] [is] [c:[not]] [data] [int:61])] 
            [s:"code"]
        ))
    ), "('test `(this is ,not data 61) code)");
}
