//! Pretty Printing of Values
//!
//! The pretty printing rules here are made to be as simple to *implement*
//! as possible.
//!
//! # Defining Values
//!
//! ## Code versus Data
//!
//! For a `Symbol` to be considered **code**, it must be explicitly marked as 
//! **code** when it is in a **data** block. If a `Symbol` is not inside a 
//! **data** block, it is considered **code**.
//!
//! For a `Cons` to be considered **code**, it must be a *list* and must also 
//! start with a symbol that is **code**.
//!
//! ## Depth
//!
//! * The *depth* of an `Symbol, `Int`, `Str`, `Float`, or `Nil` is 0.
//! * The *depth* of a `Cons` is the greater of the depth of the *left* value
//!   + 1 or the depth of the *right* value.
//!
//! # Displaying Values
//!
//! * A `Cons` that is **data** is rendered such that
//!   * the *root* starts with the opening brace followed by its *left* value.
//!   * If the *left* value
//!     * is a `Cons`, it is displayed with its opening brace followed by its 
//!       left value across 
//!       * a single line if it has a *depth* of 1, or 
//!       * across multiple lines if it has a *depth* of more than 1, otherwise
//!     * is rendered as normal.
//!   * If the *right* value
//!     * is a `Cons`, it is displayed a
//!
//!   * If the *right* value is a `Nil`, the *left* value is displayed on
//!     the current line followed immediately by a closing brace.
//!   * If the *right* value is a `Cons`:
//!     * With a depth of 1, it is displayed
//!
//! * *Lists* that are **data** and *cons trees* that are *list-like* with a 
//!   depth of 1 are displayed on a single line.
//!
//!   ```listp
//!   (data on a single line)
//!   (cons on a single . line)
//!   (this
//!     has
//!     a
//!     (depth) of two)
//!   ```
//!
//! * *Lists* that are **data** and *cons trees* that are *list-like* with a 
//!   depth greater than 1 are displayed across multiple lines with each value 
//!   on a different line and with the last value followed by the closing brace.
//!   *Cons-trees* have the cons-join on the same line as the last argument.
//!
//!   ```lisp
//!   (I
//!       am
//!       (data across many)
//!       lines)
//!   (I
//!       am
//!       (a . cons)
//!       (data across many)
//!       . lines)
//!   (I am a cons . tree)
//!               . a)
//!           . cons)
//!       . tree)
//!
//!   (a . b)
//!   ((a . b)
//!     . b)
//!   ```
//!
//! * *Lists* that are **code** are rendered based on the `Layout` of the
//!   symbol at the start of the list.
//!   * If the `Layout::always_multiline` is true, then the block will always
//!     be split across multiple lines, otherwise it will only be split if
//!     the depth of the list is greater than 1.
//!   * `Layout::
//!   * If it is **code**, the `Layout` of the first symbol will be consulted.
//!     * `Layout::with_n_args` determines how many elements share the first
//!       line with the first symbol.
//!     * 

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::fmt::{self, Display, Debug, Formatter};
use std::ops::Deref;
use std::cmp::max;

use value::Value;

/**
 * Classify values for printing
 */
trait Classify {
    /// THe depth of a value
    fn depth(&self) -> u64;
}

impl<S> Classify for Value<S> {
    fn depth(&self) -> u64 {
        match *self {
            Value::Nil => 0u64,
            Value::Symbol(_) => 0u64,
            Value::Str(_) => 0u64,
            Value::Int(_) => 0u64,
            Value::Float(_) => 0u64,
            Value::Data(ref v) => v.depth(),
            Value::Code(ref v) => v.depth(),
            Value::Cons(ref left, ref right) =>
                max(left.depth() + 1, right.depth())
        }
    }
}


/**
 * Inform the printer of how render *code*.
 *
 * A type used for `Symbol` **must** implement this trait in order to be pretty
 * printed. It informs the displays of how cons lists should be rendered.
 */
pub trait Layout {
    /**
     * The number of elements that should occupy the same line as the first
     * element of the list.
     *
     * A `0u64` (which is the default) in this case would mean that the first 
     * symbol should be on its own line.
     *
     * This is only used where the cons in question has a depth of more than 1.
     */
    fn first_line_args(&self) -> u64 {0u64}
}

/**
 * Produce a pretty wrapped value that will display as pretty-printed.
 *
 * In this case, all the work is done for you, you just need to have the
 * trait in scope in order to use pretty printing.
 *
 * To print a value in pretty printed form is as easy as
 *
 * ```rust
 * use atoms::{StringValue, Pretty};
 * let value = StringValue::into_list(
 *     vec!["a", "b", "c", "d", "e"],
 *     |s| StringValue::symbol(&s).unwrap()
 *  );
 *  println!("{}", value.pretty());
 */
pub trait Pretty<'a> {
    /**
     * The type used to represent a symbol.
     */
    type Sym: Sized;
    
    /**
     * Produce a value that displays in pretty-printed form.
     */
    fn pretty(&'a self) -> PrettyValue<'a, Self::Sym>;
}

impl<'a, Sym> Pretty<'a> for Value<Sym> where Sym: Sized {
    type Sym = Sym;

    fn pretty(&self) -> PrettyValue<Sym> {
        PrettyValue{
            value: self,
            data: false,
            stop: Indentation::Tab,
            // If the root element is across multiple linesm it should indent
            level: 1u64,
            single_line: false,
        }
    }
}

/**
 * Implementation for strings is default.
 */
impl Layout for String {}

// Indentation mode
#[derive(Clone, Copy)]
enum Indentation {
    Tab,
    Spaces(u64),
}

impl ToString for Indentation {
    fn to_string(&self) -> String {
        match *self {
            Indentation::Tab => "\t".to_string(),
            Indentation::Spaces(n) => {
                let mut string = String::new();
                for _ in 0..n {
                    string.push(' ')
                }
                string
            }
        }
    }
}

/**
 * A wrapper for a value that changes its printing behaviour such that it pretty
 * prints.
 */
pub struct PrettyValue<'a, Sym: 'a> {
    /// Stored Value
    value: &'a Value<Sym>,

    /// Is data
    data: bool,

    /// Indentation stop
    stop: Indentation,

    /// Indentation level
    level: u64,

    /// Print on single line (ugly)
    single_line: bool,
}

impl<'a, 'b, S> PrettyValue<'a, S> {
    /// Set the indentation to tabs
    pub fn with_tabs(mut self) -> PrettyValue<'a, S> {
        self.stop = Indentation::Tab;
        self
    }

    /// Set the indentation to *n* spaces
    pub fn with_spaces(mut self, spaces: u64) -> PrettyValue<'a, S> {
        self.stop = Indentation::Spaces(spaces);
        self
    }
    
    /// Print value on single line (ugly)
    pub fn ugly(mut self) -> PrettyValue<'a, S> {
        self.single_line = true;
        self
    }

    /// Set the value to render as data
    fn as_data(mut self) -> PrettyValue<'a, S> {
        self.data = true;
        self
    }

    /// Set the value to render as data
    fn as_code(mut self) -> PrettyValue<'a, S> {
        self.data = false;
        self
    }

    /// Create a child
    fn create_child(&self, child: &'b Value<S>) -> PrettyValue<'b, S> {
        let level = self.level + 1;
        PrettyValue {
            value: child,
            data: self.data,
            stop: self.stop,
            level: level,
            single_line: self.single_line,
        }
    }

    /// Get the separator for a given level
    fn get_separator(&self) -> String {
        if self.single_line {
            " ".to_string()
        } else if self.value.depth() > 1 {
            let mut sep = String::new();
            sep.push('\n');
            for _ in 0..self.level {
                sep.push_str(self.stop.to_string().as_str());
            }
            sep
        } else {
            " ".to_string()
        }
    }
}

impl<'a, Sym: Layout> PrettyValue<'a, Sym> {
    /// Get the next separator 
    ///
    /// Should only eve be called on a cons
    fn first_line_args(&self) -> u64 {
        match *self.value {
            Value::Cons(ref left, _) =>
                if self.data {
                    0u64
                } else {
                    PrettyValue::first_line_args_value(left)
                },
            _ => unreachable!(),
        }
    }

    fn first_line_args_value(v: &Value<Sym>) -> u64 {
        match *v {
            Value::Code(ref code) =>
                PrettyValue::first_line_args_value(code),
            Value::Symbol(ref sym) => sym.first_line_args(),
            _ => 0u64,
        }
    }

    /// Get the next separator to use given the number of arguments shown
    fn next_sep(&self, args: u64) -> String {
        if args < self.first_line_args() {
            " ".to_string()
        } else {
            self.get_separator()
        }
    }
}

impl<'a, Sym: ToString + Layout> PrettyValue<'a, Sym> {
    fn pretty_cons(&self, f: &mut Formatter, left: &Value<Sym>, right: &Value<Sym>) 
        -> Result<(), fmt::Error> {
        // Open Braces and display left
        try!(write!(f, "({}", self.create_child(left)));

        // Display list
        let mut next = right;
        let mut args = 0u64;
        loop {
            // Use N separators
            match *next {
                Value::Nil => {
                    return write!(f, ")");
                },
                Value::Cons(ref left, ref right) => {
                    try!(write!(f, 
                        "{}{}", 
                        self.next_sep(args), 
                        self.create_child(left.as_ref())
                    ));
                    next = right.as_ref();
                    args += 1;
                }
                _ => {
                    return write!(f, 
                        "{}. {})", 
                        self.next_sep(args), 
                        self.create_child(next.as_ref())
                    );
                }
            }
        }
    }
}

impl<'a, Sym> Deref for PrettyValue<'a, Sym> where Sym: Sized {
    type Target = Value<Sym>;
    fn deref(&self) -> &Value<Sym> {
        self.value
    }
}

impl<'a, Sym> Display for PrettyValue<'a, Sym> where Sym: Layout + ToString {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self.value {
            Value::Data(ref v) => {
                let child = self.create_child(v.as_ref()).as_data();
                if self.data {
                    // Don't annotate if already data
                    write!(f, "{}", child)
                } else {
                    if self.value.is_multimode() {
                        write!(f, "`{}", child)
                    } else {
                        write!(f, "'{}", child)
                    }
                }
            },
            Value::Code(ref v) => {
                let child = self.create_child(v.as_ref()).as_code();
                if self.data {
                    // Annotate if in data block
                    write!(f, ",{}", child)
                } else {
                    write!(f, "{}", child)
                }
            },
            Value::Cons(ref left, ref right) => 
                self.pretty_cons(f, 
                    left.as_ref(), 
                    right.as_ref()
                ),
            _ => write!(f, "{}", self.value)
        }
    }
}

impl<'a, Sym> Debug for PrettyValue<'a, Sym> where Sym: Layout + ToString {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

#[test]
fn pretty_basic() {
    use value::StringValue;

    macro_rules! pretty_test {
        ($v:expr, $r:expr) => {
            assert_eq!($v.pretty().to_string(), $r)
        }
    }

    pretty_test!(s_tree!(StringValue: ([a] [b] [c] [d])), "(a b c d)");
    pretty_test!(s_tree!(StringValue: ([a] [b] [c] [d])), "(a b c d)");
}

#[test]
fn pretty_symmetry() {
    use value::StringValue;
    use parse::Parser;

    macro_rules! pretty_symmetry {
        ($v:expr) => {
            let string = $v.pretty().to_string();
            let parser = Parser::new(&string);
            assert_eq!(parser.parse_basic().unwrap(), $v)
        }
    }

    pretty_symmetry!(s_tree!(StringValue: ([a] [b] [c] [d])));
}
