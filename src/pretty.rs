//! Pretty Printing of Values

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::fmt::{self, Display, Debug, Formatter};
use std::ops::Deref;

use value::Value;


/**
 * Inform the printer of how to lay out the cons.
 *
 * Symbols that implement this inform the pretty printer of how lists that they
 * are the first element of should be displayed.
 */
pub trait Layout {
    /**
     * The number of elements that should occupy the same line as the first
     * element of the list.
     *
     * A `0u64` in this case would mean that the first symbol should be on its
     * own line.
     *
     * This is only used where the cons in question has a depth of more than 2.
     */
    fn share_line(&self) -> u64 {1u64}

    /**
     * The cons should always be made multiline.
     *
     * This ensures that a cons beginning with a particular symbol will always
     * be displayed over mutliple lines, regardless of the depth or number of
     * elements.
     */
    fn always_multiline(&self) -> bool {false}
}

/**
 * Produce a pretty wrapped value that will display as pretty-printed.
 */
pub trait Pretty {
    /**
     * THe type used to represent a symbol.
     */
    type Sym: Sized;
    
    /**
     * Produce a value that displays in pretty-printed form.
     */
    fn pretty(self) -> PrettyValue<Self::Sym>;
}

impl<Sym> Pretty for Value<Sym> where Sym: Sized {
    type Sym = Sym;

    fn pretty(self) -> PrettyValue<Sym> {
        PrettyValue{
            value: self
        }
    }
}

/**
 * Implementation for strings is default.
 */
impl Layout for String {}

/**
 * A wrapper for a value that changes its printing behaviour such that it pretty
 * prints.
 */
pub struct PrettyValue<Sym> {
    value: Value<Sym>
}


impl<Sym> Deref for PrettyValue<Sym> where Sym: Sized {
    type Target = Value<Sym>;
    fn deref(&self) -> &Value<Sym> {
        &self.value
    }
}

impl<Sym> Display for PrettyValue<Sym> where Sym: Layout + ToString {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.value)
    }
}

impl<Sym> Debug for PrettyValue<Sym> where Sym: Layout + ToString {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}
