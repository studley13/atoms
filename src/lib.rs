//! A lightweight, self-contained s-expression parser and data format.
//! Use `parse` to get an s-expression from its string representation, and the
//! `Display` trait to serialize it, potentially by doing `sexp.to_string()`.

#![deny(missing_docs)]
#![deny(unsafe_code)]

extern crate unescape;

mod parse;
mod error;
mod value;

pub use value::Value;
pub use parse::Parser;
pub use error::{ParseResult, ParseError};

/*
#[test]
fn test_hello_world() {
  assert_eq!(
    parse("(hello -42\n\t  -4.0 \"world\") ; comment").unwrap(),
    list(&[ atom_sym("hello"), atom_i(-42), atom_f(-4.0), atom_s("world") ]));
}

#[test]
fn test_escaping() {
  assert_eq!(
    parse("(\"\\\"\\q\" \"1234\" 1234)").unwrap(),
    list(&[ atom_s("\"\\q"), atom_s("1234"), atom_i(1234) ]));
}

#[test]
fn test_pp() {
  let s = "(hello world (what is (up) (4 6.4 you \"123\\\\ \\\"\")))";
  let sexp = parse(s).unwrap();
  assert_eq!(s, sexp.to_string());
  assert_eq!(s, format!("{:?}", sexp));
}

#[test]
fn test_tight_parens() {
    let s = "(hello(world))";
    let sexp = parse(s).unwrap();
    assert_eq!(sexp, Sexp::List(vec![Sexp::Atom(Atom::Sym("hello".into())),
                                     Sexp::List(vec![Sexp::Atom(Atom::Sym("world".into()))])]));
    let s = "(this (has)tight(parens))";
    let s2 = "( this ( has ) tight ( parens ) )";
    assert_eq!(parse(s).unwrap(), parse(s2).unwrap());
}

#[test]
fn test_space_in_atom() {
  let sexp = list(&[ atom_s("hello world")]);
  let sexp_as_string = sexp.to_string();
  assert_eq!("(\"hello world\")", sexp_as_string);
  assert_eq!(sexp, parse(&sexp_as_string).unwrap());
}

#[allow(missing_docs)]
pub fn unwrap_atom_s(sexp: &Sexp) ->  Option<String> {
    match *sexp {
        Sexp::Atom(Atom::S(ref s)) => Some(s.clone()),
        Sexp::Atom(Atom::Sym(_)) => None,
        Sexp::Atom(Atom::I(_)) => None,
        Sexp::Atom(Atom::F(_)) => None,
        Sexp::List(_) => None,
    }
}

#[allow(missing_docs)]
pub fn unwrap_atom_sym(sexp: &Sexp) ->  Option<String> {
    match *sexp {
        Sexp::Atom(Atom::S(_)) => None,
        Sexp::Atom(Atom::Sym(ref s)) => Some(s.clone()),
        Sexp::Atom(Atom::I(_)) => None,
        Sexp::Atom(Atom::F(_)) => None,
        Sexp::List(_) => None,
    }
}

#[allow(missing_docs)]
pub fn unwrap_atom_i(sexp: &Sexp) ->  Option<i64> {
    match *sexp {
        Sexp::Atom(Atom::S(_)) => None,
        Sexp::Atom(Atom::Sym(_)) => None,
        Sexp::Atom(Atom::I(i)) => Some(i.clone()),
        Sexp::Atom(Atom::F(_)) => None,
        Sexp::List(_) => None,
    }
}

#[allow(missing_docs)]
pub fn unwrap_atom_f(sexp: &Sexp) ->  Option<f64> {
    match *sexp {
        Sexp::Atom(Atom::S(_)) => None,
        Sexp::Atom(Atom::Sym(_)) => None,
        Sexp::Atom(Atom::I(_)) => None,
        Sexp::Atom(Atom::F(f)) => Some(f.clone()),
        Sexp::List(_) => None,
    }
}

#[allow(missing_docs)]
pub fn unwrap_list (sexp: &Sexp) -> Option<Vec<Sexp>> {
    match *sexp {
        Sexp::Atom(Atom::S(_)) => None,
        Sexp::Atom(Atom::Sym(_)) => None,
        Sexp::Atom(Atom::I(_)) => None,
        Sexp::Atom(Atom::F(_)) => None,
        Sexp::List(ref v) => Some(v.clone()),
    }
}

#[test]
fn test_unwrap() {
  assert_eq!(Some(3), unwrap_atom_i(&atom_i(3)));
  assert_eq!(Some(3.0), unwrap_atom_f(&atom_f(3.0)));
  assert_eq!(Some("a".to_string()), unwrap_atom_s(&atom_s("a")));
  assert_eq!(Some("a".to_string()), unwrap_atom_sym(&atom_sym("a")));
  assert_eq!(Some(vec![atom_i(3)]), unwrap_list(&list(&[atom_i(3)])));
}
*/

