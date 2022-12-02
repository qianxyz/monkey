use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use super::Environment;
use crate::parser::{Block, Ident};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Int(i32),
    Bool(bool),
    Null,
    Ret(Box<Object>),
    Fn {
        params: Vec<Ident>,
        body: Block,
        env: Rc<RefCell<Environment>>,
    },
}

// Get the `truthy value` of the object.
// This is only implemented for some primitive types.
impl From<&Object> for bool {
    fn from(obj: &Object) -> Self {
        match obj {
            Object::Int(n) => *n != 0,
            Object::Bool(b) => *b,
            Object::Null => false,
            _ => unimplemented!(),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(n) => write!(f, "{}", n),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Null => write!(f, "null"),
            Self::Ret(obj) => write!(f, "{}", obj),
            Self::Fn {
                params,
                body,
                env: _,
            } => {
                write!(
                    f,
                    "fn({}) {}",
                    params
                        .iter()
                        .map(|i| i.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    body
                )
            }
        }
    }
}
