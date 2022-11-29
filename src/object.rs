use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub enum Object {
    Int(i32),
    Bool(bool),
    Null,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(n) => write!(f, "{}", n),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Null => write!(f, "null"),
        }
    }
}
