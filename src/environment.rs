use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::Ident;
use crate::evaluator::{RuntimeError, RuntimeResult};
use crate::object::Object;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Environment {
    inner: HashMap<Ident, Object>,
    outer: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
            outer: None,
        }
    }

    pub fn enclose(outer: Rc<RefCell<Environment>>) -> Self {
        Self {
            inner: HashMap::new(),
            outer: Some(outer),
        }
    }

    pub fn get(&self, ident: &Ident) -> RuntimeResult<Object> {
        if let Some(obj) = self.inner.get(ident) {
            Ok(obj.to_owned())
        } else if let Some(Ok(obj)) = self.outer.as_ref().map(|h| h.borrow().get(ident)) {
            Ok(obj)
        } else {
            Err(RuntimeError::UnboundIdentifier(ident.to_owned()))
        }
    }

    pub fn set(&mut self, ident: Ident, obj: Object) {
        self.inner.insert(ident, obj);
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}
