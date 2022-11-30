use std::collections::HashMap;

use crate::ast::Ident;
use crate::evaluator::{RuntimeError, RuntimeResult};
use crate::object::Object;

pub struct Environment(HashMap<Ident, Object>);

impl Environment {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn get(&self, ident: Ident) -> RuntimeResult<Object> {
        match self.0.get(&ident) {
            Some(obj) => Ok(obj.to_owned()),
            None => Err(RuntimeError::UnboundIdentifier(ident)),
        }
    }

    pub fn set(&mut self, ident: Ident, obj: Object) {
        self.0.insert(ident, obj);
    }
}
