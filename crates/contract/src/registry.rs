//! Programs by name. A name is either an exact registered program or
//! `prefix:params` handled by a factory, so parameterised programs (a bond
//! for one receipt, a payment gated on one attestation) can be named on the
//! wire and rebuilt identically by both parties.

use std::collections::HashMap;
use std::sync::Arc;

use anyhow::{anyhow, Result};

use crate::Program;

type Factory = Arc<dyn Fn(&str) -> Result<Arc<dyn Program>> + Send + Sync>;

#[derive(Clone, Default)]
pub struct ProgramRegistry {
    exact: HashMap<String, Arc<dyn Program>>,
    factories: HashMap<String, Factory>,
}

impl ProgramRegistry {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with(mut self, p: Arc<dyn Program>) -> Self {
        self.register(p);
        self
    }
    pub fn register(&mut self, p: Arc<dyn Program>) {
        self.exact.insert(p.name().to_string(), p);
    }
    /// `prefix:params` names are built by `f(params)`.
    pub fn register_factory(&mut self, prefix: &str, f: impl Fn(&str) -> Result<Arc<dyn Program>> + Send + Sync + 'static) {
        self.factories.insert(prefix.to_string(), Arc::new(f));
    }
    pub fn resolve(&self, name: &str) -> Result<Arc<dyn Program>> {
        if let Some(p) = self.exact.get(name) {
            return Ok(p.clone());
        }
        if let Some((prefix, params)) = name.split_once(':') {
            if let Some(f) = self.factories.get(prefix) {
                let p = f(params)?;
                anyhow::ensure!(p.name() == name, "factory for {prefix} built a program named {}", p.name());
                return Ok(p);
            }
        }
        Err(anyhow!("unknown program {name}"))
    }
}
