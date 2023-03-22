use std::error::Error;
use std::sync::Arc;

pub struct ExecutionContext {
    pub stack: Vec<i32>,
}

pub trait Instruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>>;
}
