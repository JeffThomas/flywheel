use std::error::Error;

pub struct ExecutionContext {
    pub stack: Vec<i32>,
}

pub trait Instruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>>;
}
