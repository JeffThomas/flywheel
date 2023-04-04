use std::error::Error;
use std::sync::Arc;

///The [ExecutionContext](ExecutionContext) stores state information for
/// an executing script. In our instance we just store aa stack of integers, a more complex
/// scripting language would use this object to store call stacks, namespaces, heaps etc. etc.
pub struct ExecutionContext {
    pub stack: Vec<i32>,
}

pub trait Instruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>>;
}
