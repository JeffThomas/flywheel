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

pub struct StaticIntInstruction {
    pub value: i32,
    pub next: Option<Box<dyn Instruction>>,
}
impl Instruction for StaticIntInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
        ctx.stack.push(self.value);
        Ok(self.next.as_ref())
    }
}

pub struct AddInstruction {
    pub next: Option<Box<dyn Instruction>>,
}
impl Instruction for AddInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left + right);
        Ok(self.next.as_ref())
    }
}
pub struct SubtractInstruction {
    pub next: Option<Box<dyn Instruction>>,
}
impl Instruction for SubtractInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left - right);
        Ok(self.next.as_ref())
    }
}
pub struct MultiplyInstruction {
    pub next: Option<Box<dyn Instruction>>,
}
impl Instruction for MultiplyInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left * right);
        Ok(self.next.as_ref())
    }
}
pub struct DivideInstruction {
    pub next: Option<Box<dyn Instruction>>,
}
impl Instruction for DivideInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left / right);
        Ok(self.next.as_ref())
    }
}
