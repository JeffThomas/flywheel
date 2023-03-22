use lexx::token::Token;

use crate::instruction::Instruction;

pub struct CompileContext {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompileError {
    Error(String),
}

pub trait Compiler: {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Box<dyn Instruction>>,
    ) -> Result<Option<Box<dyn Instruction>>, CompileError>;
    fn get_type(&self) -> u8;
    fn get_token(&self) -> Token;
    fn get_next(&self) -> Option<Box<dyn Compiler>>;
    fn set_next(&mut self, next: Option<Box<dyn Compiler>>);

    fn clone_this(&self) -> Box<dyn Compiler>;
}
