use std::cell::RefCell;
use std::error::Error;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use lexx::token::Token;

use crate::instruction::Instruction;

pub struct CompileContext {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompileError {
    Error(String),
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CompileError::Error(m) => write!(f, "{}", m),
        }
    }
}

impl Error for CompileError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        match *self {
            CompileError::Error(..) => "a compile error occurred",
        }
    }
}

pub trait Compiler: {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Arc<dyn Instruction>>,
    ) -> Result<Option<Arc<dyn Instruction>>, CompileError>;
    fn get_type(&self) -> u8;
    fn get_token(&self) -> Token;
}


pub struct EmptyExpressionCompiler {
    pub next: Option<Rc<RefCell<dyn Compiler>>>,
    pub expression: Option<Rc<RefCell<dyn Compiler>>>,
    pub token: Token,
    pub compiler_type: u8,
}
impl Compiler for EmptyExpressionCompiler {
    fn compile(
        &self,
        _ctx: &mut CompileContext,
        _next: Option<Arc<dyn Instruction>>,
    ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
        Ok(None)
    }
    fn get_type(&self) -> u8 { self.compiler_type }
    fn get_token(&self) -> Token { self.token.clone() }
}

pub struct ExpressionCompiler {
    pub next: Option<Rc<RefCell<dyn Compiler>>>,
    pub expression: Option<Rc<RefCell<dyn Compiler>>>,
    pub token: Token,
    pub compiler_type: u8,
}
impl Compiler for ExpressionCompiler {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Arc<dyn Instruction>>,
    ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
        let n = match self.next {
            Some(ref n) => {n.borrow().compile(ctx, next)?}
            None => {next}
        };
        match &self.expression {
            None => {
                Ok(None)
            }
            Some(e) => {
                Ok(e.as_ref().borrow().compile(ctx, n)?)
            }
        }
    }
    fn get_type(&self) -> u8 { self.compiler_type }
    fn get_token(&self) -> Token { self.token.clone() }
}