use lexx::token::Token;

use crate::instruction::{Instruction, StaticIntInstruction};

pub struct CompileContext {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompileError {
    Error(String),
}

pub trait Compiler {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Box<dyn Instruction>>,
    ) -> Result<Option<Box<dyn Instruction>>, CompileError>;
    fn get_type(&self) -> u8;
    fn get_token(&self) -> Token;
}

pub struct CompilerInt {
    pub next: Option<Box<dyn Compiler>>,
    pub token: Token,
    pub compiler_type: u8,
}

impl Compiler for CompilerInt {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Box<dyn Instruction>>,
    ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
        Ok(Some(Box::new(StaticIntInstruction {
            value: self.token.value.parse::<i32>().unwrap(),
            next,
        })))
    }
    fn get_type(&self) -> u8 {
        self.compiler_type
    }
    fn get_token(&self) -> Token {
        self.token.clone()
    }
}

#[derive(Clone)]
pub struct CompilerStruct {
    pub left: Option<Box<CompilerStruct>>,
    pub right: Option<Box<CompilerStruct>>,
    pub next: Option<Box<CompilerStruct>>,
    pub token: Token,
    pub compiler_type: u8,
    pub compile: fn(
        ctx: &mut CompileContext,
        compiler: &CompilerStruct,
        next: Option<Box<dyn Instruction>>,
    ) -> Result<Option<Box<dyn Instruction>>, CompileError>,
}

impl CompilerStruct {
    pub fn fold_left_compile(
        ctx: &mut CompileContext,
        compiler: Option<Box<CompilerStruct>>,
    ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
        match compiler {
            None => Ok(None),
            Some(c) => {
                let next = CompilerStruct::fold_left_compile(ctx, c.next.clone())?;
                (c.compile)(ctx, &c, next)
            }
        }
    }
}

#[macro_export]
macro_rules! make_prefix_compiler {
    ( $c_type:expr, $token:expr, $compiler:expr ) => {
        Some(Box::new(CompilerStruct {
            left: None,
            right: None,
            next: None,
            token: $token.clone(),
            compiler_type: $c_type,
            compile: $compiler,
        }))
    };
}

#[macro_export]
macro_rules! make_infix_compiler_function {
    ( $instruction:ident ) => {
        |ctx: &mut CompileContext, compiler: &CompilerStruct, next: Option<Box<dyn Instruction>>| {
            let i = Box::new($instruction { next });
            let r = (compiler.right.as_ref().unwrap().compile)(
                ctx,
                compiler.right.as_ref().unwrap(),
                Some(i),
            )?;
            let l =
                (compiler.left.as_ref().unwrap().compile)(ctx, compiler.left.as_ref().unwrap(), r)?;
            Ok(Some(l.unwrap()))
        }
    };
}

#[macro_export]
macro_rules! make_infix_compiler {
    ( $c_type:expr, $token:expr, $left:expr, $right:expr, $compiler:expr ) => {
        Some(Box::new(CompilerStruct {
            left: $left.as_ref().map(|l: &Box<CompilerStruct>| l.clone()),
            right: $right.map(|r: Box<CompilerStruct>| r),
            next: None,
            token: $token.clone(),
            compiler_type: $c_type,
            compile: $compiler,
        }))
    };
}
