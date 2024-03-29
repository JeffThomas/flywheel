//!
//! # Flywheel
//!
//! Flywheel is a Rust framework for building scripting languages. It contains a Pratt inspired
//! [Parser](crate::parser::Parser) which builds a [Compiler](crate::compiler::Compiler) tree which
//! will then produce an [Instructions](crate::instruction::Instruction) chain.
//!
//! As an example the expression `3 - 2 + 4` will parse into a [Compiler](crate::compiler::Compiler)
//! tree like so:
//!```text
//!           C(+)
//!          /   \
//!       C(-)  C(4)
//!       /  \
//!     C(3) C(2)
//!```
//!
//! When `C(+).compile(ctx)` is called it will result in an
//! [Instruction](crate::instruction::Instruction) chain like so:
//!
//!```text
//! integer(3)->integer(2)->Isubtract(-)->integer(4)->Iaddition(+)
//!```
//!
//! When executed [Instructions](crate::instruction::Instruction)s return the next Instruction in the
//! chain to be executed, so a simple loop is all that is required to execute a parsed and
//! compiled script.
//!
//! Flywheel's components are:
//!
//! * A Pratt inspired recursive decent parser utilizing [Parslets](crate::parslet::PrefixParslet)
//! which consume [Tokens](lexx::token::Token)s and produce a [Compiler](crate::compiler::Compiler) tree structure
//! * [Compiler](crate::compiler::Compiler)s which will compile down to a chain of [Instructions](crate::instruction::Instruction)
//! * When an [Instruction](crate::instruction::Instruction) is run it returns the next [Instruction](crate::instruction::Instruction) to be run
//!
//! ## Parsing and Compiling
//! Flywheel comes with a couple of simple example implementations of itself which can execute
//! expressions such as `3 * 2 + 4` or `(1 + (2 + 3) * 4 - 5) * -9 / 3 (1 +1) 2*5`. Yes,
//! there are 3 different expressions in that last one, seperated by spaces. Flywheel
//! can handle that.
//!
//! For more details on this process checkout the [Parser](crate::parser::Parser)
//!
//! ## Execution
//! The execution engine need simply call `.run(ctx)` on the first
//! [Instruction](crate::instruction::Instruction), which returns
//! the next [Instruction](crate::instruction::Instruction) to be run and so on. The engine need
//! know nothing about what the [Instructions](crate::instruction::Instruction) do. Flywheel comes
//! with some very simple execution engines in the samples and an execution context with nothing
//! but an Integer stack in it. Executing the above example would look like this
//!
//! ```text
//! Step 1
//! integer(3).run(ctx) -> Some(integer(2))
//! 3 was inserted into the stack, Some(integer(2)) is returned
//! // ctx.stack = [3]
//!
//! Step 2
//! integer(2).run(ctx) -> Some(multiply(*))
//! 2 was pushed into the stack, Some(multiply(*)) is returned
//! // ctx.stack = [2,3]
//!
//! Step 3
//! multiply(-).run(ctx) -> Some(integer(4))
//! 3 and 2 were pulled out, subtracted and the results pushed into the stack, Some(integer(4)) is returned
//! // ctx.stack = [1]
//!
//! Step 4
//! integer(4).run(ctx) -> Some(addition(+))
//! 4 was pushed into the stack, Some(addition(+)) is returned
//! // ctx.stack = [4,1]
//!
//! Step 5
//! addition(+).run(ctx) -> None
//! 1 and 4 were pulled out, added and the results pushed into the stack, None is returned
//! // ctx.stack = [5]
//!```
//!
//! # Dependencies
//!
//! Rust uses the Lexx string tokenizer.
//!
//! # USE
//!
//! Flywheel is not intended to be used as-is or as a library. Instead it's meant to
//! be Forked and modified to suit whatever need you wish.
//!
//! # Examples
//!
//!```
#![doc = include_str!("../examples/minimal.rs")]
//!```
//!
//! ## Branching?
//! Branching is handled
//! by forking the chain and having the branching [Instructions](crate::instruction::Instruction) return whichever
//! [Instructions](crate::instruction::Instruction) is appropriate. The [Instructions](crate::instruction::Instruction) chain looking something like:
//!
//! ```text
//! I(rand)->I(if)->I('yes')->I('is decided')
//!               \>I('no')/
//!```
//!
//! ``I(if)`` will return either ``I('yes')`` or ``I('no')`` depending on how it
//! interoperates the results of ``I(rand)``
//!
//!```
#![doc = include_str!("../examples/branching.rs")]
//!```


pub mod compiler;
pub mod parser;
pub mod parslet;
pub mod instruction;