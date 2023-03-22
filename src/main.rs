//!
//! # Flywheel
//!
//! Flywheel is a framework for writing scripting languages in Rust. It contains a Pratt inspired
//! [Parser](crate::parser::Parser) which builds compilers which will then produces instructions:
//!
//! * A Pratt inspired recursive decent parser utilizing [Parslets](crate::parslet::PrefixParslet)
//! which consume [Tokens](crate::lexx::token::Token) and produce a [Compiler](crate::compiler::Compiler) tree structure
//! * [Compiler](crate::compiler::Compiler)s which will compile down to a chain of [Instructions](crate::instruction::Instruction)
//! * When an [Instruction](crate::instruction::Instruction) is run it returns the next [Instruction](crate::instruction::Instruction) to be run
//!
//! ## Parsing and Compiling
//!
//! Flywheel comes with a couple of simple implementations of itself which can execute
//! expressions such as `3 * 2 + 4` or `(1 + (2 + 3) * 4 - 5) * 9 / 3 (1 +1) 2*5`. Yes,
//! there are 3 different expressions in that last one, seperated by spaces. Flywheel
//! can handle that.
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
//! For more details on this process checkout the [Parser](crate::parser::Parser)
//!
//! When `C(+).compile(ctx)` is called it will result in an
//! [Instruction](crate::instruction::Instruction) chain like so:
//!
//! ```text
//! Iinteger(3)->Iinteger(2)->Isubtract(-)->Iinteger(4)->Iaddition(+)
//!```
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
//! Iinteger(3).run(ctx) -> Some(Iinteger(2))
//! 3 was inserted into the stack, Some(Iinteger(2)) is returned
//! // ctx.stack = [3]
//!
//! Step 2
//! Iintger(2).run(ctx) -> Some(Imultiply(*))
//! 2 was pushed into the stack, Some(Imultiply(*)) is returned
//! // ctx.stack = [2,3]
//!
//! Step 3
//! Imultiply(-).run(ctx) -> Some(Iinteger(4))
//! 3 and 2 were pulled out, subtracted and the results pushed into the stack, Some(Iinteger(4)) is returned
//! // ctx.stack = [1]
//!
//! Step 4
//! Iintger(4).run(ctx) -> Some(Iaddition(+))
//! 4 was pushed into the stack, Some(Iaddition(+)) is returned
//! // ctx.stack = [4,1]
//!
//! Step 5
//! Iaddition(+).run(ctx) -> None
//! 1 and 4 were pulled out, added and the results pushed into the stack, None is returned
//! // ctx.stack = [5]
//!```
//!
//! ## Branching?
//! While there isn't (currently) an example it is expected that branching is handled
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
//! ```
//! # use compiler::{CompileContext, Compiler};
//! # use crate::instruction::{
//! #    AddInstruction, DivideInstruction, ExecutionContext, Instruction, MultiplyInstruction,
//! #    StaticIntInstruction, SubtractInstruction,
//! # };
//! # use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
//! # use crate::parslet::{InfixParslet, PrefixParslet};
//! # use crate::{make_infix_compiler, make_infix_compiler_function, make_prefix_compiler};
//! # use lexx::input::InputString;
//! # use lexx::matcher_integer::IntegerMatcher;
//! # use lexx::matcher_symbol::SymbolMatcher;
//! # use lexx::matcher_whitespace::WhitespaceMatcher;
//! # use lexx::token::TOKEN_TYPE_INTEGER;
//! # use lexx::token::{Token, TOKEN_TYPE_SYMBOL};
//! # use lexx::Lexx;
//! # use std::error::Error;
//!
//! // A simple static integer instruction which is created with the integer it's representing. When
//! // it is executed it simply pushes this value into `ctx.stack` and return the next instruction.
//! pub struct SimpleStaticIntInstruction {
//!     // the integer value we represent
//!     pub value: i32,
//!     // the next Instruction to be executed after this one
//!     pub next: Option<Box<dyn Instruction>>,
//! }
//! impl Instruction for SimpleStaticIntInstruction {
//!     // `execute` is the only function an Instruction has
//!     fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
//!         // the insert happens here
//!         ctx.stack.push(self.value);
//!         // return the next Instruction
//!         Ok(self.next.as_ref())
//!     }
//! }
//!
//! // A very simple math instruction which only does addition and subtraction. Note that is
//! // is not ideal since it has to check which instruction it is each time it executes. The
//! // more complex example creates individual Instructions for each math function, which will
//! // execute faster.
//! pub struct SimpleMathInstruction {
//!     // which math function are we
//!     pub instruction: char,
//!     // the next Instruction in the chain
//!     pub next: Option<Box<dyn Instruction>>,
//! }
//! impl Instruction for SimpleMathInstruction {
//!     fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
//!         // pull the values we're acting on from the stack.
//!         // NOTE: The order is important, 2 - 3 is not the same as 3 - 2
//!         // fortunately the compiler will always provide consistent results
//!         let right = ctx.stack.pop().unwrap();
//!         let left = ctx.stack.pop().unwrap();
//!         // perform the action and push the results into the stack
//!         match self.instruction {
//!             '+' => { ctx.stack.push(left + right); }
//!             '-' => { ctx.stack.push(left - right); }
//!             _   => {}
//!         }
//!         // return the next Instruction
//!         Ok(self.next.as_ref())
//!     }
//! }
//!
//! // The Pratt parser pattern only has two kinds of Parslets, Prefix and Infix. Items that
//! // stand alone, such as a simple number, are considered Prefix Parslets that don't consume
//! // any right hand components.
//! let simple_int_parslet = PrefixParslet {
//!     // the `matcher` function lets the Parser know that this Parslet will consume this token.
//!     // if `matcher` returns `true` then the `generator` function will be called
//!     matcher: |_ctx, token| {
//!         if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
//!     },
//!     // the `generator` function creates a Compiler from this Parslet
//!     generator: |_ctx, token| {
//!         Ok(Some(Box::new(Compiler {
//!             // because this is a static integer, it is a Leaf node in the Compiler tree
//!             // that will be generated. We don't need to worry about the `left`, `right` or
//!             // `next` fields. We also aren't using the `compiler_type` which can be used for
//!             // pre-compile directives or optimizations
//!             left: None, right: None, next: None, compiler_type: 0,
//!             // when compiling knowing what Token created this compiler can be useful
//!             token: token.clone(),
//!             // the actual `compile` function which generates an Instruction
//!             compile: |_ctx: &mut CompileContext, compiler: &Compiler, next: Option<Box<dyn Instruction>>| {
//!                 // simply makes a `SimpleStaticIntInstruction`
//!                 Ok(Some(Box::new(SimpleStaticIntInstruction
//!                 {
//!                     value: compiler.token.value.parse::<i32>().unwrap(),
//!                     next
//!                 })))
//!             }})
//!         ))
//!     }
//! };
//!
//! // The InfixParslet is a bit more complex. It typically gets handed the previously parsed
//! // Token in the form of an already created Compiler for it's left element, and then it
//! // recursively parses the next Token(s) to get it's right hand component
//! let simple_operator_parslet = InfixParslet {
//!     // InfixParslets also have Precedence which insure the orders of operation are followed
//!     // For an in-depth look at how they work check the docs for the Parser
//!     precedence: PRECEDENCE_PRODUCT,
//!     matcher: |_ctx, token, precedence| {
//!         if precedence < PRECEDENCE_PRODUCT
//!             && token.token_type == TOKEN_TYPE_SYMBOL {true} else {false}
//!     },
//!     generator: |ctx, token, left, precedence| {
//!         let right = Parser::parse(ctx, left, precedence)?;
//!         Ok(Some(Box::new(Compiler {
//!             next: None, compiler_type: 0,
//!             left: left.as_ref().map(|l:&Box<Compiler>|{l.clone()}),
//!             right: right.map(|r:Box<Compiler>|{r}),
//!             token: token.clone(),
//!             compile: |ctx: &mut CompileContext, compiler: &Compiler, next: Option<Box<dyn Instruction>>| {
//!                 let i = Box::new(
//!                     SimpleMathInstruction {
//!                         instruction: compiler.token.value.chars().next().unwrap(),
//!                         next
//!                     } );
//!                 let r = (compiler.right.as_ref().unwrap().compile)(ctx, compiler.right.as_ref().unwrap(), Some(i))?;
//!                 let l = (compiler.left.as_ref().unwrap().compile)(ctx, compiler.left.as_ref().unwrap(), r)?;
//!                 Ok(Some(l.unwrap()))
//!             }
//!         })))
//!     }
//! };
//!
//! let lexx = Box::new(Lexx::<512>::new(
//!     Box::new(InputString::new(String::from("3 + 2".to_string()))),
//!     vec![
//!         Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
//!         Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
//!         Box::new(SymbolMatcher { index: 0, precedence: 0, running: true }),
//!     ],
//! ));
//!
//! let mut simple_parse_context: ParseContext = ParseContext {
//!     lexx: lexx,
//!     prefix: vec![
//!         simple_int_parslet,
//!     ],
//!     infix: vec![
//!         simple_operator_parslet,
//!     ],
//!     script: "test.txt".to_string(),
//! };
//!
//! simple_parse_context.lexx.set_input(Box::new(InputString::new(String::from("3 - 2 + 4".to_string()))));
//!
//! let parse_result = Parser::parse(&mut simple_parse_context, &None, 0);
//!
//! let compiler = parse_result.unwrap().unwrap();
//! let compile_result = (compiler.compile)(&mut CompileContext{}, &compiler, None);
//!
//!
//! let mut ctx = ExecutionContext{
//!     stack: Vec::new()
//! };
//!
//! let binding = compile_result.unwrap().unwrap();
//! let mut running_instruction: Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> = Ok(Some(&binding));
//!
//! loop {
//!     match running_instruction {
//!         Ok(Some(i)) => {
//!             running_instruction = i.execute(&mut ctx);
//!         }
//!         Ok(None) => {
//!             break;
//!         }
//!         Err(_) => {
//!             break;
//!         }
//!     }
//! }
//!
//! assert_eq!(ctx.stack.pop(), Some(5));
//!
//! ```

use std::alloc::alloc;

use lexx::Lexxer;

use crate::compiler::CompileError;
use crate::instruction::ExecutionContext;

pub mod compiler;
pub mod instruction;
pub mod parser;
pub mod parslet;

pub const TOKEN_TYPE_OPERATOR: u16 = 20;

fn main() {
    println!("Hello, world!");

    use compiler::{CompileContext, Compiler};
    use crate::instruction::Instruction;
    use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
    use crate::parslet::{InfixParslet, PrefixParslet};
    use lexx::input::InputString;
    use lexx::matcher_integer::IntegerMatcher;
    use lexx::matcher_symbol::SymbolMatcher;
    use lexx::matcher_whitespace::WhitespaceMatcher;
    use lexx::token::TOKEN_TYPE_INTEGER;
    use lexx::token::{Token, TOKEN_TYPE_SYMBOL};
    use lexx::Lexx;
    use std::error::Error;

    /// The Pratt parser pattern only has two kinds of Parslets, Prefix and Infix. Items that
    /// stand alone, such as a simple number, are considered Prefix Parslets that don't consume
    /// any right hand components. This is about as simple as a Paarslet gets
    let simple_int_parslet = PrefixParslet {
        // the `matcher` function evaluates a token and decides if this parslet will parse it
        // if `matcher` returns `true` then the `generator` function will be called to do the parsing
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        // the `generator` function creates a Compiler from this Parslet
        generator: |_ctx, token| {
            // all we need to do is create the compiler that will build the Instruction
            Ok(Some(Box::new(CompilerInt {
                // the next link in our compiler chain, not used in this example
                next: None,
                /// this can be used to identify this kind of compiler, useful for optimizing compilers
                /// or for downcasting which may be demonstrated in a test.
                compiler_type: 0,
                // the token holds the value of the integer that was parsed
                // when compiling we'll turn this string into an actual integer value
                token: token.clone(),
            })))
        }
    };

    /// A [Compiler](crate::compiler::Compiler) for making the Int [Instructions](crate::instruction::Instruction)
    /// the parser above will make this compiler and this compiler will make the integer instruction
    /// below. This is about as simple as compilers can be.
    pub struct CompilerInt {
        /// for chained expressions, this is the chain link
        pub next: Option<Box<dyn Compiler>>,
        /// this will hold what the integer is, such as "4" or "100"
        pub token: Token,
        /// this can be used to identify this kind of compiler, useful for optimizing compilers
        /// or for downcasting which may be demonstrated in a test.
        pub compiler_type: u8,
    }
    impl Compiler for CompilerInt {
        fn compile(
            &self,
            // The context can be used for state information during a compile, it's not
            // used in this example
            _ctx: &mut CompileContext,
            // the next instruction is used to build the instruction chain, it will contain
            // the next instruction that is to be executed after this one, this is important
            // because Instructions are immutable
            next: Option<Box<dyn Instruction>>,
        ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
            // because this is a static integer, it is a Leaf node in the Compiler tree
            // that will be generated. We don't need to worry about the `left`, `right` or
            // `next` fields. We also aren't using the `compiler_type` which can be used for
            // pre-compile directives or optimizations
            Ok(Some(Box::new(StaticIntInstruction {
                value: self.token.value.parse::<i32>().unwrap(),
                next,
            })))
        }

        /// utility methods that aren't used in this example
        fn get_type(&self) -> u8 {
            self.compiler_type
        }
        fn get_token(&self) -> Token {
            self.token.clone()
        }
        fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
        fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

        /// complexities with the Clone trait make it undesirable to mix in with
        /// [Compiler](crate::compiler::Compiler), so it's done the old-fashioned way.
        fn clone_this(&self) -> Box<dyn Compiler> {
            Box::new(CompilerInt {
                next: None,
                token: self.token.clone(),
                compiler_type: self.compiler_type,
            })
        }
    }

    /// A simple static integer instruction. When it is executed it simply pushes this value into
    /// `ctx.stack` and return the next instruction.
    pub struct StaticIntInstruction {
        /// the integer value we represent
        pub value: i32,
        /// the next Instruction to be executed after this one
        pub next: Option<Box<dyn Instruction>>,
    }
    impl Instruction for StaticIntInstruction {
        /// `execute` is the only function an Instruction has
        fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
            // the insert happens here
            ctx.stack.push(self.value);
            // return the next Instruction
            Ok(self.next.as_ref())
        }
    }


    /// The InfixParslet which is used to parse operators such as '+' is a bit more complex.
    /// It typically gets handed the previously parsed Token in the form of an already created
    /// Compiler for it's left hand element, and then it recursively parses the next Token
    /// to get it's right hand component.
    let simple_operator_parslet = InfixParslet {
        // InfixParslets also have Precedence which insure the orders of operation are followed
        // For an in-depth look at how they work check the docs for the Parser
        precedence: PRECEDENCE_PRODUCT,
        // the `matcher` function evaluates a token and decides if this parslet will parse it
        // in this case it needs to take the precedence of any previous infix parslets into
        // consideration. Again, for an in-depth look at how precedence works check the Parser
        // if `matcher` returns `true` then the `generator` function will be called to do the parsing
        matcher: |_ctx, token, precedence| {
            if precedence < PRECEDENCE_PRODUCT
                && token.token_type == TOKEN_TYPE_SYMBOL {true} else {false}
        },
        // the `generator` function creates a Compiler from this Parslet
        // the 'left' parameter here would represent the left hand componant, or the '1' in the
        // expression '1 + 5'.
        generator: |ctx, token, left, precedence| {
            // parse the next 'right' hand token for this operator. that would be the compiler for
            // '5' in the expression '1 + 5'. Note that both the right hand component or the left
            // one might be more complex, for example the left hand might be an expression of its
            // own such as in '1 + 5 + 4 + 2' in which case our right hand component will be
            // a compiler tree representing `5 + 4 + 2`, but we don't have to worry about that,
            // the details are taken care of for us.
            let right = Parser::parse(ctx, left, precedence)?;
            // now build our compiler
            Ok(Some(Box::new(CompilerAddSubtract {
                next: None,
                compiler_type: 0,
                left: left.as_ref().map(|l|{l.clone_this()}),
                right: right.map(|r:Box<dyn Compiler>|{r}),
                token: token.clone(),
            })))
        }
    };

    /// A [Compiler](crate::compiler::Compiler) for making the math [Instructions](crate::instruction::Instruction).
    /// because this is an infix compiler it's a bit more complicated, it needs to keep track of and
    /// compile it's left and right hand components as well as itself.
    pub struct CompilerAddSubtract {
        /// for chained expressions, this is the chain link
        pub next: Option<Box<dyn Compiler>>,
        /// the left hand component of this infix
        pub left: Option<Box<dyn Compiler>>,
        /// the right hand component of this infix
        pub right: Option<Box<dyn Compiler>>,
        /// the math expression this represents
        pub token: Token,
        /// this can be used to identify this kind of compiler, useful for optimizing compilers
        /// or for downcasting which may be demonstrated later on.
        pub compiler_type: u8,
    }
    impl Compiler for CompilerAddSubtract {
        fn compile(
            &self,
            ctx: &mut CompileContext,
            next: Option<Box<dyn Instruction>>,
        ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
            // the end results we want is a chain of instructions that look like
            // left->right->math->next->...
            // because we want these instances to be immutable we want to create them
            // with the linked one already existing: math, then right, then left
            // build the math instruction with the next instruction.
            let m = Box::new(
                MathInstruction {
                    instruction: self.token.value.chars().next().unwrap(),
                    next
                } );
            // build the right instruction with the math instruction
            let r = self.right.as_ref().unwrap().compile(ctx, Some(m))?;
            // build the left instruction with the left right instruction
            let l = self.left.as_ref().unwrap().compile(ctx, r)?;
            Ok(Some(l.unwrap()))
        }
        fn get_type(&self) -> u8 {
            self.compiler_type
        }
        fn get_token(&self) -> Token {
            self.token.clone()
        }
        fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
        fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

        fn clone_this(&self) -> Box<dyn Compiler> {
            Box::new(CompilerAddSubtract {
                next: None,
                left: self.left.as_ref().map(|oc| {oc.clone_this()}),
                right: self.right.as_ref().map(|oc| {oc.clone_this()}),
                token: self.token.clone(),
                compiler_type: self.compiler_type,
            })
        }

    }

    /// A very simple math instruction which only does addition and subtraction. Note that is
    /// is not ideal since it has to check which instruction it is each time it executes. The
    /// more complex example creates individual [Instructions](crate::instruction::Instruction)
    /// for each math function, which will execute faster.
    pub struct MathInstruction {
        /// which math function are we
        pub instruction: char,
        /// the next Instruction in the chain
        pub next: Option<Box<dyn Instruction>>,
    }
    impl Instruction for MathInstruction {
        fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
            // pull the values we're acting on from the stack.
            // NOTE: The order is important, 2 - 3 is not the same as 3 - 2
            // fortunately the compiler will always provide consistent results
            let right = ctx.stack.pop().unwrap();
            let left = ctx.stack.pop().unwrap();
            // perform the action and push the results into the stack
            match self.instruction {
                '+' => { ctx.stack.push(left + right); }
                '-' => { ctx.stack.push(left - right); }
                _   => {}
            }
            // return the next Instruction
            Ok(self.next.as_ref())
        }
    }

    let lexx = Box::new(Lexx::<512>::new(
        Box::new(InputString::new(String::from("3 + 2".to_string()))),
        vec![
            Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
            Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
            Box::new(SymbolMatcher { index: 0, precedence: 0, running: true }),
        ],
    ));

    let mut simple_parse_context: ParseContext = ParseContext {
        lexx: lexx,
        prefix: vec![
            simple_int_parslet,
        ],
        infix: vec![
            simple_operator_parslet,
        ],
        script_name: "test.txt".to_string(),
    };

    simple_parse_context.lexx.set_input(Box::new(InputString::new(String::from("3 - 2 + 4".to_string()))));

    let parse_result = Parser::parse(&mut simple_parse_context, &None, 0);

    let compiler = parse_result.unwrap().unwrap();
    let compile_result = compiler.compile(&mut CompileContext{}, None);


    let mut ctx = ExecutionContext{
        stack: Vec::new()
    };

    let binding = compile_result.unwrap().unwrap();
    let mut running_instruction: Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> = Ok(Some(&binding));

    loop {
        match running_instruction {
            Ok(Some(i)) => {
                running_instruction = i.execute(&mut ctx);
            }
            Ok(None) => {
                break;
            }
            Err(_) => {
                break;
            }
        }
    }

    assert_eq!(ctx.stack.pop(), Some(5));
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use lexx::input::InputString;
    use lexx::Lexx;
    use lexx::matcher_exact::ExactMatcher;
    use lexx::matcher_integer::IntegerMatcher;
    use lexx::matcher_symbol::SymbolMatcher;
    use lexx::matcher_whitespace::WhitespaceMatcher;
    use lexx::token::{Token, TOKEN_TYPE_INTEGER, TOKEN_TYPE_SYMBOL};

    use crate::TOKEN_TYPE_OPERATOR;
    use crate::compiler::{CompileContext, CompileError, Compiler};
    use crate::instruction::{ExecutionContext, Instruction};
    use crate::parser::{ParseContext, Parser, PRECEDENCE_EOE, PRECEDENCE_PREFIX, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
    use crate::parslet::{InfixParslet, PrefixParslet};

    #[test]
    fn math_test() {

        /// A simple static integer instruction which is created with the integer it's representing. When
        /// it is executed it simply pushes this value into `ctx.stack` and return the next instruction.
        pub struct StaticIntInstruction {
            /// the integer value we represent
            pub value: i32,
            /// the next Instruction to be executed after this one
            pub next: Option<Box<dyn Instruction>>,
        }
        impl Instruction for StaticIntInstruction {
            /// `execute` is the only function an Instruction has
            fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                /// the insert happens here
                ctx.stack.push(self.value);
                /// return the next Instruction
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
        pub struct NegateInstruction {
            pub next: Option<Box<dyn Instruction>>,
        }
        impl Instruction for NegateInstruction {
            fn execute(
                &self,
                ctx: &mut ExecutionContext,
            ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                let right = ctx.stack.pop().unwrap();
                ctx.stack.push(-right);
                Ok(self.next.as_ref())
            }
        }


        let int_parslet = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
            },
            generator: |_ctx, token| {
                Ok(Some(Box::new(IntCompiler {
                    next: None,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };

        pub struct IntCompiler {
            pub next: Option<Box<dyn Compiler>>,
            pub token: Token,
            pub compiler_type: u8,
        }
        impl Compiler for IntCompiler {
            fn compile(
                &self,
                ctx: &mut CompileContext,
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                let n = match self.next {
                    Some(ref n) => {n.compile(ctx, next)?}
                    None => {next}
                };
                Ok(Some(Box::new(StaticIntInstruction {
                    value: self.token.value.parse::<i32>().unwrap(),
                    next: n,
                })))
            }
            fn get_type(&self) -> u8 { self.compiler_type }
            fn get_token(&self) -> Token { self.token.clone() }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(IntCompiler {
                    next: self.next.as_ref().map(|oc| {oc.clone_this()}),
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }
        }

        pub struct NegateCompiler {
            pub right: Option<Box<dyn Compiler>>,
            pub next: Option<Box<dyn Compiler>>,
            pub token: Token,
            pub compiler_type: u8,
        }
        impl Compiler for NegateCompiler {
            fn compile(
                &self,
                ctx: &mut CompileContext,
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                let n = match self.next {
                    Some(ref n) => {n.compile(ctx, next)?}
                    None => {next}
                };
                let i = Box::new(NegateInstruction {
                    next: n,
                });
                let r = self.right.as_ref().unwrap().compile(ctx, Some(i))?;
                Ok(Some(r.unwrap()))
            }
            fn get_type(&self) -> u8 { self.compiler_type }
            fn get_token(&self) -> Token { self.token.clone() }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(NegateCompiler {
                    right: self.right.as_ref().map(|oc| {oc.clone_this()}),
                    next: self.next.as_ref().map(|oc| {oc.clone_this()}),
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }
        }

        let negate_parslet = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_OPERATOR
                    && "-" == token.value { true } else { false }},
            generator: |ctx, token| {
                let right = Parser::parse(ctx, &None, PRECEDENCE_PREFIX)?;
                Ok(Some(Box::new(NegateCompiler {
                    right,
                    next: None,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };

        pub struct MathCompiler {
            pub next: Option<Box<dyn Compiler>>,
            pub left: Option<Box<dyn Compiler>>,
            pub right: Option<Box<dyn Compiler>>,
            pub token: Token,
            pub compiler_type: u8,
        }
        impl Compiler for MathCompiler {
            fn compile(
                &self,
                ctx: &mut CompileContext,
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                let n = match self.next {
                    Some(ref n) => {n.compile(ctx, next)?}
                    None => {next}
                };
                let i: Box<dyn Instruction> = match self.token.value.as_str() {
                    "+" => { Box::new(AddInstruction { next: n } ) }
                    "-" => { Box::new(SubtractInstruction { next: n } ) }
                    "*" => { Box::new(MultiplyInstruction { next: n } ) }
                    "/" => { Box::new(DivideInstruction { next: n } ) }
                    _ => { Box::new(AddInstruction { next: n } ) } // this can (should) not happen
                };
                let r = self.right.as_ref().unwrap().compile(ctx, Some(i))?;
                let l = self.left.as_ref().unwrap().compile(ctx, r)?;
                Ok(l)
            }
            fn get_type(&self) -> u8 { self.compiler_type }
            fn get_token(&self) -> Token { self.token.clone() }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(MathCompiler {
                    next: self.next.as_ref().map(|oc| {oc.clone_this()}),
                    left: self.left.as_ref().map(|oc| {oc.clone_this()}),
                    right: self.right.as_ref().map(|oc| {oc.clone_this()}),
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }
        }
        let div_operator = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "/" == token.value { true } else { false }},
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(Some(Box::new(MathCompiler {
                    left: left.as_ref().map(|l| l.clone_this()),
                    right,
                    next: None,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };
        let mult_operator = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "*" == token.value { true } else { false }},
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(Some(Box::new(MathCompiler {
                    left: left.as_ref().map(|l| l.clone_this()),
                    right,
                    next: None,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };
        let plus_operator = InfixParslet {
            precedence: PRECEDENCE_SUM,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_SUM
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "+" == token.value { true } else { false }},
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(Some(Box::new(MathCompiler {
                    left: left.as_ref().map(|l| l.clone_this()),
                    right,
                    next: None,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };
        let minus_operator = InfixParslet {
            precedence: PRECEDENCE_SUM,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_SUM
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "-" == token.value { true } else { false }},
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(Some(Box::new(MathCompiler {
                    left: left.as_ref().map(|l| l.clone_this()),
                    right,
                    next: None,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };

        let eoe_parslet = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_OPERATOR
                    && ";" == token.value { true } else { false }},
            generator: |ctx, token| {
                Parser::parse(ctx, &None, 0)
            },
        };

        pub struct ScriptCompiler {
            pub next: Option<Box<dyn Compiler>>,
            pub token: Token,
            pub compiler_type: u8,
        }
        impl Compiler for ScriptCompiler {
            fn compile(
                &self,
                ctx: &mut CompileContext,
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                match self.next {
                    Some(ref n) => { n.compile(ctx, None) }
                    None => { Ok(next) }
                }
            }
            fn get_type(&self) -> u8 { self.compiler_type }
            fn get_token(&self) -> Token { self.token.clone() }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }
            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(ScriptCompiler {
                    next: self.next.as_ref().map(|c|{c.clone_this()}),
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }
        }

        let script_parser = PrefixParslet {
            matcher: |_ctx, _token| true,
            generator: |ctx, token| {
                let next = PrefixParslet::chain_parse(ctx)?;
                Ok(Some(Box::new(ScriptCompiler {
                    next,
                    token: token.clone(),
                    compiler_type: 0,
                })))
            },
        };

        let sub_parser = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_OPERATOR && "(" == token.value {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, _token| {
                return PrefixParslet::chain_parse_until_token(
                    ctx,
                    &Token {
                        value: ")".to_string(),
                        token_type: TOKEN_TYPE_OPERATOR,
                        len: 0,
                        line: 0,
                        column: 0,
                        precedence: 0,
                    },
                );
            },
        };

        let mut parse_context: ParseContext = ParseContext {
            lexx: Box::new(Lexx::<512>::new(
                Box::new(InputString::new(String::from("".to_string()))),
                vec![
                    Box::new(IntegerMatcher { index: 0, precedence: 0, running: true, }),
                    Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true, }),
                    Box::new(ExactMatcher::build_exact_matcher(
                        vec!["+", "-", "*", "/", "(", ")", ";"],
                        TOKEN_TYPE_OPERATOR,
                        1,
                    )),
                ],
            )),
            prefix: vec![
                negate_parslet,
                int_parslet,
                sub_parser,
                eoe_parslet
            ],
            infix: vec![
                plus_operator,
                minus_operator,
                mult_operator,
                div_operator
            ],
            script_name: "test.txt".to_string(),
        };

        let token = Token {
            value: "".to_string(),
            token_type: 0,
            len: 0,
            line: 0,
            column: 0,
            precedence: 0,
        };

        parse_context
            .lexx
            .set_input(Box::new(InputString::new(String::from(
                "(1 + (2 + 3) * 4 - -5) * 9 / 3; (1 +1) 2*5; -7+6".to_string(),
            ))));

        let result = script_parser.parse(&mut parse_context, &token, &None, 0);

        let compiler = result.unwrap().unwrap();
        let compile_result = compiler.compile(&mut CompileContext {}, None);

        let mut ctx = ExecutionContext { stack: Vec::new() };

        let binding = compile_result.unwrap().unwrap();
        let mut running_instruction: Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> =
            Ok(Some(&binding));

        loop {
            match running_instruction {
                Ok(Some(i)) => {
                    running_instruction = i.execute(&mut ctx);
                }
                Ok(None) => {
                    break;
                }
                Err(_) => {
                    break;
                }
            }
        }

        assert_eq!(ctx.stack.pop(), Some(-1));
        assert_eq!(ctx.stack.pop(), Some(10));
        assert_eq!(ctx.stack.pop(), Some(2));
        assert_eq!(ctx.stack.pop(), Some(78));
    }






    #[test]
    fn branching_test() {
        use crate::compiler::{CompileContext, Compiler};
        use crate::instruction::Instruction;
        use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
        use crate::parslet::{InfixParslet, PrefixParslet};
        use lexx::input::InputString;
        use lexx::matcher_integer::IntegerMatcher;
        use lexx::matcher_symbol::SymbolMatcher;
        use lexx::matcher_whitespace::WhitespaceMatcher;
        use lexx::token::TOKEN_TYPE_INTEGER;
        use lexx::token::{Token, TOKEN_TYPE_SYMBOL};
        use lexx::Lexx;
        use std::error::Error;

        /// The Pratt parser pattern only has two kinds of Parslets, Prefix and Infix. Items that
        /// stand alone, such as a simple number, are considered Prefix Parslets that don't consume
        /// any right hand components. This is about as simple as a Paarslet gets
        let simple_int_parslet = PrefixParslet {
            // the `matcher` function evaluates a token and decides if this parslet will parse it
            // if `matcher` returns `true` then the `generator` function will be called to do the parsing
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
            },
            // the `generator` function creates a Compiler from this Parslet
            generator: |_ctx, token| {
                // all we need to do is create the compiler that will build the Instruction
                Ok(Some(Box::new(CompilerInt {
                    // the next link in our compiler chain, not used in this example
                    next: None,
                    /// this can be used to identify this kind of compiler, useful for optimizing compilers
                    /// or for downcasting which may be demonstrated in a test.
                    compiler_type: 0,
                    // the token holds the value of the integer that was parsed
                    // when compiling we'll turn this string into an actual integer value
                    token: token.clone(),
                })))
            }
        };

        /// A [Compiler](crate::compiler::Compiler) for making the Int [Instructions](crate::instruction::Instruction)
        /// the parser above will make this compiler and this compiler will make the integer instruction
        /// below. This is about as simple as compilers can be.
        pub struct CompilerInt {
            /// for chained expressions, this is the chain link
            pub next: Option<Box<dyn Compiler>>,
            /// this will hold what the integer is, such as "4" or "100"
            pub token: Token,
            /// this can be used to identify this kind of compiler, useful for optimizing compilers
            /// or for downcasting which may be demonstrated in a test.
            pub compiler_type: u8,
        }
        impl Compiler for CompilerInt {
            fn compile(
                &self,
                // The context can be used for state information during a compile, it's not
                // used in this example
                _ctx: &mut CompileContext,
                // the next instruction is used to build the instruction chain, it will contain
                // the next instruction that is to be executed after this one, this is important
                // because Instructions are immutable
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                // because this is a static integer, it is a Leaf node in the Compiler tree
                // that will be generated. We don't need to worry about the `left`, `right` or
                // `next` fields. We also aren't using the `compiler_type` which can be used for
                // pre-compile directives or optimizations
                Ok(Some(Box::new(StaticIntInstruction {
                    value: self.token.value.parse::<i32>().unwrap(),
                    next,
                })))
            }

            /// utility methods that aren't used in this example
            fn get_type(&self) -> u8 {
                self.compiler_type
            }
            fn get_token(&self) -> Token {
                self.token.clone()
            }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

            /// complexities with the Clone trait make it undesirable to mix in with
            /// [Compiler](crate::compiler::Compiler), so it's done the old-fashioned way.
            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(CompilerInt {
                    next: None,
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }
        }

        /// A simple static integer instruction. When it is executed it simply pushes this value into
        /// `ctx.stack` and return the next instruction.
        pub struct StaticIntInstruction {
            /// the integer value we represent
            pub value: i32,
            /// the next Instruction to be executed after this one
            pub next: Option<Box<dyn Instruction>>,
        }
        impl Instruction for StaticIntInstruction {
            /// `execute` is the only function an Instruction has
            fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                // the insert happens here
                ctx.stack.push(self.value);
                // return the next Instruction
                Ok(self.next.as_ref())
            }
        }


        /// The InfixParslet which is used to parse operators such as '+' is a bit more complex.
        /// It typically gets handed the previously parsed Token in the form of an already created
        /// Compiler for it's left hand element, and then it recursively parses the next Token
        /// to get it's right hand component.
        let simple_operator_parslet = InfixParslet {
            // InfixParslets also have Precedence which insure the orders of operation are followed
            // For an in-depth look at how they work check the docs for the Parser
            precedence: PRECEDENCE_PRODUCT,
            // the `matcher` function evaluates a token and decides if this parslet will parse it
            // in this case it needs to take the precedence of any previous infix parslets into
            // consideration. Again, for an in-depth look at how precedence works check the Parser
            // if `matcher` returns `true` then the `generator` function will be called to do the parsing
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_SYMBOL {true} else {false}
            },
            // the `generator` function creates a Compiler from this Parslet
            // the 'left' parameter here would represent the left hand componant, or the '1' in the
            // expression '1 + 5'.
            generator: |ctx, token, left, precedence| {
                // parse the next 'right' hand token for this operator. that would be the compiler for
                // '5' in the expression '1 + 5'. Note that both the right hand component or the left
                // one might be more complex, for example the left hand might be an expression of its
                // own such as in '1 + 5 + 4 + 2' in which case our right hand component will be
                // a compiler tree representing `5 + 4 + 2`, but we don't have to worry about that,
                // the details are taken care of for us.
                let right = Parser::parse(ctx, left, precedence)?;
                // now build our compiler
                Ok(Some(Box::new(CompilerAddSubtract {
                    next: None,
                    compiler_type: 0,
                    left: left.as_ref().map(|l|{l.clone_this()}),
                    right: right.map(|r:Box<dyn Compiler>|{r}),
                    token: token.clone(),
                })))
            }
        };

        /// A [Compiler](crate::compiler::Compiler) for making the math [Instructions](crate::instruction::Instruction).
        /// because this is an infix compiler it's a bit more complicated, it needs to keep track of and
        /// compile it's left and right hand components as well as itself.
        pub struct CompilerAddSubtract {
            /// for chained expressions, this is the chain link
            pub next: Option<Box<dyn Compiler>>,
            /// the left hand component of this infix
            pub left: Option<Box<dyn Compiler>>,
            /// the right hand component of this infix
            pub right: Option<Box<dyn Compiler>>,
            /// the math expression this represents
            pub token: Token,
            /// this can be used to identify this kind of compiler, useful for optimizing compilers
            /// or for downcasting which may be demonstrated later on.
            pub compiler_type: u8,
        }
        impl Compiler for CompilerAddSubtract {
            fn compile(
                &self,
                ctx: &mut CompileContext,
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                // the end results we want is a chain of instructions that look like
                // left->right->math->next->...
                // because we want these instances to be immutable we want to create them
                // with the linked one already existing: math, then right, then left
                // build the math instruction with the next instruction.
                let m = Box::new(
                    MathInstruction {
                        instruction: self.token.value.chars().next().unwrap(),
                        next
                    } );
                // build the right instruction with the math instruction
                let r = self.right.as_ref().unwrap().compile(ctx, Some(m))?;
                // build the left instruction with the left right instruction
                let l = self.left.as_ref().unwrap().compile(ctx, r)?;
                Ok(Some(l.unwrap()))
            }
            fn get_type(&self) -> u8 {
                self.compiler_type
            }
            fn get_token(&self) -> Token {
                self.token.clone()
            }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(CompilerAddSubtract {
                    next: None,
                    left: self.left.as_ref().map(|oc| {oc.clone_this()}),
                    right: self.right.as_ref().map(|oc| {oc.clone_this()}),
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }

        }

        /// A very simple math instruction which only does addition and subtraction. Note that is
        /// is not ideal since it has to check which instruction it is each time it executes. The
        /// more complex example creates individual [Instructions](crate::instruction::Instruction)
        /// for each math function, which will execute faster.
        pub struct MathInstruction {
            /// which math function are we
            pub instruction: char,
            /// the next Instruction in the chain
            pub next: Option<Box<dyn Instruction>>,
        }
        impl Instruction for MathInstruction {
            fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                // pull the values we're acting on from the stack.
                // NOTE: The order is important, 2 - 3 is not the same as 3 - 2
                // fortunately the compiler will always provide consistent results
                let right = ctx.stack.pop().unwrap();
                let left = ctx.stack.pop().unwrap();
                // perform the action and push the results into the stack
                match self.instruction {
                    '+' => { ctx.stack.push(left + right); }
                    '-' => { ctx.stack.push(left - right); }
                    _   => {}
                }
                // return the next Instruction
                Ok(self.next.as_ref())
            }
        }



        /// The InfixParslet which is used to parse operators such as '+' is a bit more complex.
        /// It typically gets handed the previously parsed Token in the form of an already created
        /// Compiler for it's left hand element, and then it recursively parses the next Token
        /// to get it's right hand component.
        let simple_branching_parslet = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_SYMBOL {true} else {false}
            },

            generator: |ctx, token, left, precedence| {
                let then_branch = Parser::parse(ctx, left, precedence)?;
                let else_branch = Parser::parse(ctx, left, precedence)?;
                // now build our compiler
                Ok(Some(Box::new(CompilerBranching {
                    next: None,
                    compiler_type: 0,
                    if_expression: left.as_ref().map(|l|{l.clone_this()}),
                    then_branch: then_branch.map(|r:Box<dyn Compiler>|{r}),
                    else_branch: else_branch.map(|r:Box<dyn Compiler>|{r}),
                    token: token.clone(),
                })))
            }
        };

        /// A [Compiler](crate::compiler::Compiler) for making the math [Instructions](crate::instruction::Instruction).
        /// because this is an infix compiler it's a bit more complicated, it needs to keep track of and
        /// compile it's left and right hand components as well as itself.
        pub struct CompilerBranching {
            /// for chained expressions, this is the chain link
            pub next: Option<Box<dyn Compiler>>,
            /// the left hand component of this infix
            pub if_expression: Option<Box<dyn Compiler>>,
            /// the if component of this infix
            pub then_branch: Option<Box<dyn Compiler>>,
            /// the else component of this infix
            pub else_branch: Option<Box<dyn Compiler>>,
            /// the math expression this represents
            pub token: Token,
            /// this can be used to identify this kind of compiler, useful for optimizing compilers
            /// or for downcasting which may be demonstrated later on.
            pub compiler_type: u8,
        }
        impl Compiler for CompilerBranching {
            fn compile(
                &self,
                ctx: &mut CompileContext,
                next: Option<Box<dyn Instruction>>,
            ) -> Result<Option<Box<dyn Instruction>>, CompileError> {
                let mut ibrn: Option<Box<dyn Instruction>> = None;
                let mut tbrn: Option<Box<dyn Instruction>> = None;
                if next.is_some() {
                    let next_ptr = Box::into_raw(next.unwrap());
                    ibrn = Some(unsafe { Box::from_raw(next_ptr) });
                    tbrn = Some(unsafe { Box::from_raw(next_ptr) });
                }
                let tb = self.then_branch.as_ref().unwrap().compile(ctx, ibrn)?;
                let eb = self.else_branch.as_ref().unwrap().compile(ctx, tbrn)?;
                let bi = Box::new(
                    BranchingInstruction {
                        instruction: self.token.value.chars().next().unwrap(),
                        then_branch: tb,
                        else_branch: eb
                    } );
                let if_expression = self.if_expression.as_ref().unwrap().compile(ctx, Some(bi))?;
                Ok(Some(if_expression.unwrap()))
            }
            fn get_type(&self) -> u8 {
                self.compiler_type
            }
            fn get_token(&self) -> Token {
                self.token.clone()
            }
            fn get_next(&self) -> Option<Box<dyn Compiler>> { self.next.as_ref().map(|c|{c.clone_this()}) }
            fn set_next(&mut self, next: Option<Box<dyn Compiler>>) { self.next = next }

            fn clone_this(&self) -> Box<dyn Compiler> {
                Box::new(CompilerBranching {
                    next: None,
                    if_expression: self.if_expression.as_ref().map(|oc| {oc.clone_this()}),
                    then_branch: self.then_branch.as_ref().map(|oc| {oc.clone_this()}),
                    else_branch: self.else_branch.as_ref().map(|oc| {oc.clone_this()}),
                    token: self.token.clone(),
                    compiler_type: self.compiler_type,
                })
            }

        }

        /// A very simple math instruction which only does addition and subtraction. Note that is
        /// is not ideal since it has to check which instruction it is each time it executes. The
        /// more complex example creates individual [Instructions](crate::instruction::Instruction)
        /// for each math function, which will execute faster.
        pub struct BranchingInstruction {
            /// which math function are we
            pub instruction: char,
            pub then_branch: Option<Box<dyn Instruction>>,
            pub else_branch: Option<Box<dyn Instruction>>,
        }
        impl Instruction for BranchingInstruction {
            fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                // pull the values we're acting on from the stack.
                // NOTE: The order is important, 2 - 3 is not the same as 3 - 2
                // fortunately the compiler will always provide consistent results
                let left = ctx.stack.pop().unwrap();
                if left == 0 {
                    return Ok(self.then_branch.as_ref())
                }
                // return the next Instruction
                Ok(self.else_branch.as_ref())
            }
        }


        let lexx = Box::new(Lexx::<512>::new(
            Box::new(InputString::new(String::from("3 + 2".to_string()))),
            vec![
                Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
                Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
                Box::new(SymbolMatcher { index: 0, precedence: 0, running: true }),
            ],
        ));

        let mut simple_parse_context: ParseContext = ParseContext {
            lexx: lexx,
            prefix: vec![
                simple_int_parslet,
            ],
            infix: vec![
                simple_operator_parslet,
            ],
            script_name: "test.txt".to_string(),
        };

        simple_parse_context.lexx.set_input(Box::new(InputString::new(String::from("3 - 2 + 4".to_string()))));

        let parse_result = Parser::parse(&mut simple_parse_context, &None, 0);

        let compiler = parse_result.unwrap().unwrap();
        let compile_result = compiler.compile(&mut CompileContext{}, None);


        let mut ctx = ExecutionContext{
            stack: Vec::new()
        };

        let binding = compile_result.unwrap().unwrap();
        let mut running_instruction: Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> = Ok(Some(&binding));

        loop {
            match running_instruction {
                Ok(Some(i)) => {
                    running_instruction = i.execute(&mut ctx);
                }
                Ok(None) => {
                    break;
                }
                Err(_) => {
                    break;
                }
            }
        }

        assert_eq!(ctx.stack.pop(), Some(5));
    }
    //
    // #[test]
    // fn complex_math_test() {
    //     let script_parser = PrefixParslet {
    //         matcher: |_ctx, _token| true,
    //         generator: |ctx, token| {
    //             let next = PrefixParslet::chain_parse(ctx)?;
    //             Ok(Some(Box::new(Compiler {
    //                 left: None,
    //                 right: None,
    //                 next: next,
    //                 token: token.clone(),
    //                 compiler_type: 0,
    //                 compile: |ctx: &mut CompileContext,
    //                           compiler: &Compiler,
    //                           _next: Option<Box<dyn Instruction>>| {
    //                     match &compiler.next {
    //                         None => Ok(None),
    //                         Some(c) => Ok(Compiler::fold_left_compile(ctx, Some(c.clone()))?),
    //                     }
    //                 },
    //             })))
    //         },
    //     };
    //
    //     let div_operator = InfixParslet {
    //         precedence: PRECEDENCE_PRODUCT,
    //         matcher: |_ctx, token, precedence| {
    //             if precedence < PRECEDENCE_PRODUCT
    //                 && token.token_type == TOKEN_TYPE_SYMBOL
    //                 && "/" == token.value
    //             {
    //                 true
    //             } else {
    //                 false
    //             }
    //         },
    //         generator: |ctx, token, left, precedence| {
    //             let right = Parser::parse(ctx, left, precedence)?;
    //             Ok(make_infix_compiler!(
    //                 0,
    //                 token,
    //                 left,
    //                 right,
    //                 make_infix_compiler_function!(DivideInstruction)
    //             ))
    //         },
    //     };
    //     let minus_operator = InfixParslet {
    //         precedence: PRECEDENCE_SUM,
    //         matcher: |_ctx, token, precedence| {
    //             if precedence < PRECEDENCE_SUM
    //                 && token.token_type == TOKEN_TYPE_SYMBOL
    //                 && "-" == token.value
    //             {
    //                 true
    //             } else {
    //                 false
    //             }
    //         },
    //         generator: |ctx, token, left, precedence| {
    //             let right = Parser::parse(ctx, left, precedence)?;
    //             Ok(make_infix_compiler!(
    //                 0,
    //                 token,
    //                 left,
    //                 right,
    //                 make_infix_compiler_function!(SubtractInstruction)
    //             ))
    //         },
    //     };
    //     let mult_operator = InfixParslet {
    //         precedence: PRECEDENCE_PRODUCT,
    //         matcher: |_ctx, token, precedence| {
    //             if precedence < PRECEDENCE_PRODUCT
    //                 && token.token_type == TOKEN_TYPE_SYMBOL
    //                 && "*" == token.value
    //             {
    //                 true
    //             } else {
    //                 false
    //             }
    //         },
    //         generator: |ctx, token, left, precedence| {
    //             let right = Parser::parse(ctx, left, precedence)?;
    //             Ok(make_infix_compiler!(
    //                 0,
    //                 token,
    //                 left,
    //                 right,
    //                 make_infix_compiler_function!(MultiplyInstruction)
    //             ))
    //         },
    //     };
    //     let plus_operator = InfixParslet {
    //         precedence: PRECEDENCE_SUM,
    //         matcher: |_ctx, token, precedence| {
    //             if precedence < PRECEDENCE_SUM
    //                 && token.token_type == TOKEN_TYPE_SYMBOL
    //                 && "+" == token.value
    //             {
    //                 true
    //             } else {
    //                 false
    //             }
    //         },
    //         generator: |ctx, token, left, precedence| {
    //             let right = Parser::parse(ctx, left, precedence)?;
    //             Ok(make_infix_compiler!(
    //                 0,
    //                 token,
    //                 left,
    //                 right,
    //                 make_infix_compiler_function!(AddInstruction)
    //             ))
    //         },
    //     };
    //
    //     let int_parslet = PrefixParslet {
    //         matcher: |_ctx, token| {
    //             if token.token_type == TOKEN_TYPE_INTEGER {
    //                 true
    //             } else {
    //                 false
    //             }
    //         },
    //         generator: |_ctx, token| {
    //             Ok(make_prefix_compiler!(
    //                 0,
    //                 token,
    //                 |_ctx: &mut CompileContext,
    //                  compiler: &Compiler,
    //                  next: Option<Box<dyn Instruction>>| {
    //                     Ok(Some(Box::new(StaticIntInstruction {
    //                         value: compiler.token.value.parse::<i32>().unwrap(),
    //                         next,
    //                     })))
    //                 }
    //             ))
    //         },
    //     };
    //
    //     let mut parse_context: ParseContext = ParseContext {
    //         lexx: Box::new(Lexx::<512>::new(
    //             Box::new(InputString::new(String::from("3+2".to_string()))),
    //             vec![
    //                 Box::new(IntegerMatcher {
    //                     index: 0,
    //                     precedence: 0,
    //                     running: true,
    //                 }),
    //                 Box::new(WhitespaceMatcher {
    //                     index: 0,
    //                     column: 0,
    //                     line: 0,
    //                     precedence: 0,
    //                     running: true,
    //                 }),
    //                 Box::new(SymbolMatcher {
    //                     index: 0,
    //                     precedence: 0,
    //                     running: true,
    //                 }),
    //             ],
    //         )),
    //         prefix: vec![int_parslet],
    //         infix: vec![plus_operator, minus_operator, mult_operator, div_operator],
    //         script: "test.txt".to_string(),
    //     };
    //
    //     let token = Token {
    //         value: "".to_string(),
    //         token_type: 0,
    //         len: 0,
    //         line: 0,
    //         column: 0,
    //         precedence: 0,
    //     };
    //
    //     parse_context
    //         .lexx
    //         .set_input(Box::new(InputString::new(String::from(
    //             "2 + 3 * 4 - 5 * 9 / 3 1 +1 2*5".to_string(),
    //         ))));
    //
    //     let result2 = script_parser.parse(&mut parse_context, &token, &None, 0); //Parser::parse(&mut parse_context, &None, 0);
    //
    //     let compiler = result2.unwrap().unwrap();
    //     let compile_result = (compiler.compile)(&mut CompileContext {}, &compiler, None);
    //
    //     let mut ctx = ExecutionContext { stack: Vec::new() };
    //
    //     let mut instruction = compile_result
    //         .as_ref()
    //         .unwrap()
    //         .as_ref()
    //         .unwrap()
    //         .execute(&mut ctx);
    //     loop {
    //         match instruction {
    //             Ok(Some(i)) => {
    //                 instruction = i.execute(&mut ctx);
    //             }
    //             Ok(None) => {
    //                 break;
    //             }
    //             Err(_) => {
    //                 break;
    //             }
    //         }
    //     }
    //
    //     assert_eq!(ctx.stack.pop(), Some(10));
    //     assert_eq!(ctx.stack.pop(), Some(2));
    //     assert_eq!(ctx.stack.pop(), Some(-1));
    // }
}
