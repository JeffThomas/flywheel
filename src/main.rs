//!
//! # Flywheel
//!
//! Flywheel is a framework for writing scripting languages in Rust. It contains a Pratt inspired
//! parser which builds compilers which will then produces instructions:
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
//! As an example the expression `3 - 2 + 4` will parse into a [Compiler](crate::compiler::Compiler) tree like so:
//!```text
//!           C(+)
//!          /   \
//!       C(-)  C(4)
//!       /  \
//!     C(3) C(2)
//!```
//!
//! When `C(+).compile(ctx)` is called it will result in an [Instruction](crate::instruction::Instruction) chain like so:
//!
//! ```text
//! Iinteger(3)->Iinteger(2)->Isubtract(-)->Iinteger(4)->Iaddition(+)
//!```
//!
//! ## Execution
//! The execution engine need simply call `.run(ctx)` on the first [Instruction](crate::instruction::Instruction), which returns
//! the next [Instruction](crate::instruction::Instruction) to be run and so on. The engine need know nothing about what the
//! [Instructions](crate::instruction::Instruction) do. Flywheel comes with some very simple execution engines in the samples
//! and an execution context with nothing but an Integer stack in it. Executing the above
//! example would look like this
//!
//! ```text
//! Step 1
//! Iinteger(3).run(ctx) -> Some(Iinteger(2))
//! // 3 was inserted into the stack, Some(Iinteger(2)) is returned
//! // ctx.stack = [3]
//!
//! Step 2
//! Iintger(2).run(ctx) -> Some(Imultiply(*))
//! // 2 was pushed into the stack, Some(Imultiply(*)) is returned
//! // ctx.stack = [2,3]
//!
//! Step 3
//! Imultiply(-).run(ctx) -> Some(Iinteger(4))
//! // 3 and 2 were pulled out, subtracted and the results pushed into the stack, Some(Iinteger(4)) is returned
//! // ctx.stack = [1]
//!
//! Step 4
//! Iintger(4).run(ctx) -> Some(Iaddition(+))
//! // 4 was pushed into the stack, Some(Iaddition(+)) is returned
//! // ctx.stack = [4,1]
//!
//! Step 5
//! Iaddition(+).run(ctx) -> None
//! // 1 and 4 were pulled out, added and the results pushed into the stack, None is returned
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
//! # use compiler::{CompileContext, CompilerStruct};
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
//!         Ok(Some(Box::new(CompilerStruct {
//!             // because this is a static integer, it is a Leaf node in the Compiler tree
//!             // that will be generated. We don't need to worry about the `left`, `right` or
//!             // `next` fields. We also aren't using the `compiler_type` which can be used for
//!             // pre-compile directives or optimizations
//!             left: None, right: None, next: None, compiler_type: 0,
//!             // when compiling knowing what Token created this compiler can be useful
//!             token: token.clone(),
//!             // the actual `compile` function which generates an Instruction
//!             compile: |_ctx: &mut CompileContext, compiler: &CompilerStruct, next: Option<Box<dyn Instruction>>| {
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
//!         Ok(Some(Box::new(CompilerStruct {
//!             next: None, compiler_type: 0,
//!             left: left.as_ref().map(|l:&Box<CompilerStruct>|{l.clone()}),
//!             right: right.map(|r:Box<CompilerStruct>|{r}),
//!             token: token.clone(),
//!             compile: |ctx: &mut CompileContext, compiler: &CompilerStruct, next: Option<Box<dyn Instruction>>| {
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

use lexx::Lexxer;

pub mod compiler;
pub mod instruction;
pub mod parser;
pub mod parslet;

pub const TOKEN_TYPE_OPERATOR: u16 = 20;

fn main() {
    println!("Hello, world!");

    use compiler::{CompileContext, CompilerStruct};
    use crate::instruction::{
        AddInstruction, DivideInstruction, ExecutionContext, Instruction, MultiplyInstruction,
        StaticIntInstruction, SubtractInstruction,
    };
    use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
    use crate::parslet::{InfixParslet, PrefixParslet};
    use crate::{make_infix_compiler, make_infix_compiler_function, make_prefix_compiler};
    use lexx::input::InputString;
    use lexx::matcher_integer::IntegerMatcher;
    use lexx::matcher_symbol::SymbolMatcher;
    use lexx::matcher_whitespace::WhitespaceMatcher;
    use lexx::token::TOKEN_TYPE_INTEGER;
    use lexx::token::{Token, TOKEN_TYPE_SYMBOL};
    use lexx::Lexx;
    use std::error::Error;

    // A simple static integer instruction which is created with the integer it's representing. When
    // it is executed it simply pushes this value into `ctx.stack` and return the next instruction.
    pub struct SimpleStaticIntInstruction {
        // the integer value we represent
        pub value: i32,
        // the next Instruction to be executed after this one
        pub next: Option<Box<dyn Instruction>>,
    }
    impl Instruction for SimpleStaticIntInstruction {
        // `execute` is the only function an Instruction has
        fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
            // the insert happens here
            ctx.stack.push(self.value);
            // return the next Instruction
            Ok(self.next.as_ref())
        }
    }

    // A very simple math instruction which only does addition and subtraction. Note that is
    // is not ideal since it has to check which instruction it is each time it executes. The
    // more complex example creates individual Instructions for each math function, which will
    // execute faster.
    pub struct SimpleMathInstruction {
        // which math function are we
        pub instruction: char,
        // the next Instruction in the chain
        pub next: Option<Box<dyn Instruction>>,
    }
    impl Instruction for SimpleMathInstruction {
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

    // The Pratt parser pattern only has two kinds of Parslets, Prefix and Infix. Items that
    // stand alone, such as a simple number, are considered Prefix Parslets that don't consume
    // any right hand components.
    let simple_int_parslet = PrefixParslet {
        // the `matcher` function lets the Parser know that this Parslet will consume this token.
        // if `matcher` returns `true` then the `generator` function will be called
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        // the `generator` function creates a Compiler from this Parslet
        generator: |_ctx, token| {
            Ok(Some(Box::new(CompilerStruct {
                // because this is a static integer, it is a Leaf node in the Compiler tree
                // that will be generated. We don't need to worry about the `left`, `right` or
                // `next` fields. We also aren't using the `compiler_type` which can be used for
                // pre-compile directives or optimizations
                left: None,
                right: None,
                next: None,
                compiler_type: 0,
                // when compiling knowing what Token created this compiler can be useful
                token: token.clone(),
                // the actual `compile` function which generates an Instruction
                compile: |_ctx: &mut CompileContext, compiler: &CompilerStruct, next: Option<Box<dyn Instruction>>| {
                    // simply makes a `SimpleStaticIntInstruction`
                    Ok(Some(Box::new(SimpleStaticIntInstruction
                    {
                        value: compiler.token.value.parse::<i32>().unwrap(),
                        next
                    })))
                }
            })
            ))
        }
    };

    // The InfixParslet is a bit more complex. It typically gets handed the previously parsed
    // Token in the form of an already created Compiler for it's left element, and then it
    // recursively parses the next Token(s) to get it's right hand component
    let simple_operator_parslet = InfixParslet {
        // InfixParslets also have Precedence which insure the orders of operation are followed
        // For an in-depth look at how they work check the docs for the Parser
        precedence: PRECEDENCE_PRODUCT,
        matcher: |_ctx, token, precedence| {
            if precedence < PRECEDENCE_PRODUCT
                && token.token_type == TOKEN_TYPE_SYMBOL {true} else {false}
        },
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Box::new(CompilerStruct {
                next: None, compiler_type: 0,
                left: left.as_ref().map(|l:&Box<CompilerStruct>|{l.clone()}),
                right: right.map(|r:Box<CompilerStruct>|{r}),
                token: token.clone(),
                compile: |ctx: &mut CompileContext, compiler: &CompilerStruct, next: Option<Box<dyn Instruction>>| {
                    let i = Box::new(
                        SimpleMathInstruction {
                            instruction: compiler.token.value.chars().next().unwrap(),
                            next
                        } );
                    let r = (compiler.right.as_ref().unwrap().compile)(ctx, compiler.right.as_ref().unwrap(), Some(i))?;
                    let l = (compiler.left.as_ref().unwrap().compile)(ctx, compiler.left.as_ref().unwrap(), r)?;
                    Ok(Some(l.unwrap()))
                }
            })))
        }
    };

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
        script: "test.txt".to_string(),
    };

    simple_parse_context.lexx.set_input(Box::new(InputString::new(String::from("3 - 2 + 4".to_string()))));

    let parse_result = Parser::parse(&mut simple_parse_context, &None, 0);

    let compiler = parse_result.unwrap().unwrap();
    let compile_result = (compiler.compile)(&mut CompileContext{}, &compiler, None);


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

    use crate::{
        make_infix_compiler, make_infix_compiler_function, make_prefix_compiler,
        TOKEN_TYPE_OPERATOR,
    };
    use crate::compiler::{CompileContext, CompilerStruct};
    use crate::instruction::{
        AddInstruction, DivideInstruction, ExecutionContext, Instruction, MultiplyInstruction,
        StaticIntInstruction, SubtractInstruction,
    };
    use crate::parser::{ParseContext, Parser, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
    use crate::parslet::{InfixParslet, PrefixParslet};

    #[test]
    fn simple_math_test() {
        pub struct SimpleStaticIntInstruction {
            pub value: i32,
            pub next: Option<Box<dyn Instruction>>,
        }
        impl Instruction for SimpleStaticIntInstruction {
            fn execute(
                &self,
                ctx: &mut ExecutionContext,
            ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                ctx.stack.push(self.value);
                Ok(self.next.as_ref())
            }
        }

        pub struct SimpleMathInstruction {
            pub instruction: char,
            pub next: Option<Box<dyn Instruction>>,
        }
        impl Instruction for SimpleMathInstruction {
            fn execute(
                &self,
                ctx: &mut ExecutionContext,
            ) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
                let right = ctx.stack.pop().unwrap();
                let left = ctx.stack.pop().unwrap();
                match self.instruction {
                    '+' => {
                        ctx.stack.push(left + right);
                    }
                    '-' => {
                        ctx.stack.push(left - right);
                    }
                    _ => {}
                }
                Ok(self.next.as_ref())
            }
        }

        let simple_int_parslet = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_INTEGER {
                    true
                } else {
                    false
                }
            },
            generator: |_ctx, token| {
                Ok(Some(Box::new(CompilerStruct {
                    left: None,
                    right: None,
                    next: None,
                    compiler_type: 0,
                    token: token.clone(),
                    compile: |_ctx: &mut CompileContext,
                              compiler: &CompilerStruct,
                              next: Option<Box<dyn Instruction>>| {
                        Ok(Some(Box::new(SimpleStaticIntInstruction {
                            value: compiler.token.value.parse::<i32>().unwrap(),
                            next,
                        })))
                    },
                })))
            },
        };

        let simple_operator_parslet = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT && token.token_type == TOKEN_TYPE_SYMBOL {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(Some(Box::new(CompilerStruct {
                    next: None,
                    compiler_type: 0,
                    left: left.as_ref().map(|l: &Box<CompilerStruct>| l.clone()),
                    right: right.map(|r: Box<CompilerStruct>| r),
                    token: token.clone(),
                    compile: |ctx: &mut CompileContext,
                              compiler: &CompilerStruct,
                              next: Option<Box<dyn Instruction>>| {
                        let i = Box::new(SimpleMathInstruction {
                            instruction: compiler.token.value.chars().next().unwrap(),
                            next,
                        });
                        let r = (compiler.right.as_ref().unwrap().compile)(
                            ctx,
                            compiler.right.as_ref().unwrap(),
                            Some(i),
                        )?;
                        let l = (compiler.left.as_ref().unwrap().compile)(
                            ctx,
                            compiler.left.as_ref().unwrap(),
                            r,
                        )?;
                        Ok(Some(l.unwrap()))
                    },
                })))
            },
        };

        let lexx = Box::new(Lexx::<512>::new(
            Box::new(InputString::new(String::from("3 + 2".to_string()))),
            vec![
                Box::new(IntegerMatcher {
                    index: 0,
                    precedence: 0,
                    running: true,
                }),
                Box::new(WhitespaceMatcher {
                    index: 0,
                    column: 0,
                    line: 0,
                    precedence: 0,
                    running: true,
                }),
                Box::new(SymbolMatcher {
                    index: 0,
                    precedence: 0,
                    running: true,
                }),
            ],
        ));

        let mut simple_parse_context: ParseContext = ParseContext {
            lexx: lexx,
            prefix: vec![simple_int_parslet],
            infix: vec![simple_operator_parslet],
            script: "test.txt".to_string(),
        };

        simple_parse_context
            .lexx
            .set_input(Box::new(InputString::new(String::from(
                "3 - 2 + 4".to_string(),
            ))));

        let parse_result = Parser::parse(&mut simple_parse_context, &None, 0);

        let compiler = parse_result.unwrap().unwrap();
        let compile_result = (compiler.compile)(&mut CompileContext {}, &compiler, None);

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

        assert_eq!(ctx.stack.pop(), Some(5));
    }

    #[test]
    fn math_test() {
        let script_parser = PrefixParslet {
            matcher: |_ctx, _token| true,
            generator: |ctx, token| {
                let next = PrefixParslet::chain_parse(ctx)?;
                Ok(Some(Box::new(CompilerStruct {
                    left: None,
                    right: None,
                    next: next,
                    token: token.clone(),
                    compiler_type: 0,
                    compile: |ctx: &mut CompileContext,
                              compiler: &CompilerStruct,
                              _next: Option<Box<dyn Instruction>>| {
                        match &compiler.next {
                            None => Ok(None),
                            Some(c) => Ok(CompilerStruct::fold_left_compile(ctx, Some(c.clone()))?),
                        }
                    },
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

        let div_operator = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "/" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(DivideInstruction)
                ))
            },
        };
        let minus_operator = InfixParslet {
            precedence: PRECEDENCE_SUM,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_SUM
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "-" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(SubtractInstruction)
                ))
            },
        };
        let mult_operator = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "*" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(MultiplyInstruction)
                ))
            },
        };
        let plus_operator = InfixParslet {
            precedence: PRECEDENCE_SUM,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_SUM
                    && token.token_type == TOKEN_TYPE_OPERATOR
                    && "+" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(AddInstruction)
                ))
            },
        };

        let int_parslet = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_INTEGER {
                    true
                } else {
                    false
                }
            },
            generator: |_ctx, token| {
                Ok(make_prefix_compiler!(
                    0,
                    token,
                    |_ctx: &mut CompileContext,
                     compiler: &CompilerStruct,
                     next: Option<Box<dyn Instruction>>| {
                        Ok(Some(Box::new(StaticIntInstruction {
                            value: compiler.token.value.parse::<i32>().unwrap(),
                            next,
                        })))
                    }
                ))
            },
        };

        let mut parse_context: ParseContext = ParseContext {
            lexx: Box::new(Lexx::<512>::new(
                Box::new(InputString::new(String::from("3+2".to_string()))),
                vec![
                    Box::new(IntegerMatcher {
                        index: 0,
                        precedence: 0,
                        running: true,
                    }),
                    Box::new(WhitespaceMatcher {
                        index: 0,
                        column: 0,
                        line: 0,
                        precedence: 0,
                        running: true,
                    }),
                    Box::new(ExactMatcher::build_exact_matcher(
                        vec!["+", "-", "*", "/", "(", ")"],
                        TOKEN_TYPE_OPERATOR,
                        1,
                    )),
                ],
            )),
            prefix: vec![int_parslet, sub_parser],
            infix: vec![plus_operator, minus_operator, mult_operator, div_operator],
            script: "test.txt".to_string(),
        };

        let token = Token {
            value: "".to_string(),
            token_type: 0,
            len: 0,
            line: 0,
            column: 0,
            precedence: 0,
        };

        //parse_context.lexx.set_input(Box::new(InputString::new(String::from("(2 + 3) * 4".to_string()))));
        parse_context
            .lexx
            .set_input(Box::new(InputString::new(String::from(
                "(1 + (2 + 3) * 4 - 5) * 9 / 3 (1 +1) 2*5".to_string(),
            ))));

        let result2 = script_parser.parse(&mut parse_context, &token, &None, 0); //Parser::parse(&mut parse_context, &None, 0);

        let compiler = result2.unwrap().unwrap();
        let compile_result = (compiler.compile)(&mut CompileContext {}, &compiler, None);

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

        println!();
        print!("{}", ctx.stack.pop().unwrap());
        while !ctx.stack.is_empty() {
            print!(", {}", ctx.stack.pop().unwrap());
        }
        println!();
    }

    #[test]
    fn complex_math_test() {
        let script_parser = PrefixParslet {
            matcher: |_ctx, _token| true,
            generator: |ctx, token| {
                let next = PrefixParslet::chain_parse(ctx)?;
                Ok(Some(Box::new(CompilerStruct {
                    left: None,
                    right: None,
                    next: next,
                    token: token.clone(),
                    compiler_type: 0,
                    compile: |ctx: &mut CompileContext,
                              compiler: &CompilerStruct,
                              _next: Option<Box<dyn Instruction>>| {
                        match &compiler.next {
                            None => Ok(None),
                            Some(c) => Ok(CompilerStruct::fold_left_compile(ctx, Some(c.clone()))?),
                        }
                    },
                })))
            },
        };

        let div_operator = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_SYMBOL
                    && "/" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(DivideInstruction)
                ))
            },
        };
        let minus_operator = InfixParslet {
            precedence: PRECEDENCE_SUM,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_SUM
                    && token.token_type == TOKEN_TYPE_SYMBOL
                    && "-" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(SubtractInstruction)
                ))
            },
        };
        let mult_operator = InfixParslet {
            precedence: PRECEDENCE_PRODUCT,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_PRODUCT
                    && token.token_type == TOKEN_TYPE_SYMBOL
                    && "*" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(MultiplyInstruction)
                ))
            },
        };
        let plus_operator = InfixParslet {
            precedence: PRECEDENCE_SUM,
            matcher: |_ctx, token, precedence| {
                if precedence < PRECEDENCE_SUM
                    && token.token_type == TOKEN_TYPE_SYMBOL
                    && "+" == token.value
                {
                    true
                } else {
                    false
                }
            },
            generator: |ctx, token, left, precedence| {
                let right = Parser::parse(ctx, left, precedence)?;
                Ok(make_infix_compiler!(
                    0,
                    token,
                    left,
                    right,
                    make_infix_compiler_function!(AddInstruction)
                ))
            },
        };

        let int_parslet = PrefixParslet {
            matcher: |_ctx, token| {
                if token.token_type == TOKEN_TYPE_INTEGER {
                    true
                } else {
                    false
                }
            },
            generator: |_ctx, token| {
                Ok(make_prefix_compiler!(
                    0,
                    token,
                    |_ctx: &mut CompileContext,
                     compiler: &CompilerStruct,
                     next: Option<Box<dyn Instruction>>| {
                        Ok(Some(Box::new(StaticIntInstruction {
                            value: compiler.token.value.parse::<i32>().unwrap(),
                            next,
                        })))
                    }
                ))
            },
        };

        let mut parse_context: ParseContext = ParseContext {
            lexx: Box::new(Lexx::<512>::new(
                Box::new(InputString::new(String::from("3+2".to_string()))),
                vec![
                    Box::new(IntegerMatcher {
                        index: 0,
                        precedence: 0,
                        running: true,
                    }),
                    Box::new(WhitespaceMatcher {
                        index: 0,
                        column: 0,
                        line: 0,
                        precedence: 0,
                        running: true,
                    }),
                    Box::new(SymbolMatcher {
                        index: 0,
                        precedence: 0,
                        running: true,
                    }),
                ],
            )),
            prefix: vec![int_parslet],
            infix: vec![plus_operator, minus_operator, mult_operator, div_operator],
            script: "test.txt".to_string(),
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
                "2 + 3 * 4 - 5 * 9 / 3 1 +1 2*5".to_string(),
            ))));

        let result2 = script_parser.parse(&mut parse_context, &token, &None, 0); //Parser::parse(&mut parse_context, &None, 0);

        let compiler = result2.unwrap().unwrap();
        let compile_result = (compiler.compile)(&mut CompileContext {}, &compiler, None);

        let mut ctx = ExecutionContext { stack: Vec::new() };

        let mut instruction = compile_result
            .as_ref()
            .unwrap()
            .as_ref()
            .unwrap()
            .execute(&mut ctx);
        loop {
            match instruction {
                Ok(Some(i)) => {
                    instruction = i.execute(&mut ctx);
                }
                Ok(None) => {
                    break;
                }
                Err(_) => {
                    break;
                }
            }
        }

        assert_eq!(ctx.stack.pop(), Some(10));
        assert_eq!(ctx.stack.pop(), Some(2));
        assert_eq!(ctx.stack.pop(), Some(-1));
    }
}
