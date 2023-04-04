use std::cell::RefCell;
use std::error::Error;
use std::rc::Rc;
use std::sync::Arc;

use lexx::input::InputString;
use lexx::Lexx;
use lexx::matcher_integer::IntegerMatcher;
use lexx::matcher_symbol::SymbolMatcher;
use lexx::matcher_whitespace::WhitespaceMatcher;
use lexx::token::{Token, TOKEN_TYPE_SYMBOL};
use lexx::token::TOKEN_TYPE_INTEGER;

use flywheel::compiler::{CompileContext, CompileError, Compiler};
use flywheel::instruction::{ExecutionContext, Instruction};
use flywheel::parser::{ParseContext, Parser, PRECEDENCE_PRODUCT};
use flywheel::parslet::{InfixParslet, PrefixParslet};

fn main() {
    // parslet for parsing a static integer
    let simple_int_parslet = PrefixParslet {
        // the `matcher` function evaluates a token and decides if this parslet will parse it
        // if `matcher` returns `true` then the `generator` function will be called to do the parsing
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        // the `generator` function creates a Compiler based on the Token
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(IntCompiler {
                token: token.clone(),
                compiler_type: 0,
            }))))
        }
    };

    pub struct IntCompiler {
        // this will hold what the integer is, such as "4" or "100"
        pub token: Token,
        // this can be used to identify this kind of compiler, useful for optimizing compilers
        // or for downcasting which may be demonstrated in a test.
        pub compiler_type: u8,
    }
    impl Compiler for IntCompiler {
        fn compile(
            &self,
            _ctx: &mut CompileContext,
            next: Option<Arc<dyn Instruction>>,
        ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
            Ok(Some(Arc::new(StaticIntInstruction {
                value: self.token.value.parse::<i32>().unwrap(),
                next,
            })))
        }
        fn get_type(&self) -> u8 { self.compiler_type }
        fn get_token(&self) -> Token { self.token.clone() }
    }

    pub struct StaticIntInstruction {
        pub value: i32,
        pub next: Option<Arc<dyn Instruction>>,
    }
    impl Instruction for StaticIntInstruction {
        fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
            // the insert happens here
            ctx.stack.push(self.value);
            // return the next Instruction
            Ok(self.next.clone())
        }
    }

    // The InfixParslet which is used to parse operators such as '+' is a bit more complex.
    // It typically gets handed the previously parsed Token in the form of an already created
    // Compiler for it's left hand element, and then it recursively parses the next Token
    // to get it's right hand component.
    let simple_operator_parslet = InfixParslet {
        // InfixParslets also have Precedence which insure the orders of operation are followed
        // For an in-depth look at how they work check the docs for the Parser
        precedence: PRECEDENCE_PRODUCT,
        matcher: |_ctx, token, precedence| {
            if precedence < PRECEDENCE_PRODUCT
                && token.token_type == TOKEN_TYPE_SYMBOL { true } else { false }
        },
        // the 'left' parameter here would represent the left hand component, or the '1' in the
        // expression '1 + 5'.
        generator: |ctx, token, left, precedence| {
            // parse the next 'right' hand token for this operator. that would be the compiler for
            // '5' in the expression '1 + 5'. Note that both the right hand component or the left
            // one might be more complex, for example the left hand might be an expression of its
            // own such as in '1 + 5 + 4 + 2' in which case our right hand component will be
            // a compiler tree representing `5 + 4 + 2`, but we don't have to worry about that,
            // the details are taken care of for us.
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(AddSubtractCompiler {
                compiler_type: 0,
                left: left.as_ref().map(|l| { l.clone() }),
                right: right.map(|r: Rc<RefCell<dyn Compiler>>| { r }),
                token: token.clone(),
            }))))
        }
    };

    // because this is an infix compiler it's a bit more complicated, it needs to keep track of and
    // compile it's left and right hand components as well as itself.
    pub struct AddSubtractCompiler {
        // the left hand component of this infix
        pub left: Option<Rc<RefCell<dyn Compiler>>>,
        // the right hand component of this infix
        pub right: Option<Rc<RefCell<dyn Compiler>>>,
        pub token: Token,
        pub compiler_type: u8,
    }
    impl Compiler for AddSubtractCompiler {
        fn compile(
            &self,
            ctx: &mut CompileContext,
            next: Option<Arc<dyn Instruction>>,
        ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
            // the end results we want is a chain of instructions that look like
            // left->right->math->next->...
            // because instructions are are immutable we have to create them
            // with the next one already existing: math, then right, then left

            // build the math instruction with the next instruction.
            let m = Arc::new(
                MathInstruction {
                    instruction: self.token.value.chars().next().unwrap(),
                    next
                });
            // build the right instruction with the math instruction
            let r = self.right.as_ref().unwrap().borrow().compile(ctx, Some(m))?;
            // build the left instruction with the left right instruction
            let l = self.left.as_ref().unwrap().borrow().compile(ctx, r)?;
            Ok(Some(l.unwrap()))
        }
        fn get_type(&self) -> u8 { self.compiler_type }
        fn get_token(&self) -> Token { self.token.clone() }
    }

    // A very simple math instruction which only does addition and subtraction. Note that is
    // is not ideal since it has to check which instruction it is each time it executes. The
    // compiler could make a unique instruction for each operation, which the main.rc code does.
    pub struct MathInstruction {
        pub instruction: char,
        pub next: Option<Arc<dyn Instruction>>,
    }
    impl Instruction for MathInstruction {
        fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
            // pull the values we're acting on from the stack.
            // NOTE: The order is important, 2 - 3 is not the same as 3 - 2
            let right = ctx.stack.pop().unwrap();
            let left = ctx.stack.pop().unwrap();
            // perform the action and push the results into the stack
            match self.instruction {
                '+' => { ctx.stack.push(left + right); }
                '-' => { ctx.stack.push(left - right); }
                _ => {}
            }
            // return the next Instruction
            Ok(self.next.clone())
        }
    }

    // The tokenizer
    let lexx = Box::new(Lexx::<512>::new(
        Box::new(InputString::new(String::from("".to_string()))),
        vec![
            Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
            Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
            Box::new(SymbolMatcher { index: 0, precedence: 0, running: true }),
        ],
    ));

    // ParseContext holds the parser state
    let mut simple_parse_context: ParseContext = ParseContext {
        lexx: lexx,
        // This contains all of the PrefixParslets to use
        prefix: vec![
            simple_int_parslet,
        ],
        // This would contain all of the PrefixParslets to use
        infix: vec![
            simple_operator_parslet,
        ],
        script_name: "test.txt".to_string(),
    };

    // set the text we want to parse
    simple_parse_context.lexx.set_input(Box::new(InputString::new(String::from("3 - 2 + 4".to_string()))));

    // do the parsing
    let parse_result = Parser::parse(&mut simple_parse_context, &None, 0);

    if parse_result.is_err() {
        println!("Parse failed: `{}`", parse_result.err().unwrap().to_string());
        return;
    }

    // compile the result of the parsing
    let compiler = parse_result.unwrap().unwrap();
    let compile_result = compiler.borrow().compile(&mut CompileContext {}, None);

    if compile_result.is_err() {
        println!("Compile failed: `{}`", compile_result.err().unwrap());
        return;
    }

    // ExecutionContext stores state information for an executing script.
    let mut ctx = ExecutionContext {
        stack: Vec::new()
    };

    // To start the execution loop we want the first instruction to be the same type as the results
    // of an `Instruction.execute()` call, it almost is except the current Results error is of
    // type CompileError instead of generic Box<dyn Error>> so we unwrap and rewrap it.
    let binding = compile_result.unwrap();
    let mut running_instruction: Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> = Ok(binding);

    // This is the execution loop. Pretty simple: call execute on the results of calling
    // execute until the results is None or Error. In a real scripting language this is where
    // thread management and debugging functionality would exist, as well as some actual error
    // handling.
    loop {
        match running_instruction {
            Ok(Some(i)) => {
                running_instruction = i.execute(&mut ctx);
            }
            Ok(None) => {
                break;
            }
            Err(e) => {
                println!("Execution failed: `{}`", e);
                break;
            }
        }
    }

// Validate the results, which will be left on the stack by the last instruction
    assert_eq!(ctx.stack.pop(), Some(5));
}