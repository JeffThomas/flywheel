use std::cell::RefCell;
use std::error::Error;
use std::rc::Rc;
use std::sync::Arc;

use lexx::input::InputString;
use lexx::Lexx;
use lexx::matcher_integer::IntegerMatcher;
use lexx::matcher_whitespace::WhitespaceMatcher;
use lexx::token::Token;
use lexx::token::TOKEN_TYPE_INTEGER;

use flywheel::compiler::{CompileContext, CompileError, Compiler};
use flywheel::instruction::{ExecutionContext, Instruction};
use flywheel::parser::{ParseContext, Parser};
use flywheel::parslet::PrefixParslet;

fn main() {
    // parslet for parsing a static integer
    let simple_int_parslet = PrefixParslet {
        // the `matcher` function evaluates a token and decides if this parslet will parse it
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        // the `generator` function creates a Compiler based on the Token
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(IntCompiler {
                token: token.clone(),
                next: None,
                compiler_type: 0,
            }))))
        }
    };

    pub struct IntCompiler {
        pub next: Option<Rc<RefCell<dyn Compiler>>>,
        pub token: Token,
        pub compiler_type: u8,
    }
    impl Compiler for IntCompiler {
        fn compile(
            &self,
            _ctx: &mut CompileContext,
            next: Option<Arc<dyn Instruction>>,
        ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
            let value = self.token.value.parse::<i32>();
            if value.is_err() {
                return Err(CompileError::Error(format!("Error parsing integer '{}'", self.token.value)));
            }
            Ok(Some(Arc::new(StaticIntInstruction {
                value: value.unwrap(),
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
            // just push our value into the stack
            ctx.stack.push(self.value);
            // return the next Instruction
            Ok(self.next.clone())
        }
    }

    // The tokenizer
    let lexx = Box::new(Lexx::<512>::new(
        // we can set the actual text to parse later
        Box::new(InputString::new(String::from("".to_string()))),
        vec![
            Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
            Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
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
        infix: vec![],
        script_name: "test.txt".to_string(),
    };

    // set the text we want to parse
    simple_parse_context.lexx.set_input(Box::new(InputString::new(String::from("3".to_string()))));

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

    // Execute our instruction, it returns the next instruction which is `Ok(None)` in this case
    let results = compile_result.unwrap().unwrap().execute(&mut ctx);

    if results.is_err() {
        println!("Execution failed: `{}`", results.err().unwrap());
        return;
    }

    // make sure we're right about there being no more instructions.
    assert_eq!(results.unwrap().is_none(), true);

    // Validate that the instruction pushed the integer value into the stack
    assert_eq!(ctx.stack.pop(), Some(3));
}