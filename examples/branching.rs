use std::cell::RefCell;
use std::error::Error;
use std::rc::Rc;
use std::sync::Arc;

use lexx::input::InputString;
use lexx::Lexx;
use lexx::matcher_integer::IntegerMatcher;
use lexx::matcher_symbol::SymbolMatcher;
use lexx::matcher_whitespace::WhitespaceMatcher;
use lexx::token::{Token, TOKEN_TYPE_SYMBOL, TOKEN_TYPE_WHITESPACE};
use lexx::token::TOKEN_TYPE_INTEGER;

use flywheel::compiler::{CompileContext, CompileError, Compiler};
use flywheel::eat_token_or_throw_error;
use flywheel::instruction::{ExecutionContext, Instruction};
use flywheel::parser::{ParseContext, ParseError, Parser, PRECEDENCE_CALL};
use flywheel::parslet::{InfixParslet, PrefixParslet};

fn main() {
    let int_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(IntCompiler {
                compiler_type: 0,
                token: token.clone(),
            }))))
        }
    };

    pub struct IntCompiler {
        pub token: Token,
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

    let branching_parslet = InfixParslet {
        precedence: PRECEDENCE_CALL,
        matcher: |_ctx, token, precedence| {
            if precedence < PRECEDENCE_CALL
                && token.token_type == TOKEN_TYPE_SYMBOL
                && token.value == "?" {true} else {false}
        },

        generator: |ctx, token, left, precedence| {
            let then_branch = Parser::parse(ctx, &None, precedence)?;
            eat_token_or_throw_error!(ctx, TOKEN_TYPE_SYMBOL, ":");
            let else_branch = Parser::parse(ctx, &None, precedence)?;
            // now build our compiler
            Ok(Some(Rc::new(RefCell::new(BranchingCompiler {
                compiler_type: 0,
                if_expression: left.as_ref().map(|l|{l.clone()}),
                then_branch: then_branch.map(|r:Rc<RefCell<dyn Compiler>>|{r}),
                else_branch: else_branch.map(|r:Rc<RefCell<dyn Compiler>>|{r}),
                token: token.clone(),
            }))))
        }
    };

    pub struct BranchingCompiler {
        pub if_expression: Option<Rc<RefCell<dyn Compiler>>>,
        pub then_branch: Option<Rc<RefCell<dyn Compiler>>>,
        pub else_branch: Option<Rc<RefCell<dyn Compiler>>>,
        pub token: Token,
        pub compiler_type: u8,
    }
    impl Compiler for BranchingCompiler {
        fn compile(
            &self,
            ctx: &mut CompileContext,
            next: Option<Arc<dyn Instruction>>,
        ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
            let tb = self.then_branch.as_ref().unwrap().borrow().compile(ctx, next.clone())?;
            let eb = self.else_branch.as_ref().unwrap().borrow().compile(ctx, next.clone())?;
            let bi = Arc::new(
                BranchingInstruction {
                    instruction: self.token.value.chars().next().unwrap(),
                    true_branch: tb,
                    false_branch: eb
                } );
            let if_expression = self.if_expression.as_ref().unwrap().borrow().compile(ctx, Some(bi))?;
            Ok(Some(if_expression.unwrap()))
        }
        fn get_type(&self) -> u8 { self.compiler_type }
        fn get_token(&self) -> Token { self.token.clone() }
    }

    pub struct BranchingInstruction {
        pub instruction: char,
        pub true_branch: Option<Arc<dyn Instruction>>,
        pub false_branch: Option<Arc<dyn Instruction>>,
    }
    impl Instruction for BranchingInstruction {
        fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
            let if_results = ctx.stack.pop().unwrap();
            if if_results == 0 {
                return Ok(self.false_branch.clone())
            }
            Ok(self.true_branch.clone())
        }
    }

    let lexx = Box::new(Lexx::<512>::new(
        Box::new(InputString::new(String::from("".to_string()))),
        vec![
            Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
            Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
            Box::new(SymbolMatcher { index: 0, precedence: 0, running: true }),
        ],
    ));

    let mut pctx: ParseContext = ParseContext {
        lexx: lexx,
        prefix: vec![
            int_parslet,
        ],
        infix: vec![
            branching_parslet,
        ],
        script_name: "test.txt".to_string(),
    };

    pctx.lexx.set_input(Box::new(InputString::new(String::from("1 ? 1 : 0".to_string()))));
    let mut parse_result = Parser::parse(&mut pctx, &None, 0);
    if parse_result.is_err() {
        println!("Parse failed: `{}`", parse_result.err().unwrap().to_string());
        return;
    }
    let mut compile_result = parse_result.unwrap().unwrap().borrow().compile(&mut CompileContext{}, None);
    if compile_result.is_err() {
        println!("Compile failed: `{}`", compile_result.err().unwrap());
        return;
    }
    let mut ctx = ExecutionContext{ stack: Vec::new() };
    let mut running_instruction: Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> = Ok(Some(compile_result.unwrap().unwrap()));
    loop {
        match running_instruction {
            Ok(Some(i)) => {
                running_instruction = i.execute(&mut ctx);
            }
            Ok(None) => {
                break;
            }
            Err(_) => {
                println!("Execution failed: `{}`", running_instruction.err().unwrap());
                break;
            }
        }
    }
    assert_eq!(ctx.stack.pop(), Some(1));

    pctx.lexx.set_input(Box::new(InputString::new(String::from("0 ? 1 : 0".to_string()))));
    parse_result = Parser::parse(&mut pctx, &None, 0);
    compile_result = parse_result.unwrap().unwrap().borrow().compile(&mut CompileContext{}, None);
    ctx = ExecutionContext{ stack: Vec::new() };
    running_instruction = Ok(Some(compile_result.unwrap().unwrap()));
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
    assert_eq!(ctx.stack.pop(), Some(0));

    pctx.lexx.set_input(Box::new(InputString::new(String::from("0 ? 1 0".to_string()))));
    parse_result = Parser::parse(&mut pctx, &None, 0);
    assert_eq!(parse_result.err().unwrap().to_string(), "an error occurred: \"Missing ':' at 1, 7\"")
}