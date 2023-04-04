use std::cell::RefCell;
use std::error::Error;
use std::fs::File;
use std::io::stdin;
use std::rc::Rc;
use std::sync::Arc;

use clap::Parser as CliParser;
use lexx::input::{InputReader, InputString, LexxInput};
use lexx::Lexx;
use lexx::matcher_exact::ExactMatcher;
use lexx::matcher_integer::IntegerMatcher;
use lexx::matcher_whitespace::WhitespaceMatcher;
use lexx::token::{Token, TOKEN_TYPE_INTEGER, TOKEN_TYPE_WHITESPACE};

use crate::compiler::{CompileContext, CompileError, Compiler};
use crate::instruction::{ExecutionContext, Instruction};
use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_CALL, PRECEDENCE_PREFIX, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
use crate::parslet::{InfixParslet, PrefixParslet};

pub mod compiler;
pub mod instruction;
pub mod parser;
pub mod parslet;

pub const TOKEN_TYPE_OPERATOR: u16 = 20;

#[derive(CliParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name of file to parse
    #[arg(short, long, default_value_t = String::from(""))]
    file: String,
    #[arg(default_value_t = String::from(""))]
    raw: String,
}


pub struct StaticIntInstruction {
    pub value: i32,
    pub next: Option<Arc<dyn Instruction>>,
}
impl Instruction for StaticIntInstruction {
    // `execute` is the only function an Instruction has
    fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        // the insert happens here
        ctx.stack.push(self.value);
        // return the next Instruction
        Ok(self.next.clone())
    }
}

pub struct AddInstruction {
    pub next: Option<Arc<dyn Instruction>>,
}
impl Instruction for AddInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left + right);
        Ok(self.next.clone())
    }
}
pub struct SubtractInstruction {
    pub next: Option<Arc<dyn Instruction>>,
}
impl Instruction for SubtractInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left - right);
        Ok(self.next.clone())
    }
}
pub struct MultiplyInstruction {
    pub next: Option<Arc<dyn Instruction>>,
}
impl Instruction for MultiplyInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left * right);
        Ok(self.next.clone())
    }
}
pub struct DivideInstruction {
    pub next: Option<Arc<dyn Instruction>>,
}
impl Instruction for DivideInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        let left = ctx.stack.pop().unwrap();
        ctx.stack.push(left / right);
        Ok(self.next.clone())
    }
}
pub struct NegateInstruction {
    pub next: Option<Arc<dyn Instruction>>,
}
impl Instruction for NegateInstruction {
    fn execute(
        &self,
        ctx: &mut ExecutionContext,
    ) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        let right = ctx.stack.pop().unwrap();
        ctx.stack.push(-right);
        Ok(self.next.clone())
    }
}


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

pub struct NegateCompiler {
    pub right: Option<Rc<RefCell<dyn Compiler>>>,
    pub token: Token,
    pub compiler_type: u8,
}
impl Compiler for NegateCompiler {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Arc<dyn Instruction>>,
    ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
        let i = Arc::new(NegateInstruction {
            next,
        });
        let r = self.right.as_ref().unwrap().borrow().compile(ctx, Some(i))?;
        Ok(r)
    }
    fn get_type(&self) -> u8 { self.compiler_type }
    fn get_token(&self) -> Token { self.token.clone() }
}

pub struct MathCompiler {
    pub left: Option<Rc<RefCell<dyn Compiler>>>,
    pub right: Option<Rc<RefCell<dyn Compiler>>>,
    pub token: Token,
    pub compiler_type: u8,
}
impl Compiler for MathCompiler {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Arc<dyn Instruction>>,
    ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
        let i: Arc<dyn Instruction> = match self.token.value.as_str() {
            "+" => { Arc::new(AddInstruction { next } ) }
            "-" => { Arc::new(SubtractInstruction { next } ) }
            "*" => { Arc::new(MultiplyInstruction { next } ) }
            "/" => { Arc::new(DivideInstruction { next } ) }
            _ => { Arc::new(AddInstruction { next } ) } // this can (should) not happen
        };
        let r = self.right.as_ref().unwrap().borrow().compile(ctx, Some(i))?;
        let l = self.left.as_ref().unwrap().borrow().compile(ctx, r)?;
        Ok(l)
    }
    fn get_type(&self) -> u8 { self.compiler_type }
    fn get_token(&self) -> Token { self.token.clone() }
}

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
                then_branch: tb,
                else_branch: eb
            } );
        let if_expression = self.if_expression.as_ref().unwrap().borrow().compile(ctx, Some(bi))?;
        Ok(Some(if_expression.unwrap()))
    }
    fn get_type(&self) -> u8 { self.compiler_type }
    fn get_token(&self) -> Token { self.token.clone() }
}

pub struct BranchingInstruction {
    pub instruction: char,
    pub then_branch: Option<Arc<dyn Instruction>>,
    pub else_branch: Option<Arc<dyn Instruction>>,
}
impl Instruction for BranchingInstruction {
    fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> {
        let if_results = ctx.stack.pop().unwrap();
        if if_results == 0 {
            return Ok(self.else_branch.clone())
        }
        Ok(self.then_branch.clone())
    }
}

pub struct ScriptCompiler {
    pub next: Option<Rc<RefCell<dyn Compiler>>>,
    pub token: Token,
    pub compiler_type: u8,
}
impl Compiler for ScriptCompiler {
    fn compile(
        &self,
        ctx: &mut CompileContext,
        next: Option<Arc<dyn Instruction>>,
    ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
        match self.next {
            Some(ref n) => { n.borrow().compile(ctx, None) }
            None => { Ok(next) }
        }
    }
    fn get_type(&self) -> u8 { self.compiler_type }
    fn get_token(&self) -> Token { self.token.clone() }
}


pub fn make_parse_context(input: Box<dyn LexxInput>) -> ParseContext {
    let eoe_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_OPERATOR
                && ";" == token.value { true } else { false }},
        generator: |ctx, _token| {
            Parser::parse(ctx, &None, 0)
        },
    };

    let int_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(IntCompiler {
                token: token.clone(),
                compiler_type: 0,
            }))))
        },
    };

    let negate_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_OPERATOR
                && "-" == token.value { true } else { false }},
        generator: |ctx, token| {
            let right = Parser::parse(ctx, &None, PRECEDENCE_PREFIX)?;
            Ok(Some(Rc::new(RefCell::new(NegateCompiler {
                right,
                token: token.clone(),
                compiler_type: 0,
            }))))
        },
    };
    let div_operator = InfixParslet {
        precedence: PRECEDENCE_PRODUCT,
        matcher: |_ctx, token, precedence| {
            if precedence < PRECEDENCE_PRODUCT
                && token.token_type == TOKEN_TYPE_OPERATOR
                && "/" == token.value { true } else { false }},
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: 0,
            }))))
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
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: 0,
            }))))
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
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: 0,
            }))))
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
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: 0,
            }))))
        },
    };

    let branching_parslet = InfixParslet {
        precedence: PRECEDENCE_CALL,
        matcher: |_ctx, token, precedence| {
            if precedence < PRECEDENCE_CALL
                && token.token_type == TOKEN_TYPE_OPERATOR
                && token.value == "?" {true} else {false}
        },

        generator: |ctx, token, left, precedence| {
            let then_branch = Parser::parse(ctx, &None, precedence)?;
            eat_token_or_throw_error!(ctx, TOKEN_TYPE_OPERATOR, ":");
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



    return ParseContext {
        lexx: Box::new(Lexx::<512>::new(
            input,
            vec![
                Box::new(IntegerMatcher { index: 0, precedence: 0, running: true, }),
                Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true, }),
                Box::new(ExactMatcher::build_exact_matcher(
                    vec!["+", "-", "*", "/", "(", ")", ";","?",":"],
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
            div_operator,
            branching_parslet
        ],
        script_name: "test.txt".to_string(),
    };

}

pub fn execute_instructions(instruction: Arc<dyn Instruction>) -> Result<ExecutionContext, Box<dyn Error>> {
    let mut ctx = ExecutionContext { stack: Vec::new() };


    let mut running_instruction: Result<Option<Arc<dyn Instruction>>, Box<dyn Error>> = Ok(Some(instruction));

    loop {
        match running_instruction {
            Ok(Some(i)) => {
                running_instruction = i.execute(&mut ctx);
            }
            Ok(None) => {
                return Ok(ctx);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }
}

pub fn run_script(parse_context: &mut ParseContext) -> Result<ExecutionContext, Box<dyn Error>> {

    let parse_result = PrefixParslet::chain_parse(parse_context);

    if parse_result.as_ref().is_err() {
        println!("{}", parse_result.as_ref().err().unwrap());
        return Err(Box::new(parse_result.as_ref().err().unwrap().clone()));
    }

    let compiler = parse_result.unwrap().unwrap();
    let compile_result = compiler.borrow().compile(&mut CompileContext {}, None);

    if compile_result.is_err() {
    }

    let instruction = match compile_result {
        Ok(None) => {
            return Ok(ExecutionContext{ stack: vec![] });
        },
        Ok(cr) => {
            cr.unwrap()
        },
        Err(e) => {
            return Err(Box::new(e));
        }
    };

    execute_instructions(instruction)
}

fn main() {
    let args = Args::parse();

    let input: Box<dyn LexxInput> = if args.file != "" {
        let file = File::open(args.file).unwrap();
        Box::new(InputReader::new(file))
    } else if args.raw != "" {
        Box::new(InputString::new(args.raw))
    } else {
        let input_stdin = InputReader::new(stdin());
        Box::new(input_stdin)
    };

    let mut pc = make_parse_context(input);

    let run_result = run_script(&mut pc);

    let mut ctx = match run_result {
        Ok(ctx) => {
            ctx
        }
        Err(e) => {
            println!("{}", e);
            return;
        }
    };

    loop {
        match ctx.stack.pop() {
            None => {
                return
            }
            Some(i) => {
                println!("{}", i)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use lexx::input::InputString;

    use crate::{make_parse_context, run_script};

    #[test]
    fn test_basic_parse_and_execute() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1"))));

        let ctx = run_script(&mut pc);

        assert_eq!(ctx.unwrap().stack.pop(), Some(1));
    }

    #[test]
    fn test_basic_addition() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1 + 2"))));

        let ctx = run_script(&mut pc);

        assert_eq!(ctx.unwrap().stack.pop(), Some(3));
    }

    #[test]
    fn test_basic_precedence() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1 + 2 * 3"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(7));

        pc.lexx.set_input(Box::new(InputString::new(String::from("2 * 3 + 1"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(7));
    }

    #[test]
    fn test_basic_sub() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("(1 + 2) * 3"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(9));

        pc.lexx.set_input(Box::new(InputString::new(String::from("2 * (3 + 1)"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(8));
    }

    #[test]
    fn test_basic_sub_sub() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("(6+((2 * (3 + 1))/2))"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(10));

        pc.lexx.set_input(Box::new(InputString::new(String::from("((((3 + 1))))"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(4));
    }

    #[test]
    fn test_prefix_negate() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("-1"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(-1));

        pc.lexx.set_input(Box::new(InputString::new(String::from("3 * -5"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(-15));

        pc.lexx.set_input(Box::new(InputString::new(String::from("-3 * -5"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(15));

        pc.lexx.set_input(Box::new(InputString::new(String::from("-3 + -5"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(-8));

        pc.lexx.set_input(Box::new(InputString::new(String::from("(6+(-(2 * (3 + 1))/-2))"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(10));
    }

    #[test]
    fn test_ternary_branch() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1 ? 1 : 0"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(1));

        pc.lexx.set_input(Box::new(InputString::new(String::from("0 ? 1 : 0"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(0));

        pc.lexx.set_input(Box::new(InputString::new(String::from("1 + (-1) ? (3 * 6 + 1) : (5 * 2) + 2"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(22));

        pc.lexx.set_input(Box::new(InputString::new(String::from("(1 + -1) ? (3 * 6 + 1) : (5 * 2) + 2"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(12));
    }

    #[test]
    fn test_chaining_expressions() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1+2 3 + 4 5+6 "))));
        let mut ctx = run_script(&mut pc);
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(11));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(7));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(3));

        pc.lexx.set_input(Box::new(InputString::new(String::from("(1+2); -(3 + 4) (5+6)"))));
        let mut ctx = run_script(&mut pc);
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(11));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(-7));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(3));
    }

}