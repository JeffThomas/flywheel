///

use std::error::Error;
use std::fmt;

use lexx::{Lexxer, LexxError};
use lexx::rolling_char_buffer::RollingCharBufferError;
use lexx::token::{Token, TOKEN_TYPE_WHITESPACE};

use crate::compiler::Compiler;
use crate::parslet::{InfixParslet, PrefixParslet};

pub static PRECEDENCE_ASSIGNMENT: u8 = 1;
pub static PRECEDENCE_CONDITIONAL: u8 = 2;
pub static PRECEDENCE_SUM: u8 = 3;
pub static PRECEDENCE_PRODUCT: u8 = 4;
pub static PRECEDENCE_EXPONENT: u8 = 5;
pub static PRECEDENCE_PREFIX: u8 = 6;
pub static PRECEDENCE_POSTFIX: u8 = 7;
pub static PRECEDENCE_CALL: u8 = 8;
pub static PRECEDENCE_EOE: u8 = 9;

/// This is the main structure holding data during the parsing, to parse a text you build
/// one of these and use it in calling the [Parser](crate::parser::Parser)
///
/// - lexx: is used to hold the text to be parsed and tokenizes it
/// - prefix: is a vec of prefix parslets
/// - infix: is a vec of infix parslets
/// - a reference for the script, such as it's file name or some other sourcing information
///
///
///```
/// # use compiler::{CompileContext, Compiler};
/// # use crate::instruction::{
/// #    AddInstruction, DivideInstruction, ExecutionContext, Instruction, MultiplyInstruction,
/// #    StaticIntInstruction, SubtractInstruction,
/// # };
/// # use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
/// # use crate::parslet::{InfixParslet, PrefixParslet};
/// # use crate::{make_infix_compiler, make_infix_compiler_function, make_prefix_compiler};
/// # use lexx::input::InputString;
/// # use lexx::matcher_integer::IntegerMatcher;
/// # use lexx::matcher_symbol::SymbolMatcher;
/// # use lexx::matcher_whitespace::WhitespaceMatcher;
/// # use lexx::token::TOKEN_TYPE_INTEGER;
/// # use lexx::token::{Token, TOKEN_TYPE_SYMBOL};
/// # use lexx::Lexx;
/// # use std::error::Error;
///
/// // A simple static integer instruction which is created with the integer it's representing. When
/// // it is executed it simply pushes this value into `ctx.stack` and return the next instruction.
/// pub struct SimpleStaticIntInstruction {
///     // the integer value we represent
///     pub value: i32,
///     // the next Instruction to be executed after this one
///     pub next: Option<Box<dyn Instruction>>,
/// }
/// impl Instruction for SimpleStaticIntInstruction {
///     // `execute` is the only function an Instruction has
///     fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
///         // the insert happens here
///         ctx.stack.push(self.value);
///         // return the next Instruction
///         Ok(self.next.as_ref())
///     }
/// }
///
/// // A very simple math instruction which only does addition and subtraction. Note that is
/// // is not ideal since it has to check which instruction it is each time it executes. The
/// // more complex example creates individual Instructions for each math function, which will
/// // execute faster.
/// pub struct SimpleMathInstruction {
///     // which math function are we
///     pub instruction: char,
///     // the next Instruction in the chain
///     pub next: Option<Box<dyn Instruction>>,
/// }
/// impl Instruction for SimpleMathInstruction {
///     fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<&Box<dyn Instruction>>, Box<dyn Error>> {
///         // pull the values we're acting on from the stack.
///         // NOTE: The order is important, 2 - 3 is not the same as 3 - 2
///         // fortunately the compiler will always provide consistent results
///         let right = ctx.stack.pop().unwrap();
///         let left = ctx.stack.pop().unwrap();
///         // perform the action and push the results into the stack
///         match self.instruction {
///             '+' => { ctx.stack.push(left + right); }
///             '-' => { ctx.stack.push(left - right); }
///             _   => {}
///         }
///         // return the next Instruction
///         Ok(self.next.as_ref())
///     }
/// }
///
/// // The Pratt parser pattern only has two kinds of Parslets, Prefix and Infix. Items that
/// // stand alone, such as a simple number, are considered Prefix Parslets that don't consume
/// // any right hand components.
/// let simple_int_parslet = PrefixParslet {
///     // the `matcher` function lets the Parser know that this Parslet will consume this token.
///     // if `matcher` returns `true` then the `generator` function will be called
///     matcher: |_ctx, token| {
///         if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
///     },
///     // the `generator` function creates a Compiler from this Parslet
///     generator: |_ctx, token| {
///         Ok(Some(Box::new(Compiler {
///             // because this is a static integer, it is a Leaf node in the Compiler tree
///             // that will be generated. We don't need to worry about the `left`, `right` or
///             // `next` fields. We also aren't using the `compiler_type` which can be used for
///             // pre-compile directives or optimizations
///             left: None, right: None, next: None, compiler_type: 0,
///             // when compiling knowing what Token created this compiler can be useful
///             token: token.clone(),
///             // the actual `compile` function which generates an Instruction
///             compile: |_ctx: &mut CompileContext, compiler: &Compiler, next: Option<Box<dyn Instruction>>| {
///                 // simply makes a `SimpleStaticIntInstruction`
///                 Ok(Some(Box::new(SimpleStaticIntInstruction
///                 {
///                     value: compiler.token.value.parse::<i32>().unwrap(),
///                     next
///                 })))
///             }})
///         ))
///     }
/// };
///
/// // The InfixParslet is a bit more complex. It typically gets handed the previously parsed
/// // Token in the form of an already created Compiler for it's left element, and then it
/// // recursively parses the next Token(s) to get it's right hand component
/// let simple_operator_parslet = InfixParslet {
///     // InfixParslets also have Precedence which insure the orders of operation are followed
///     // For an in-depth look at how they work check the docs for the Parser
///     precedence: PRECEDENCE_PRODUCT,
///     matcher: |_ctx, token, precedence| {
///         if precedence < PRECEDENCE_PRODUCT
///             && token.token_type == TOKEN_TYPE_SYMBOL {true} else {false}
///     },
///     generator: |ctx, token, left, precedence| {
///         let right = Parser::parse(ctx, left, precedence)?;
///         Ok(Some(Box::new(Compiler {
///             next: None, compiler_type: 0,
///             left: left.as_ref().map(|l:&Box<Compiler>|{l.clone()}),
///             right: right.map(|r:Box<Compiler>|{r}),
///             token: token.clone(),
///             compile: |ctx: &mut CompileContext, compiler: &Compiler, next: Option<Box<dyn Instruction>>| {
///                 let i = Box::new(
///                     SimpleMathInstruction {
///                         instruction: compiler.token.value.chars().next().unwrap(),
///                         next
///                     } );
///                 let r = (compiler.right.as_ref().unwrap().compile)(ctx, compiler.right.as_ref().unwrap(), Some(i))?;
///                 let l = (compiler.left.as_ref().unwrap().compile)(ctx, compiler.left.as_ref().unwrap(), r)?;
///                 Ok(Some(l.unwrap()))
///             }
///         })))
///     }
/// };
///
/// // Build the lexer that holds the text to parse
/// let lexx = Box::new(Lexx::<512>::new(
///     Box::new(InputString::new(String::from("3 + 2".to_string()))),
///     vec![
///         Box::new(IntegerMatcher { index: 0, precedence: 0, running: true }),
///         Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true }),
///         Box::new(SymbolMatcher { index: 0, precedence: 0, running: true }),
///     ],
/// ));
///
/// // actually create the ParseContext used by the [Parser](crate::parser::Parser)
/// let mut simple_parse_context: ParseContext = ParseContext {
///     lexx: lexx,
///     prefix: vec![
///         simple_int_parslet,
///     ],
///     infix: vec![
///         simple_operator_parslet,
///     ],
///     script: "test.txt".to_string(),
/// };
///
pub struct ParseContext {
    // the greedy lexicographic tokenizer which holds the text to be parsed
    pub lexx: Box<dyn Lexxer>,
    // the prefix parslets
    pub prefix: Vec<PrefixParslet>,
    // the infix parslets
    pub infix: Vec<InfixParslet>,
    // a reference for the script, such as it's file name or some other sourcing information
    pub script_name: String,
}

#[macro_export]
// not currently used, was used in testing
macro_rules! downcast {
    ($c:ident, $u:ident, $d:ident) => {
        unsafe { &*($c.as_ref() as *const dyn $u as *const $d) }
    };
}


#[macro_export]
/// A handy macro for burning off a required token or throwing an
/// error if the token doesn't exist. Should probably be updated
/// to allow a custom error message.
/// Handy for things like the conditional ternary `?:` where you
/// want to make sure the `:` exists and it's an error if it's not
/// there, but you don't need to parse it specifically
macro_rules! eat_token_or_throw_error {
    ( $ctx:expr, $t_type:expr, $t_value:expr ) => {
        loop {
            match $ctx.lexx.look_ahead() {
                Ok(Some(t)) => {
                    if t.token_type == TOKEN_TYPE_WHITESPACE {
                        // burn off whitespace
                        let _ = $ctx.lexx.next_token();
                        continue
                    }
                    if t.token_type == $t_type && t.value == $t_value {
                        // burn off the token
                        let _ = $ctx.lexx.next_token();
                        break;
                    } else {
                        return Err(ParseError::Error(format!("Missing '{}' at {}, {}",$t_value,t.line,t.column).parse().unwrap()))
                    }
                }
                _ => {
                    return Err(ParseError::Error("Unexpected EOF".parse().unwrap()))
                }
            }
        }
    };
}


#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseError {
    TokenNotFound(String),
    NoParserFound(Token),
    Error(String),
}

impl From<LexxError> for ParseError {
    fn from(le: LexxError) -> ParseError {
        match le {
            LexxError::TokenNotFound(f) => ParseError::TokenNotFound(f),
            LexxError::Error(e) => ParseError::Error(e),
        }
    }
}

impl From<RollingCharBufferError> for ParseError {
    fn from(le: RollingCharBufferError) -> ParseError {
        match le {
            RollingCharBufferError::BufferFullError => {
                ParseError::Error(String::from("the lexx buffer is full"))
            }
            RollingCharBufferError::BufferEmptyError => {
                ParseError::Error(String::from("the lexx buffer is empty"))
            }
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ParseError::NoParserFound(ref t) => {
                write!(f, "a parser could not be found for: {:?}", t.value)
            }
            ParseError::TokenNotFound(ref s) => {
                write!(f, "a parser could not be found for: {:?}", s)
            }
            ParseError::Error(ref e) => {
                write!(f, "an error occurred: {:?}", e)
            }
        }
    }
}

impl Error for ParseError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        match *self {
            ParseError::NoParserFound(..) => "a parser could not be found",
            ParseError::TokenNotFound(..) => "no token could be found",
            ParseError::Error(..) => "an error occurred",
        }
    }
}


///
/// # Pratt Parser
///
/// The Pratt style parser is an `operator-precedence` style parser that makes parsing and
/// handling precedence extremely simple.
///
/// I won't spend more time describing Pratt parsing, others have done a better job, listed
/// the the references here.
///
/// ## Useful References
/// A justifiably often sited and simple explanation of Pratt parsers using Java, this was my
/// introduction to them:
/// https://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/
///
/// Pratt parsing is mentioned in the Wikipedia article for `operator-precedence parser` with more
/// references: https://en.wikipedia.org/wiki/Operator-precedence_parser
///
/// Here's a pretty good tutorial describing Pratt parsers using Rust which I just found
/// while writing this reference section:
/// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
///
/// ## Usage
/// This object is stateless, to use it create a [ParseContext](crate::parser::ParseContext)
///
/// # Precedence
///
/// One thing I don't thing other documents do is explain exactly how the precedence parsing
/// works, which can look like a dark magic. I'll try to explain it here, partially for my own
/// clarification.
///
/// ##  Parsing '3 * 2 + 4' without precedence
///
/// First we look for a prefix token and parse the '3'
///
/// () brackets indicate what node the parser currently is at
///```text
///   (3)
///
/// '* 2 + 4'
/// ```
/// Then we enter the infix loop, find the '*' and pass in the '3' as the left hand component.
///```text
///        (*)
///       /
///     3
///
/// '2 + 4'
///```
/// Then, still in the infix loop we recurse and look for a prefix token.
/// We find the '2'.
///```text
///         *
///       /  \
///     3     (2)
///
/// '+ 4'
///```
/// We enter the infix loop, find the '+' and pass in the '2' as the left hand component.
///```text
///         *
///       /   \
///     3     (+)
///          /
///        2
///
/// '4'
///```
/// Then, still in the infix loop we recurse and look for a prefix token.
/// We find the 4.
///```text
///         *
///       /   \
///     3      +
///          /  \
///        2    (4)
///```
/// We again enter the infix loop, but now we've hit the EOF so we return through the recursions
///```text
///         *
///       /   \
///     3     (+)
///          /  \
///        2     4
///
///        (*)
///       /   \
///     3      +
///          /  \
///        2     4
///
///         *
///       /   \
///     3      +
///          /  \
///        2     4
///```
/// And we're done, but wrong because compiling will result in 3,2,4,+,* which will compute to 18.
/// Now lets see how this works with precedence in a Pratt parser.
///
/// # Parsing '3 * 2 + 4' WITH precedence in a Pratt parser
///
/// First we look for a prefix token and parse the '3', our precedence starts at '0'
///
/// The number outside the brackets indicates the current precedence
///```text
///   (3)0
///
/// '* 2 + 4'
///```
/// Then we enter the infix loop, find the '*' and pass in the '3' as the left hand component. Our
/// precedence is still '0'
///```text
///        (*)0
///       /
///     3
///
/// '2 + 4'
///```
/// Then, still in the infix loop we recurse and look for a prefix token, but since we're at a
/// multiplication symbol we pass the 'PRODUCT' precedence from the '*', which is '4'.
/// We find the '2'.
///```text
///         *
///       /  \
///     3     (2)4
///
/// '+ 4'
///```
/// We enter the infix loop, find the '+' BUT the '+' has a 'SUM' precedence which is only '3' and
/// we are at '4', so don't parse it and return instead.
///```text
///        (*)0
///       /  \
///     3     2
///
/// '+ 4'
///```
/// We're still in the infix loop here with a precedence of '0', so we look for an infix token and
/// find the '+', since our precedence is now '0' which is less than '3' we can parse it, and we
/// pass the '*' in as the left hand component.
///```text
///            (+)0
///           /
///         *
///       /   \
///     3      2
///
/// '4'
///```
/// Now we recurse again to look for a prefix token, but pass in the precedence of the '+'.
/// We find the '4'
///```text
///             +
///           /  \
///         *    (4)3
///       /   \
///     3      2
///
///```
/// We again entire the infix loop, with a precedence of '3', but we've hit EOF so we return
///```text
///            (+)0
///           /  \
///         *     4
///       /   \
///     3      2
///
///             +
///           /  \
///         *     4
///       /   \
///     3      2
///```
/// Now when we compile we'll get 3,2,*,4,+ which will compute to 10
///
pub struct Parser {}

impl Parser {
    fn next_token(ctx: &mut ParseContext) -> Result<Option<Token>, LexxError> {
        let mut token: Option<Token>;

        token = ctx.lexx.next_token()?;

        if token.is_some() && token.as_ref().unwrap().token_type == TOKEN_TYPE_WHITESPACE {
            token = ctx.lexx.next_token()?;
        }

        if token.is_none() {
            return Ok(None);
        }
        Ok(token)
    }
    pub fn parse(
        ctx: &mut ParseContext,
        left: &Option<Box<dyn Compiler>>,
        precedence: u8,
    ) -> Result<Option<Box<dyn Compiler>>, ParseError> {
        let uctx = ctx as *mut ParseContext;

        let token = match Parser::next_token(ctx)? {
            Some(t) => t,
            None => return Ok(None),
        };

        let mut left_compiler: Option<Box<dyn Compiler>> = None;

        // unsafe pointer use because of recursion
        // this could probably be done with RefCell but there's no need for the overhead
        // of runtime borrow checking
        unsafe {
            for p in &(*uctx).prefix {
                left_compiler = p.parse(ctx, &token, left, precedence)?;
                if left_compiler.is_some() {
                    break;
                }
            }
        }

        if left_compiler.is_none() {
            ctx.lexx.rewind(token.clone())?;
            return Err(ParseError::NoParserFound(token));
        }

        loop {
            let mut infix_compiler: Option<Box<dyn Compiler>> = None;
            let token = match Parser::next_token(ctx)? {
                Some(t) => t,
                None => return Ok(left_compiler),
            };

            unsafe {
                for p in &(*uctx).infix {
                    infix_compiler = p.parse(ctx, &token, &left_compiler, precedence)?;
                    if infix_compiler.is_some() {
                        break;
                    }
                }
            }

            if infix_compiler.as_ref().is_none() {
                ctx.lexx.rewind(token)?;
                break;
            }
            left_compiler = infix_compiler;
        }

        return Ok(left_compiler);
    }
}
