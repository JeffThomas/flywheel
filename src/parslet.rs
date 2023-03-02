use lexx::token::Token;

use crate::compiler::CompilerStruct;
use crate::parser::{ParseContext, ParseError, Parser};

pub struct PrefixParslet {
    pub matcher: fn(ctx: &mut ParseContext, token: &Token) -> bool,
    pub generator: fn(
        ctx: &mut ParseContext,
        token: &Token,
    ) -> Result<Option<Box<CompilerStruct>>, ParseError>,
}
impl PrefixParslet {
    pub fn parse(
        &self,
        ctx: &mut ParseContext,
        token: &Token,
        _left: &Option<Box<CompilerStruct>>,
        _precedence: u8,
    ) -> Result<Option<Box<CompilerStruct>>, ParseError> {
        if (self.matcher)(ctx, token) {
            (self.generator)(ctx, token)
        } else {
            Ok(None)
        }
    }
    pub fn chain_parse(ctx: &mut ParseContext) -> Result<Option<Box<CompilerStruct>>, ParseError> {
        let next = Parser::parse(ctx, &None, 0)?;
        return match next {
            None => Ok(None),
            Some(mut n) => {
                n.next = PrefixParslet::chain_parse(ctx)?;
                Ok(Some(n))
            }
        };
    }
    pub fn chain_parse_until_token(
        ctx: &mut ParseContext,
        token: &Token,
    ) -> Result<Option<Box<CompilerStruct>>, ParseError> {
        match ctx.lexx.look_ahead() {
            Ok(Some(t)) => {
                if t.token_type == token.token_type && t.value == token.value {
                    let _ = ctx.lexx.next_token();
                    return Ok(None);
                }
            }
            _ => {}
        }
        let next = Parser::parse(ctx, &None, 0)?;
        return match next {
            None => Ok(None),
            Some(mut n) => {
                n.next = PrefixParslet::chain_parse_until_token(ctx, token)?;
                Ok(Some(n))
            }
        };
    }
}

pub struct InfixParslet {
    pub precedence: u8,
    pub matcher: fn(ctx: &mut ParseContext, token: &Token, precedence: u8) -> bool,
    pub generator: fn(
        ctx: &mut ParseContext,
        token: &Token,
        left: &Option<Box<CompilerStruct>>,
        precedence: u8,
    ) -> Result<Option<Box<CompilerStruct>>, ParseError>,
}
impl InfixParslet {
    pub fn parse(
        &self,
        ctx: &mut ParseContext,
        token: &Token,
        left: &Option<Box<CompilerStruct>>,
        precedence: u8,
    ) -> Result<Option<Box<CompilerStruct>>, ParseError> {
        if (self.matcher)(ctx, token, precedence) {
            (self.generator)(ctx, token, left, self.precedence)
        } else {
            Ok(None)
        }
    }
}
