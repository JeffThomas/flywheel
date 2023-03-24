# Flywheel

Flywheel is a Rust framework for building scripting languages. It contains a Pratt inspired
[Parser](crate::parser::Parser) which builds a [Compiler](crate::compiler::Compiler) tree which
 will then produce an [Instructions](crate::instruction::Instruction) chain.

For example the expression `3 * 2 + 4` will parse into a Compiler tree like so:

```angular2html
          C(+)
         /   \
      C(*)  C(4)
      /  \
    C(3) C(2)
```

Then `C(+).compile(ctx)` is called it will result in an [Instruction](crate::instruction::Instruction) chain like so:

```angular2html
integer(3)->integer(2)->subtract(-)->integer(4)->addition(+)
```

## Execution
The execution engine need simply call `.run(ctx)` on the first [Instruction](crate::instruction::Instruction), which returns
the next [Instruction](crate::instruction::Instruction) to be run and so on. The engine need know nothing about what the
[Instructions](crate::instruction::Instruction) do. Flywheel comes with some very simple execution engines in the samples
and an execution context with nothing but an Integer stack in it. Executing the above
example would look like this:

```angular2html
Step 1
integer(3).run(ctx) -> Some(integer(2))
// 3 was inserted into the stack, Some(integer(2)) is returned
// ctx.stack = [3]

Step 2
integer(2).run(ctx) -> Some(multiply(*))
// 2 was pushed into the stack, Some(multiply(*)) is returned
// ctx.stack = [2,3]

Step 3
multiply(-).run(ctx) -> Some(integer(4))
// 3 and 2 were pulled out, subtracted and the results pushed into the stack, Some(integer(4)) is returned
// ctx.stack = [1]

Step 4
integer(4).run(ctx) -> Some(addition(+))
// 4 was pushed into the stack, Some(addition(+)) is returned
// ctx.stack = [4,1]

Step 5
addition(+).run(ctx) -> None
// 1 and 4 were pulled out, added and the results pushed into the stack, None is returned
// ctx.stack = [5]
```

Flywheel consist of:
* A Pratt inspired recursive decent parser utilizing [Parslets](crate::parslet::PrefixParslet)
  which consume [Tokens](crate::lexx::token::Token) and produce a [Compiler](crate::compiler::Compiler) tree structure
* [Compiler](crate::compiler::Compiler)s which will compile down to a chain of [Instructions](crate::instruction::Instruction)
* When an [Instruction](crate::instruction::Instruction) is run it returns the next [Instruction](crate::instruction::Instruction) to be run


# Dependencies

Rust uses the Lexx string tokenizer.

# USE

Flywheel is not intended to be used as-is or as a library. Instead it's ment to
be Forked and modified to suit whatever need you wish.

# More Information

Check out the rust documents and examples for lots more detail!