# Flywheel

Flywheel is a framework for writing scripting languages in Rust. 
It consist of the following components:

* A Pratt inspired recursive decent parser utilizing [Parslets](crate::parslet::PrefixParslet)
which consume [Tokens](crate::lexx::token::Token) and produce a [Compiler](crate::compiler::Compiler) tree structure
* [Compiler](crate::compiler::Compiler)s which will compile down to a chain of [Instructions](crate::instruction::Instruction)
* When an [Instruction](crate::instruction::Instruction) is run it returns the next [Instruction](crate::instruction::Instruction) to be run

## Parsing and Compiling

Flywheel comes with a couple of simple implementations of itself which can execute
expressions such as `3 * 2 + 4` or `(1 + (2 + 3) * 4 - 5) * 9 / 3 (1 +1) 2*5`. Yes,
there are 3 different expressions in that last one seperated by spaces. Flywheel
can handle that.

As an example the expression `3 * 2 + 4` will parse into a Compiler tree like so:

```angular2html
          C(+)
         /   \
      C(*)  C(4)
      /  \
    C(3) C(2)
```

When `C(+).compile(ctx)` is called it will result in an [Instruction](crate::instruction::Instruction) chain like so:

```angular2html
Iinteger(3)->Iinteger(2)->Isubtract(-)->Iinteger(4)->Iaddition(+)
```

## Execution
The execution engine need simply call `.run(ctx)` on the first [Instruction](crate::instruction::Instruction), which returns
the next [Instruction](crate::instruction::Instruction) to be run and so on. The engine need know nothing about what the
[Instructions](crate::instruction::Instruction) do. Flywheel comes with some very simple execution engines in the samples
and an execution context with nothing but an Integer stack in it. Executing the above
example would look like this

```angular2html
Step 1
Iinteger(3).run(ctx) -> Some(Iinteger(2))
// 3 was inserted into the stack, Some(Iinteger(2)) is returned
// ctx.stack = [3]

Step 2
Iintger(2).run(ctx) -> Some(Imultiply(*))
// 2 was pushed into the stack, Some(Imultiply(*)) is returned
// ctx.stack = [2,3]

Step 3
Imultiply(-).run(ctx) -> Some(Iinteger(4))
// 3 and 2 were pulled out, subtracted and the results pushed into the stack, Some(Iinteger(4)) is returned
// ctx.stack = [1]

Step 4
Iintger(4).run(ctx) -> Some(Iaddition(+))
// 4 was pushed into the stack, Some(Iaddition(+)) is returned
// ctx.stack = [4,1]

Step 5
Iaddition(+).run(ctx) -> None
// 1 and 4 were pulled out, added and the results pushed into the stack, None is returned
// ctx.stack = [5]
```


## Branching?
While there isn't (currently) an example it is expected that branching is handled
by forking the chain and having the branching Instruction return whichever
Instruction is appropriate. The instruction chain looking something like:

```angular2html
I(rand)->I(if)->I('yes')->I('is decided')
              \>I('no')/
```
``I(if)`` will return either ``I('yes')`` or ``I('no')`` depending on how it
interoperates the results of ``I(rand)`` 

# Dependencies

Rust uses the Lexx string tokenizer.

# USE

Flywheel is not intended to be used as-is or as a library. Instead it's ment to
be Forked and modified to suit whatever need you wish.

# More Information

Check out the rust documents and examples for lots more detail!