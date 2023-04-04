# Branching
This is an example of how branching is expected to work
e. Branching is handled by forking the Instruction chain and having the 
branching Instruction return whichever Instruction is appropriate. 
The instruction chain for a pseudocode 
`(rand ? 'true' : 'false') 'is decided'` looking something like:

```angular2html
I(rand)->I(if)->I('true')->I('is decided')
              \>I('false')/
```
``I(if)`` will return either ``I('true')`` or ``I('false')`` depending on how it
interoperates the results of ``I(rand)`` 

The ternary `?:` operator is used for the example, it uses a custom InfixParslet
which consumes the left hand expression as the conditional to be evaluated, then consumes
the right had expression which with be the `if true` branch. It then looks for
the `:` character, if it fails to find that it throws a parsing error. If it does
find the ':' it consumes it and then parses the next expression as the `if false`
branch. It then creates the custom Compiler giving it the three parsed expressions.

The compiler then builds the Instruction chain simply giving the BranchingInstruction the
`if true` and `if false` branches which it can chose to return given the conditional. Each
of those chains need to link back to the next piece of the chain, the `is decided` in 
the chain above.