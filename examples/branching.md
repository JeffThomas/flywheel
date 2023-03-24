## Branching
While there isn't (currently) an example it is expected that branching is handled
by forking the chain and having the branching Instruction return whichever
Instruction is appropriate. The instruction chain looking something like:

```angular2html
I(rand)->I(if)->I('yes')->I('is decided')
              \>I('no')/
```
``I(if)`` will return either ``I('yes')`` or ``I('no')`` depending on how it
interoperates the results of ``I(rand)`` 
