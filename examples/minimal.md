# Minimal

This is almost literally the least Flywheel can do and actually have a script run. This
example builds a Parslet that can parse an integer number and builds an IntCompiler with
the number in it. The IntCompiler will build a StaticIntInstruction which will just push
that integer number into the stack located in the Execution Context.

1. int_parslet: gets the integer Token and builds an IntCompiler
2. IntCompiler: on compile builds a StaticIntInstruction with the integer
3. StaticIntInstruction: on execution pushes the integer into the stack