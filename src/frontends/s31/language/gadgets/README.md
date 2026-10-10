# Relation compiler gadgets

`integer_multiply.zig` implements fixed-width wrapping multiplication with
byte-constrained schoolbook columns. Its local comments spell out the integer
bounds that make each M31 field equation sound. The parent
[`relation_compiler.zig`](../relation_compiler.zig) connects the gadget to
normalized relation nodes and the circuit builder.
