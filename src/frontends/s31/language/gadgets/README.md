# Relation compiler gadgets

`integer_multiply.zig` implements fixed-width wrapping and complete
multiplication with byte-constrained schoolbook columns. Its local comments
spell out the integer bounds that make each M31 field equation sound. The
parent
[`relation_compiler.zig`](../relation_compiler.zig) connects the gadget to
normalized relation nodes and the circuit builder, including signed and
unsigned checked-overflow constraints.

`integer_bits.zig` decomposes byte or u16 limbs into proved Boolean wires,
computes AND/OR/XOR/NOT with arithmetic gates, and packs result bits back to
bounded limbs. The relation compiler caches a decomposition per wire and limb
width, so consecutive bitwise nodes reuse it. This path stays in the
arithmetic/Equation AIR components and does not activate the large generic
XOR lookup table.
