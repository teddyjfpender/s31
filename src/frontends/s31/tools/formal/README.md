# S31 formal exporters

`export_square4_topology.zig` compiles normalized IR using the production
`relation_compiler.compileDirectWithSpans` path in topology mode. It checks
that `functional_square4.s31` lowers to two adjacent pointwise multiplication
rows whose gate IDs form a self-square chain. It also checks the input pack's
three basis multiplications and three additions against the compiler's pinned
QM31 basis constants, then prints their observed gate IDs and row spans as a
Lean module.

`scripts/s31_formal.py` runs the Python text compiler on the checked-in
`.s31` source, passes that fresh IR to this executable, and compares the
printed Lean module byte for byte with the committed
`formal/s31/S31/Gadgets/Functional/TextSquare4Native.lean`. The Lean proof
interprets the exported gate chain with the local AIR row model. The exporter
is an evidence bridge for this concrete program; it does not verify the Zig
compiler for every input program or the complete STARK protocol.
