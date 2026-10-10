# Compiler-owned source libraries

`stdlib.py` defines S31 source types, values and the checked relation builder.
`math.py` supplies the field, array and fixed-width combinators that use that
builder. `addition_chains.py` finds bounded static power schedules and falls
back to binary powering when no shorter schedule is found. The combinators
emit only normalized relation nodes; Zig validates the relation, chooses AIR,
builds witnesses and generates the native verifier.

The root `s31_stdlib.py` and `s31_mathlib.py` files are compatibility imports.
The compiler fingerprint includes these imports and every Python file here.
The package `stdlib-lock.json` hashes both compatibility imports and every
implementation module, so a published package records the exact library
source used for compilation. `std@1` remains the source-language library ABI.
