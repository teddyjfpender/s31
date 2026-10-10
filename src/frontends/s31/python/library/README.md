# Compiler-owned source libraries

`stdlib.py` defines S31 source types, values and the checked relation builder.
`math.py` supplies the field, array and fixed-width combinators that use that
builder. Both modules emit only normalized relation nodes; Zig validates the
relation, chooses AIR, builds witnesses and generates the native verifier.

The root `s31_stdlib.py` and `s31_mathlib.py` files are compatibility imports.
The compiler fingerprint includes these imports and every Python file here.
The package `stdlib-lock.json` hashes both compatibility imports and the two
implementation modules, so a published package records the exact library
source used for compilation. `std@1` remains the source-language library ABI.
