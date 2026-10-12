# Certified source fragments

`static_helper.py` parses up to eight pure, monomorphic functions before the
v2 direct-gate circuit grammar. Each accepts one or two `[m31; 4]`
parameters, local arithmetic or call lets, and a final add, pointwise
multiply, earlier-declared function call, or last local value. Calls to later
functions and recursion are rejected. Every argument and operand names a
parameter or earlier local. There are at most sixteen gates across the entire
circuit. The checker statically expands calls in declaration order and
independently derives the production specializer's generated wire names, so
its complete normalized relation must match the package. Function values and
applications have no separate AIR representation.

`lexical_let.py` independently parses bounded expression-level
`let name = bound in body` inside a circuit let. The bound expression is
evaluated eagerly, without a requested output name; a newly emitted gate
therefore receives the next `_s31_N` wire. The body sees a lexical reference
to that wire and receives the outer circuit let's requested name. Bindings
may shadow earlier source names, and nested lets are limited to depth 16.
The expression leaf is one existing wire, one `+` or `.*` gate, or a call to
one of the pure functions above. The binder itself produces no relation node.
The [worked native example](../../../examples/functional/release_let4/README.md)
shows the complete two-gate lowering and exact AIR-cost comparison.

The module is part of the independent package certificate parser, separate
from production `language/` parsing and specialization. `package/context.py`
includes it in the compiler fingerprint. The certificate continues to check
the complete native gate topology, selectors, fixed root, and key under its
documented assumptions.

This fragment is intentionally exact: higher-order values, calls nested
inside an argument expression, partial operations, subtraction,
multi-operator arithmetic expressions, and hidden effects
remain outside this v2 certificate. They remain usable through the
ordinary S31 compiler and verifier; the stricter release gate admits them
only when a corresponding independent certificate is available.
