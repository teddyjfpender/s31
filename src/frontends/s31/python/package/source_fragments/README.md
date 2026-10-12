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

The module is part of the independent package certificate parser, separate
from production `language/` parsing and specialization. `package/context.py`
includes it in the compiler fingerprint. The certificate continues to check
the complete native gate topology, selectors, fixed root, and key under its
documented assumptions.

This fragment is intentionally exact: higher-order values, calls nested
inside an argument expression, partial operations, subtraction, nested
arithmetic expressions, and hidden effects
remain outside this v2 certificate. They remain usable through the
ordinary S31 compiler and verifier; the stricter release gate admits them
only when a corresponding independent certificate is available.
