# Certified source fragments

`static_helper.py` parses one pure, monomorphic named function before the
v2 direct-gate circuit grammar. It accepts one or two `[m31; 4]` parameters,
zero or more local arithmetic lets, and a final add, pointwise multiply, or
the last local value. Every operand must name a parameter or earlier local;
there are at most sixteen gates across the entire circuit. At each call, the
checker resolves arguments to existing circuit wires and replays every gate
in order. It independently derives the production specializer's generated
wire names, so its complete normalized relation must match the package.
Function declaration and application have no AIR representation.

The module is part of the independent package certificate parser, separate
from production `language/` parsing and specialization. `package/context.py`
includes it in the compiler fingerprint. The certificate continues to check
the complete native gate topology, selectors, fixed root, and key under its
documented assumptions.

This fragment is intentionally exact: higher-order values, nested calls,
partial operations, subtraction, nested expressions, and hidden effects
remain outside this v2 certificate. They remain usable through the
ordinary S31 compiler and verifier; the stricter release gate admits them
only when a corresponding independent certificate is available.
