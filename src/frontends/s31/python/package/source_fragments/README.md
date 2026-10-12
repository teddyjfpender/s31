# Certified source fragments

`static_helper.py` parses one pure, monomorphic named function before the
v2 direct-gate circuit grammar. Its body is exactly one addition or
pointwise multiplication of one or two `[m31; 4]` parameters. At a call,
the checker resolves arguments to existing circuit wires and emits the same
single relation node as handwritten arithmetic. Function declaration and
application have no AIR representation.

The module is part of the independent package certificate parser, separate
from production `language/` parsing and specialization. `package/context.py`
includes it in the compiler fingerprint. The certificate continues to check
the complete native gate topology, selectors, fixed root, and key under its
documented assumptions.

This fragment is intentionally exact: higher-order values, nested calls,
partial operations, subtraction, multi-operation helper bodies, and hidden
effects remain outside this v2 certificate. They remain usable through the
ordinary S31 compiler and verifier; the stricter release gate admits them
only when a corresponding independent certificate is available.
