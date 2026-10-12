# Certified source fragments

`static_helper.py` parses up to eight pure, monomorphic functions before the
v2 direct-gate circuit grammar. Each accepts one or two parameters of type
`[m31; 4]` or the unary `Fn([m31; 4]) -> [m31; 4]`, local arithmetic or call
lets, and a final add, pointwise
multiply, earlier-declared function call, or last local value. Calls to later
functions and recursion are rejected. A `Fn` value can resolve to an earlier
named unary function or the bounded `static_lambda.py` form; it can pass through function parameters or source-only
aliases in circuit blocks and lexical lets. Array operands name a parameter
or earlier local. There are at most sixteen gates across the entire
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
The expression leaf is one existing wire, one `+` or `.*` gate, a call to
one of the pure functions above, or a static function alias. The binder itself
produces no relation node.
The [worked native example](../../../examples/functional/release_let4/README.md)
shows the complete two-gate lowering and exact AIR-cost comparison.

The module is part of the independent package certificate parser, separate
from production `language/` parsing and specialization. `package/context.py`
includes it in the compiler fingerprint. The certificate continues to check
the complete native gate topology, selectors, fixed root, and key under its
documented assumptions.

The [worked higher-order example](../../../examples/functional/release_higher_order4/README.md)
shows a named function passed through a `Fn` parameter and erased to two
ordinary gates. The [captured lambda example](../../../examples/functional/release_closure4/README.md)
fixes an existing wire in a unary lambda's environment and demonstrates that a
later lexical shadow does not change the capture. `static_lambda.py` parses a
bounded pure body with parentheses, nested `+` and `.*`, and lexical `let … in`
bindings. It captures free wire names at function creation, and the checker
emits only the evaluated arithmetic gates.
The same parser checks an inline lambda supplied to a monomorphic `Fn`
parameter, capturing visible wires at that call site. The
[inline native example](../../../examples/functional/release_inline_lambda4/README.md)
applies one such value twice and matches two handwritten gates.
This fragment is intentionally exact: other lambda operations and closures,
calls nested inside an argument expression, partial operations, subtraction,
and hidden effects remain outside this v2 certificate. They remain usable
through the ordinary S31 compiler and verifier; the stricter release gate admits them
only when a corresponding independent certificate is available.
