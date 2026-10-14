# Functional source examples

These programs exercise static function specialization. The normalized
relation contains first-order arithmetic nodes; function values themselves
do not occupy circuit wires. Each release example has a handwritten source
and a native acceptance driver that compares AIR geometry and verifies a
proof under the bounded direct-Gate correspondence certificate.

| Example | Main property |
| --- | --- |
| [`release_square4`](release_square4/README.md) | Composition of named pure functions. |
| [`release_let4`](release_let4/README.md) | Lexical `let` erasure. |
| [`release_higher_order4`](release_higher_order4/README.md) | Named function value passed through `Fn`. |
| [`release_closure4`](release_closure4/README.md) | Captured lambda and shadowed lexical name. |
| [`release_inline_lambda4`](release_inline_lambda4/README.md) | Inline lambda argument. |
| [`release_curried4`](release_curried4/README.md) | Returned closure and curried call. |
| [`release_nested4`](release_nested4/README.md) | Nested function and array arguments. |
| [`release_helper_composition4`](release_helper_composition4/README.md) | Nested calls and captured lambda in a helper body. |
| [`release_optimized4`](release_optimized4/README.md) | Checked commutative gate sharing with both results used. |
| [`release_functional_cse4`](release_functional_cse4/README.md) | Two live pure helper calls share the same four-gate circuit. |
| [`pattern_parameters`](pattern_parameters/README.md) | Product destructuring in function parameters. |
| [`static_fold`](static_fold/README.md) | Captured Horner left fold with exactly the handwritten canonical IR and native AIR geometry. |

The static fold uses the ordinary text frontend and native proof acceptance;
the bounded independent direct-Gate release certificate does not yet cover
this combinator.

[`reshape_flatten_zero_cost`](reshape_flatten_zero_cost/README.md) measures a
runtime three-row reshape and flatten against a direct selection and an
expanded slice/concat circuit. The first two have exactly matching native AIR
geometry; the expanded form records 41 additional raw QM31 rows.

The v2 correspondence checker is conservative about operand order and
repeated gates. The last two optimized examples explicitly select v3; both
are restricted to a public four-lane direct-Gate circuit. The certificate
checks source-to-relation and native gate topology for those examples; it is
not a proof of the entire Python frontend or STARK cryptography.
