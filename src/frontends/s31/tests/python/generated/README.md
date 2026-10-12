# Generated functional source gate

`test_functional_generated.py` creates 96 deterministic, well-typed S31
programs from a small independent expression grammar. Each program uses a
higher-order helper, a capturing closure, lexical `let`, field arithmetic and
witness-dependent `if`. The generator evaluates the source tree directly with
Python modular integers. The S31 relation oracle separately evaluates the
compiler's emitted graph for both selector values and several boundary input
values; forged public results must fail. Every functional program also has an
explicit first-order form, and the two must produce **identical relation IR**.
The same 96 terms also compile with immediate `(fun …)(argument)` application;
that third source form must emit the same relation and therefore inherits the
independently checked values and forged-output rejection.

`test_functional_arrays_generated.py` adds 64 deterministic four-lane array
programs. Its independent source evaluator covers pointwise addition and
multiplication, rotation through `drop`/`take`/`concat`, nested `let`, shadowed
lambda parameters and witness-dependent `if`. Each program has a functional
closure form and an explicit first-order form; the gate compares their entire
normalized relations and checks six concrete assignments plus forged outputs.
The array corpus has its own pinned SHA-256 identity and seed.

`test_functional_packing_generated.py` exercises array lengths 1, 2, 3, 4,
5, 7, 8, 9 and 15. Each program uses a capturing closure, a static higher-order
call, pointwise arithmetic and a total witness-dependent conditional. The
functional and first-order forms must emit identical normalized IR, while an
independent integer evaluator checks both selector values, field wrap and
forged-output rejection. A separate native gate builds both forms at lengths
3, 5 and 9, compares circuit/AIR geometry, and verifies two proofs per length.

`test_functional_library_generated.py` adds 20 deterministic four-lane math
programs across polynomial evaluation, dot product, matrix-vector and matrix
multiplication, and field powers. Nine more programs cover Poseidon2 leaves of
4, 8, 12 and 16 words and a two-leaf parent. Functional closure calls and
explicit direct forms must produce identical normalized relations. Independent
modular arithmetic and the pinned Poseidon2 reference calculate expected
outputs; changed claims must fail. The 29-source corpus has a pinned SHA-256
identity. These are source/value gates; only the existing acceptance cases
compare native AIR geometry and proofs.

`test_tuple_generated.py` adds 40 deterministic source products, including
nested pairs and chained projections. Each program computes two independently
generated scalar terms and selects a projected component with a constrained
public bit. A third source form destructures the tuple with a pattern and
must emit the same relation. The source evaluator computes the expected value
without reading compiler internals. Functional and first-order sources must emit identical
relation IR; both bit values, field boundaries, random inputs and false public
claims are checked. The three-source corpus has a pinned SHA-256 identity.

`test_higher_order_generated.py` adds 160 programs from 16 independently
evaluated arithmetic trees. Ten source routes for each tree cover named
functions, first-class function arguments, returned functions, curried
closures, captured lambdas, local function bindings and lexical shadowing.
Each route must emit the **same entire relation** as its direct expression.
Both selector values, field boundaries, random inputs and forged public
outputs are checked. A partial inverse carried through each route must be
rejected in an inactive conditional arm. The corpus seed and SHA-256 identity
are pinned in the test.

`test_product_control_generated.py` adds 48 nested nominal-record programs.
Each selects three M31 leaves with a computed Boolean value. Whole-record and
handwritten fieldwise sources must have identical complete relation JSON. A
separate modular-integer evaluator checks three assignments per source,
including both selector values and field wrap; the strict typed public ABI is
flattened independently and a forged result must fail. The seed and
two-source corpus SHA-256 are pinned in the test.

`test_static_enum_effect_generated.py` adds 112 static-enum programs over
array lengths 1–7, addition and multiplication, both positions of a dynamic
conditional, and four routes through a direct helper, relay, constructor
factory, or captured lambda. Each must have the exact normalized relation of
a handwritten arithmetic conditional. Independent M31 calculations check
both bit values and reject changed public outputs, including zero and field
wrap inputs. Sixteen negative programs require rejection when the selected
static arm or an eagerly evaluated constructor payload contains an inverse
inside a dynamic conditional. The two-source corpus digest is pinned. The
[native one-lane gate](../../acceptance/functional/static_enum_if.py) separately
checks AIR cost and proof verification; this corpus checks source lowering.

A second gate perturbs valid source text and requires located diagnostics for
rejected mutations. Deep expressions and function types must hit explicit,
located nesting limits. The scalar corpus is deterministic (`SEED = 0x531F00D`);
its two-source SHA-256 identity is pinned in the test. The corpora need no
third-party fuzzing dependency. They cover this functional subset, not the
full standard library or production AIR emission. Native proof and AIR
geometry gates live in `tests/acceptance/` and run in CI.

`test_language_mutations_generated.py` extends the robustness gate to seven
checked-in programs spanning functions, records, arrays, hashes, and
fixed-width integers. It makes 280 deterministic token mutations and requires
each result to compile or fail with a source line and column. The corpus digest
and accepted/rejected counts are pinned. This catches uncaught parser or
elaborator exceptions; it does not establish semantic preservation. Another
84 formatting variants insert whitespace or comments at token boundaries and
must emit the exact same normalized relation, so source trivia has no circuit
cost.

`test_direct_alias_correspondence_generated.py` adds 512 deterministic
programs in the independently checked direct-gate fragment. It builds a
positional arithmetic DAG, spells it with aliases and parentheses, and
compares the independent source parser with the production compiler. A direct
spelling must produce identical normalized relation, canonical IR bytes, and
the independently modeled native gate schedule. The corpus spans one through
sixteen gates, including programs that return an earlier value while later
arithmetic remains in the eager body, and pins the SHA-256 digest of both
spellings. Retargeted output
aliases must change the verifier identity and gate schedule; duplicate names
and forward references must fail closed. This checks the bounded direct-gate
profile, not the full functional language or native proof execution.

`test_source_mutation_correspondence.py` adds a separate 64-graph,
384-source corpus with a pinned SHA-256 digest. Six spellings per graph cover
comments inside expressions, ASCII whitespace, parentheses, zero-cost alias
lets, internal producer renaming, and eager arithmetic after an earlier
returned wire. For every admitted source it compares the independent bounded
parser with the production compiler, then compares canonical IR bytes and the
exact positional native gate schedule across equivalent spellings. Targeted
boundaries include invalid syntax, valid S31 forms excluded from certification,
the 16,384-byte and 256-token limits, and the 128-character producer-name
limit. A handwritten three-gate example checks that a dead later calculation
still occupies an arithmetic row and that retargeting the public return changes
the verifier identity. This is a fast Python-only differential gate; native
proof execution and general compiler correctness require separate checks.

Run with the normal Python suite:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py'
```
