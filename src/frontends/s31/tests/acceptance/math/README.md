# Math native acceptance

`power_chain.py` compares four eight-lane `pow<65535>` calls with an explicit
binary multiplication schedule. It derives each circuit's output exponent
from its complete normalized multiplication graph, calculates eight expected
field values independently, proves both native circuits, verifies their
claims, and rejects changed public results. It pins 76 versus 120 source
nodes, 471 versus 559 raw QM31 rows, and 512 versus 1,024 padded rows.
The [worked source](../../../examples/arithmetic/powers/README.md) explains
the saved-power identity and includes the two programs.

`field_subtraction.py` checks that dynamic field subtraction emits one native
subtraction relation node and fewer native QM31 rows than the prior
negation-plus-add form. It compares two
independently calculated four-lane assignments, proves both forms, verifies
all four proofs with their generated native verifiers, and changes each public
claim to require rejection. The fixture's padded trace remains 512 rows, so
its gate reduction is a raw-gate saving rather than a claimed proving-time
speedup.

`field_subtraction_partial.py` compiles a five-lane subtraction both directly
and through a named functional helper. It requires identical normalized IR,
selected profile, raw and padded rows, preprocessing, public binding, and FRI
settings. The fifth lane occupies the only active position in the second
packed row. A separate bounded source parser independently checks the
functional package's source bytes, normalized relation, public ABI, and
manifest identities; this check has `source-to-relation-only` scope. The
functional package's generated verifier must accept the honest
proof and reject public mutations of both the first and fifth output lanes.
The script reports AIR geometry and checks expected values with an independent
modular calculation.

`addition.py` generates a checked-addition source for each of the ten nominal
integer types (`u8` through `u128` and `i8` through `i128`). It checks the
signedness/width tag and three-node relation shape, uses an independent Python
integer oracle at zero, near the upper limit, across limb carries, and at the
signed minimum, then builds a `sparse-wide-gate` or `direct-gate` package for each type. Each
native run accepts the honest near-limit proof, rejects a changed public
result, and rejects an overflowing prover assignment. The last rejection is
at the prover/evaluator boundary; it is not a forged STARK proof. Use
`--source-only` for the subsecond parser/oracle loop or `--case i32` for one
native profile. The complete native matrix is:

```sh
python3 src/frontends/s31/tests/acceptance/math/addition.py
python3 src/frontends/s31/tests/acceptance/math/addition.py --lowering direct-gate
```

The direct arithmetic path proves byte and limb ranges with Boolean gates
inside the QM31 component. Its accepted checked-addition circuits contain no
generic equality or 16-bit lookup conversion gates. Compare the native matrix
reports before drawing a performance conclusion; `paired.py` in
`benchmarks/fixed_integer_addition/` measures the same witnesses under both
profiles with proof-of-work separated from the recorded proving stages.

`direct_binary.py` checks checked subtraction and signed/unsigned `<=` at
every width against the independent integer oracle. Add `--native --case i128`
to build and prove both operations under `direct-gate`, verify the honest
statement and changed-claim rejection, and require a checked-subtraction
underflow assignment to fail at the native prover boundary. The default
source-only run covers all 20 operation/type combinations in under a second.

`multiplication.py` checks signed and unsigned wrapping products at 8, 32,
and 128 bits, plus checked products at 8, 32, and 128 bits. It recalculates
every expected result with Python integer arithmetic, checks the lowered
width-tagged node, pins AIR geometry, builds the sparse-wide AIR, accepts a
native proof, and rejects a changed public product. Checked cases also reject
an independently constructed overflow witness in the oracle. Zig circuit
tests confirm that the emitted constraints reject overflow, including signed
`MIN * -1`, and reject a byte operand outside its declared range.

`direct_multiplication.py` covers checked and wrapping source semantics for
all ten types and uses the independent Python integer oracle for each. With
`--native`, it builds arithmetic-only `direct-gate` packages, accepts honest
proofs, rejects changed public products, and requires checked overflow to
fail at the native prover. Use `--case u8 --mode checked --native` for a
short feedback loop, then run the all-width matrix once compiler source is
stable. The direct gadget uses bounded digit convolution and has its own
[constraint design](../../../../../../design/s31/language/DIRECT_FIXED_INTEGER_MULTIPLICATION.md).

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/math/multiplication.py
```
