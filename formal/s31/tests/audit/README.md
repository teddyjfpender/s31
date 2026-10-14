# Executable source audit tests

`structural_derivation_lean.py` runs the generic M31 typed-tree erasure gate
over generated tuple, helper, constant, assertion, and private-input programs.
It checks compiler/Python/Lean agreement, re-sealed wrong erasures, exact
field shape, and unsupported fragments. The same generated programs also run
the `statement` mode with concrete private assignments and public statements;
wrong private values or public results are rejected. The separate native
helper/tuple fixture verifies an actual direct-Gate proof and exercises this
mode against its source package. The statement-mode theorem covers any
program admitted by the bounded Lean grammar, while native private witness
and PCS authentication remain separate obligations:

```sh
lake build s31-general-linear-structural-check
python3 tests/audit/structural_derivation_lean.py
python3 tests/audit/structural_derivation_lean.py --native
```

`--native` also compiles the same 12 source-derived normalized relations with
the production Zig direct-Gate compiler, once with and once without witness
values. It compares the compiler-owned address of every source node in both
paths and checks each **declared** M31 lane against arithmetic calculated
directly from the four handwritten source bodies. Four additional cases
exercise reduction near the M31 modulus. Twelve changed public claims and
four changed private inputs are rejected by the normalized evaluator. The
native audit separates mathematical gate validity from public-statement
binding: a changed claim can leave a valid circuit trace but makes the
compiled public words differ from the claim; the changed input to an
assertion makes the trace invalid. An altered expected intermediate is
rejected by the corpus runner. Unused packed QM31 lanes are outside the
source type and are not compared. This is a finite source-pinned compiler
regression, not a theorem about arbitrary source text, native committed rows,
or proof acceptance. The private assignment is supplied externally; the
native verifier does not authenticate that particular assignment.

`general_linear_public_abi.py` checks three source-derived certificate
fixtures against exact `.s31` bytes, ABI, assignment, and 32-byte public word
files. It includes two public inputs, a private input, zero padding, and 36
rejection controls for arithmetic, constants, assertions, proof mode, circuit
name, and ABI. A source and relation renamed together remain accepted because
this Lean gate does not recompute the certificate's SHA-256 fields. Build the
runtime gate first:

```sh
lake build s31-general-linear-public-abi-check
python3 tests/audit/general_linear_public_abi.py
```

## General structural M31 to native witness check

`scripts/general_structural_native_witness.py` checks **one supplied program
and assignment** through the exact-byte Lean structural statement gate, then
replays its accepted SSA in Python and compares every declared M31 input and
arithmetic node against the value-carrying Zig direct-Gate compiler. It checks
an independently calculated source-to-canonical ID map through CSE, identity
erasure, and constant folding against the compiler's source-name map,
gate opcode/operand addresses, witness values, and eight public output words.
The native runner also compares every primitive gate list, permutation roster,
output address, constant allocation, and compiler map between value-carrying
and witness-free compilation. Each canonical packed arithmetic node must own
exactly one gate in its compiler span, except literal-zero addition, which
must alias the other operand and emit no gate. Rejection controls inject a
redundant satisfying gate and alter a gate operand.
Independent source-pinned replays enumerate input packing, each source node's
canonical allocation and gate or justified erasure, each assertion's masked
Eq, public `outputWord` conversions, eight reserved output copies, and constant
finalization. The binding replay checks the first-use inverse-unit constants
and exact fresh addresses for lanes one through three. A coherent extra
conversion gate and a satisfying wrong output copy are rejected even when all
gate equations and padded AIR cells are valid.
It snapshots all seven artifacts before either checker runs and recomputes
the source/relation/ABI digests, which the Lean parser checks only for shape.

```sh
python3 scripts/general_structural_native_witness.py \
  program.s31 typed-structural-derivation.json \
  source-relation-certificate.json relation.json public-abi.json \
  assignment.json public-statement.json
python3 tests/audit/general_structural_native_witness.py
python3 tests/audit/native_assertion_focus.py
python3 tests/audit/native_source_node_focus.py
```

The assertion focus command runs the Zig graph export and independent replay
over twelve honest source cases, then checks that a satisfying `Eq(0, 0)`
substitution drops the nontrivial `assert_eq(out, private_z)` condition yet is
accepted with only the assertion replay disabled and rejected with it enabled.
It does not replace the Lean byte gate in the general audit.
The source-node focus command checks twelve honest Zig exports and two hostile
graphs. One changes a canonical opcode without changing native gates. The
other coherently inserts an unused broadcast constant at the first source
address, shifts all subsequent addresses, rebuilds finalization and padded
rows, and passes the older checker with only source-node replay disabled.
The new replay rejects both.

The admitted subset is the existing Lean structural **effects** profile with
one to four M31 lanes and at most eight public words. Its indexed SSA admits
add, subtraction, pointwise multiplication, add/multiply constants,
assertions, static tuples, and bounded helpers. The source, tree, certificate,
relation, ABI, assignment, and statement must all pass the general Lean gate.
Only declared lanes are compared; remaining packed QM31 lanes have no
source-level meaning. The native comparison is assignment-specific. It does
not prove that Python and Zig agree for every accepted text, authenticate the
externally supplied private assignment in a proof, establish committed AIR row
correspondence,
or prove PCS/FRI soundness. The Lean `checked_statement_sound` theorem covers
source/evaluator semantics conditional on the Lean gate; the native address
and value checks are executable evidence at the remaining compiler seam. The
two compiler modes could still share a source-independent error in the
source-pinned replay or export. This remains short of a universal native
compiler correctness theorem.

`general_linear_ssa_effects_certificate.py` runs the strict Lean effects
certificate gate on the production affine/assertion fixture and rejects
arithmetic, assertion, JSON-canonicalization, and size mutations. Build and
run from `formal/s31`:

```sh
lake build s31-general-linear-effects-certificate-check
python3 tests/audit/general_linear_ssa_effects_certificate.py
```

`test_source_function_check.py` exercises the optional Lean
`s31-source-function-check` executable against production S31 text
compilation and the independent Python source parser. It checks exact
canonical relation bytes for 96 programs and rejection of source, relation,
formatting, reserved-name, and shadowing mutations.

Run from `formal/s31` after building the executable:

```sh
lake build s31-source-function-check
python3 -m unittest discover -s tests/audit -p 'test_source_function_check.py' -q
```

The test samples the compiler boundary; the theorem in
`S31/Gadgets/Functional/Correspondence/SourceFunctionBytes.lean` establishes
the mathematical source, normalized-name, and packed-row relationship for
every program the bounded Lean parser accepts.

`native_canonical_digest.py` builds two fresh direct-gate packages: five-lane
subtraction and reversed-operand addition. It first requires the Lean audit
to accept source, normalized relation, and compact canonical IR bytes. It
then hashes those bytes and compares the result with each package's native
cost report and verification key. This covers the unsorted subtraction and
sorted commutative paths in the native canonicalizer. It does not prove the
native SHA-256 implementation or verifier correct.

```sh
python3 formal/s31/tests/audit/native_canonical_digest.py
```
