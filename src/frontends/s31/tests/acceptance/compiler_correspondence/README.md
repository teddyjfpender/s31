# Generated source to native proof samples

## Strict release of composed functions

`functional_release.py` builds the checked-in
[`release_square4`](../../../examples/functional/release_square4/README.md)
function and handwritten form under `direct-gate`. Their normalized relation,
canonical IR, raw and padded rows, preprocessing, public binding, finalization,
and FRI settings must agree. The independently checked v2 certificate covers
the function source and native gate topology. The functional package proves
`2·x²` for four public lanes, its native verifier accepts, `verify-release`
accepts from a pinned package snapshot, and a changed public claim fails.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/functional_release.py
```

This is a bounded acyclic-function certificate and native regression. It does not
prove arbitrary functional source compilation or the underlying STARK
cryptographic assumptions.

`subtraction_release.py` checks the
[`release_sub4`](../../../examples/functional/release_sub4/README.md)
helper against a handwritten three-gate program. It preserves ordered
subtraction through the independent source checker, compares the complete
native AIR cost and fixed root, proves `-2*x` in four lanes, admits that proof
through the five-pin release command, and rejects a changed public claim.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/subtraction_release.py
```

`subtraction_optimized_release.py` checks opt-in v3 reuse of the same ordered
subtraction. Four source operations become three native gates; the resulting
canonical IR and native AIR cost match a handwritten three-gate program. Its
proof passes strict release verification and a changed public statement fails.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/subtraction_optimized_release.py
```

`optimized_release.py` builds the checked-in
[`release_optimized4`](../../../examples/functional/release_optimized4/README.md)
program in explicit v3 mode. Five source lets produce four native arithmetic
gates through commutative sorting and reuse. Both repeated results feed the
output; its canonical IR and full AIR geometry match a handwritten four-gate
package. The test admits a native
proof through five-pin `verify-release`, rejects a false result, and rejects
certificate schema downgrade and unknown schema markers.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/optimized_release.py
```

`functional_optimized_release.py` applies the same package, cost, proof,
five-pin release, false-claim and downgrade checks to three pure helpers.
Two live calls of `mix(x)` expand to seven normalized arithmetic nodes but
reuse four native gates. The helper body writes `double(a) + square(a)`
directly; a 24-case pure differential corpus additionally checks nested
expression order, helper repetition and function aliases against the
production frontend and handwritten canonical IR.

```sh
python3 -m unittest src.frontends.s31.tests.python.test_optimized_functional_correspondence
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/functional_optimized_release.py
```

`lexical_release.py` repeats the package, cost, proof, release-verifier and
changed-claim controls for the checked-in
[`release_let4`](../../../examples/functional/release_let4/README.md)
program. Its scoped source binder produces no relation node; the direct form
names the same anonymous multiplication wire `_s31_0` explicitly.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/lexical_release.py
```

`higher_order_release.py` checks a named function value passed through a
lexical binding and a monomorphic `Fn` parameter. It compares the complete
normalized relation, canonical IR, and native AIR geometry with a handwritten
two-gate program, then proves, runs `verify-release`, and rejects a changed
public claim. The function value itself contributes no gate or AIR row.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/higher_order_release.py
```

`closure_release.py` checks an explicitly captured wire in a unary lambda,
passes that lambda through `Fn`, and shadows the captured name in a later
lexical `let`. The independently reconstructed four-gate relation, canonical
IR, and native AIR geometry must equal the handwritten source. The native
proof and strict release verifier accept the true result and reject a changed
public result.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/closure_release.py
```

`inline_lambda_release.py` passes a lambda directly to a monomorphic `Fn`
parameter and applies it twice. Its two-gate normalized relation, canonical
IR, and native AIR geometry must equal the handwritten `x²; x⁴` program. The
proof passes strict release verification, and a changed public result fails.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/inline_lambda_release.py
```

`curried_release.py` checks a helper that computes a gate, returns a closure
capturing its result, and applies it with `make(x)(x)`. The independently
reconstructed two-gate relation, canonical IR and native AIR geometry must
match the handwritten program; a real strict release proof passes and a changed
public result fails.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/curried_release.py
```

`nested_release.py` checks `identity(make(x))(double(x))`. The nested function
and array arguments must leave exactly the three handwritten arithmetic gates
in the same order. It compares complete normalized relation, canonical IR and
native AIR geometry, accepts a strict release proof and rejects a changed
public result.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/nested_release.py
```

`helper_composition_release.py` checks a helper whose body passes both an
inline captured `fun` and a nested array call to another helper. The native
package must contain only the two direct addition gates, pass strict release
verification, and reject a changed public result.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/helper_composition_release.py
```

`generated_native_subset.py` selects four sources from the pinned 384-source
mutation corpus: one gate; eight alias-spelled gates with an earlier return;
fifteen gates with a final return; and sixteen comment-spelled gates with an
earlier return. It evaluates the generator's positional DAG independently of
both S31 parsers, compares every generated instruction (including eager dead
ones) to the certificate and package, builds each source through the production
direct-Gate path, proves the computed claim, verifies it natively, and requires
rejection of a changed public word.

The fast `--static` path also requires rejection of ten changes to the
generator's operations, returned gate, or eager dead suffix. It checks the
production parser against the independently enumerated positional instructions
before starting a native build.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/generated_native_subset.py --static
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/generated_native_subset.py
```

Use `--work PATH` to retain packages, proofs and trial reports for inspection.
The full corpus remains a fast parser, normalizer and exact-schedule comparison
in `tests/python/generated/test_source_mutation_correspondence.py`. These
samples test the native path; they do not prove parser or emitter refinement in
Lean, nor the underlying PCS/FRI soundness assumptions.

## Static tuple direct-Gate rows and fixed root

The static tuple native-row control admits one all-public two-input source
through independent Lean source and assignment parsing, the complete
source-derived direct-Gate fixed row replay, native fixed-column
recommitment, and an accepted proof carrying that same fixed root. Mutating
the proof root or source projection must fail. It uses at most eight Zig
build jobs and does not claim arbitrary proof-opening authentication.

```sh
cd formal/s31 && lake build s31-general-linear-effects-package-check && cd ../..
python3 -B src/frontends/s31/tests/acceptance/compiler_correspondence/static_tuple_native_rows.py
```

## Pinned square4 fixed-root binding

`native_fixed_root_binding.py` checks the complete 512-row, eight-column
direct-Gate fixed roster against the binary native fixture, the physical-row
report, and Lean's `PinnedFullFixedRoster` literal. It also checks that all 512
address-indexed output values in `PinnedSquare4ConstantValues` agree with the
physical main rows, and that the Lean main witness names the pinned native
preprocessed root. Four one-cell/root controls must fail.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py --native
```

The second command builds a fresh source-bound native package in a temporary
directory. It rechecks the package's exported fixed cells and key root against
the pinned fixture, proves the square4 claim, verifies it with the generated
native verifier, changes one byte in the proof's serialized preprocessed root,
and requires `InvalidPreprocessedRoot` from that verifier. The comparison and
mutation are reproducible diagnostics. They do not independently recompute the
Blake2s PCS root from circle evaluations or prove that all authenticated proof
openings equal the uncommitted physical-row export.

## Complete modeled direct-Gate roster on four programs

### Case07 fixed-root and accepted-proof join

`alias8_fixed_root_recommit.py` takes the exact case07 8×512 fixed-column
diagnostic whose constant island is checked by Lean, admits it against the
source-derived row schedule, and sends those literal cells to
`inspect-fixed-root-from-columns`. The native command commits the supplied
canonical M31 columns through the production PCS preparation and Blake2s
Merkle path. The same source-bound package then proves the source-derived
four-lane assignment. After its generated verifier accepts the proof against
the sealed key and public statement, the regression decodes commitment 0 with
the bounded direct-Gate proof parser. The recommitted root, sealed key root,
and decoded proof root must all agree. A changed selector, source address,
constant multiplicity, column order, noncanonical word, and short column all
fail their expected controls. A one-bit change to the *decoded root value*
must fail the three-way comparison; it does not create or submit a forged
proof. The optional `--package PATH` reuses a built case07 package.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/alias8_fixed_root_recommit.py
```

The expected root is
`791ada776d80d9b30c5b0217cae11135c67658e1822296564efe3e591cb62ef8`.
The four valid 4,096-cell mutations (`selector`, `source_address`,
`island_multiplicity`, `column-swap`) must each change the root;
`noncanonical` and `short-column` must be rejected before commitment.

This joins the case07 source-derived 8×512 fixed schedule to the native
recommitment, the sealed verification key, and one separately accepted proof's
first commitment. It is a fixture and proof-byte regression. The native
command accepts explicit untrusted columns; the comparison does not prove
Merkle binding, PCS opening authentication, or FRI.

`four_case_fixed_root_join.py` repeats this root join for the selected
one-, eight-, 15-, and 16-gate source programs. For each case it rebuilds a
source-bound package, checks its fresh full 512-row diagnostic against the
independent source schedule and pinned native fixture, recommits all 4,096
fixed cells through the production PCS path, and joins that root with the
sealed key, fresh topology, and one proof accepted by the generated verifier.
It also changes a single byte in that proof's fixed root and requires
`InvalidPreprocessedRoot`, then checks cell, column-order, canonicality, and
shape controls through the same recommit command. Use `--case case00` for a
short single-case run or omit it for all four:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/four_case_fixed_root_join.py --case case00
```

These are four finite public-source regressions; they do not establish a
general compiler correspondence theorem or authenticate arbitrary proof
openings to the displayed rows.
On 2026-10-12, the fresh four-case run accepted four proofs, joined each
4,096-cell recommitment to its sealed key and proof root, rejected all 24
fixed-column controls, and rejected all four one-byte proof-root changes at
`InvalidPreprocessedRoot`.

The 2026-10-12 fresh native run passed: all three roots were
`791ada776d80d9b30c5b0217cae11135c67658e1822296564efe3e591cb62ef8`;
the generated verifier accepted a 55,911-byte proof (SHA-256
`78c032715cd56be1d3f71e725ee11a75d89d04146a51f47a527c4cca20b58548`).
The decoded-root mismatch and all six fixed-column controls were rejected.
These are observed bytes from that local trial, not a cross-build guarantee.

### Four-case full-roster checks

`full_native_roster.py` checks a 1-gate direct multiplication, an 8-gate
alias-spelled program that returns gate 4, a 15-gate direct program, and a
16-gate comment-spelled program that returns gate 8 while later gates are still
computed. `--plan-only` checks all four source/schedule plans against the
earlier native fixed-column digests without building packages or reading
physical-row fixtures. For each full diagnostic it evaluates the generator's positional source DAG
and uses the host-side `package.direct_gate_schedule` model to construct all
512 fixed rows. That schedule is also used by the package correspondence
checker; it is separate from the Zig native emitter, but is not a second
independent host-side implementation. The diagnostic separately reconstructs
the source, input, and output row roles using the finite witness checker in
`formal/s31/scripts/check_early_return_nonvacuity.py`, which also supplies
its host-side nine-root arithmetic model. It checks that the remaining
constant/padding rows partition the physical trace; verifies every fixed cell,
all 4,608 local arithmetic roots, seed/basis/inverse values, a single coherent
address-to-QM31 value map, public copy values, and exact Gate event balance
with the native direct profile's nine public feeder uses. The checked-in
diagnostic exports are cross-checked against the earlier source-cell snapshot's
fixed-column digest and preprocessed root. Seven export/key mutations plus
one extra-feeder ledger control per program must be rejected.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --plan-only
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --native
zig build --build-file src/frontends/s31/build.zig test-public-physical-guard
```

`--native` builds all four source-bound packages, checks each package certificate,
compares `inspect-topology` with the sealed topology and verification key,
then compares fresh `inspect-physical-rows` output byte-for-byte with the
checked-in diagnostic exports. `--native --write` is only for intentional
fixture refreshes after inspecting compiler changes. `--work PATH` retains
packages and assignments for debugging. Each case also produces one honest
proof, requires its generated native verifier to accept it against that
package's sealed key, and requires `InvalidInteractionNonce` for an exact,
canonical M31 change to the named public result with the same proof and key.
The changed public word enters the verifier transcript before the interaction
nonce check, so these deterministic proof/statement bytes check transcript
binding at that point. A changed transcript could by chance pass that nonce
check and fail later, so the named error is a pinned regression result rather
than a universal verifier rule. The native run reports proof byte counts and
hashes. The fresh-native path invokes both physical inspection commands with a
nonempty private assignment and requires both to return
`PrivatePhysicalRowsUnavailable` before writing diagnostic rows. It builds the
existing private-input `named_square4_manual.s31` package and requires its
two physical inspection commands to fail with `UnsupportedPhysicalRowInspection`
without returning fixed columns, main columns, or a main root.

For each of the four accepted proofs, the native path also calls
`inspect-physical-root` on the same public assignment. It parses only the
bounded direct-Gate proof header after the generated native verifier accepts
that exact proof. Proof commitment 0 must equal the package's sealed fixed
root; commitment 1 must equal the reported main root. SHA-256 of the 12×512
canonical M31 main words, serialized column by column as little-endian `u32`,
must equal the root diagnostic's digest. The ordinary `--native` path separately
requires that digest to match the checked-in fixture's rows, then compares the
entire fresh export byte-for-byte. `--native --write` binds its fresh rows before
refreshing fixtures and preserves the deliberate refresh workflow. The result
reports both proof roots and the main-row digest per case.

The physical-row command is limited to transparent, public-only four-lane M31
programs with 1–16 add/multiply source nodes and no assertions. It exports
uncommitted fixed and main evaluations from `writeBase`. Even if a native
proof verifies, this export does not authenticate PCS openings, prove LogUp
soundness, or establish a verifier-to-trace correspondence theorem. The proof
acceptance checks authenticate the proof against its sealed key and public
statement. The main-root comparison binds these public exported base rows to
the commitment root in those separately accepted honest proofs. It does not
establish that arbitrary prover-supplied openings equal the exported rows,
prove collision resistance, or supply a general verifier-to-trace theorem.
The Zig guard tests require rejection of a private input, a nonempty private
assignment, wrong input and output shape, assertions, constant/repeat nodes,
and a 17-node source.

## Public main commitment from serialized rows

The `inspect-physical-root ASSIGNMENT.json` command is limited by the same
public-only source and assignment guard. It takes the 12×512 `writeBase` main
columns, installs the source's preprocessed tree as commitment tree 0, then
commits the main columns as tree 1 with the package's direct PCS configuration.
It also reports SHA-256 of all 6,144 canonical M31 words in column-major,
little-endian `u32` order. The digest identifies the exact uncommitted words
used by that invocation; it is separate from the PCS root.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/public_main_root_binding.py
```

The acceptance check builds and verifies a fresh `functional_square4` proof,
reads its first two postcard commitments with a strict direct-Gate profile
parser, and checks that commitment 0 is the sealed fixed root. It separately
exports `inspect-physical-rows`, matches all fixed rows to `inspect-topology`,
hashes the serialized main words, and requires that digest to equal the root
diagnostic's main-word digest. Finally it requires the recommitted main root
to equal commitment 1 in the accepted proof. Altering one exported M31 cell
changes the digest; altering one proof main-root byte is rejected by the
native verifier at `InvalidInteractionNonce` for this pinned trial.

This connects one honest public `writeBase` export to the main commitment in
one accepted proof, conditional on SHA-256 and the backend's PCS commitment
implementation. It does not establish that arbitrary prover-supplied openings
equal the exported rows, prove collision resistance, or cover private/mixed
programs. The source compiler and PCS verifier remain separate proof
obligations in the broader correspondence claim.

## Source-derived full main trace for direct Gate

`package.direct_gate_main_correspondence` reconstructs the full 12×512 main
columns from the compact normalized source, four public input words, and the
independent fixed schedule. It evaluates every compact add, ordered
subtraction, or pointwise multiply, including a returned earlier wire after
later lets and v3 common-subexpression sharing. The four public input scalars
and the constant basis/inverse words anchor the fixed Gate graph. It solves every other address
from the selected operation and checks the seed rows, packed input, every
source SSA word, public output copies, and all 6,144 input/output cells.
The model never reads native main words to derive its expected columns.

```sh
python3 -m unittest src.frontends.s31.tests.python.test_direct_gate_main_correspondence
python3 src/frontends/s31/tests/python/check_optimized_native_package.py
```

The pure test compares this reconstruction with four older complete native
exports and rejects altered cells, column order, claims, and digests. The
optimized native test uses the reversed/CSE `reverse_share` source with four
source lets but three compact gates. It compares all 6,144 source-derived
main words and the eight source-derived public words to fresh native exports.
The diagnostic's SHA-256 digest must equal the source-derived main bytes. It
then requires the diagnostic's main PCS root to equal commitment 1 in the
exact proof accepted by the generated native verifier. A changed main-root
proof byte and a changed public claim are rejected by that verifier; changed
export cells and swapped columns fail the independent trace comparison.

The reusable [pinned public trace audit](../../../tools/audit/README.md) performs
the same complete reconstruction for any source admitted by the strict public
four-lane release checker. The `subtraction_release.py` and optimized v3
acceptance cases run it on ordered subtraction. It compares every fixed and
main cell from the native export with the independent source schedule, checks
the public words and serialized main digest, and recommits the source-derived
main columns through the native PCS. Both that root and the export's reported
root must equal the exact proof's main commitment. A changed source-derived
cell changes its root. Both trace inspection commands reject a nonempty
private assignment before exporting any rows or roots.

This is a finite, honest-prover source-to-main-commitment regression under the
native exporter and PCS commitment implementation. It does not authenticate
arbitrary query openings as these 6,144 cells, prove collision resistance or
FRI/LogUp soundness, or cover private and mixed profiles. The v3 checker is
still an explicit opt-in. The separate `optimized_release.py` fixture checks
the generated v3 package through strict release admission.

## Resealed source-row adversarial controls

`projected_row_adversarial.py` builds the pinned eight-gate alias source and
requires its unmodified package to pass both the direct-Gate correspondence
checker and package admission. It then copies the package twice. One copy
changes the first source row's add selector to a pointwise-multiply selector;
the other swaps the complete fixed cells at the first two source row positions.
Both copies update the topology artifact SHA-256 in `manifest.json`, and the
test checks every listed artifact digest before admission. Both admissions
must fail specifically at `emitted direct-gate selector/address columns differ
from gate replay` (the source-derived native-gate to fixed-column comparison),
not at a stale file hash or certificate check.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/projected_row_adversarial.py
```

The source-row positions come from the pinned positional DAG's independent
schedule. This controls package admission of changed, uncommitted topology
exports. The generated verifier consumes its embedded source and key, not
`gate-topology.json`; the test does not claim that these forged packages are
valid proofs or that it authenticates arbitrary PCS openings.
