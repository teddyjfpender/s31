# Generated source to native proof samples

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

### Case07 fixed-root recommitment

`alias8_fixed_root_recommit.py` takes the exact case07 8×512 fixed-column
diagnostic whose constant island is checked by Lean, admits it against the
source-derived row schedule, and sends those literal cells to
`inspect-fixed-root-from-columns`. The native command commits the supplied
canonical M31 columns through the production PCS preparation and Blake2s
Merkle path. A recomputed root must equal the sealed case07 key. A changed
selector, source address, constant multiplicity, column order, noncanonical
word, and short column all fail their expected controls.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/alias8_fixed_root_recommit.py
```

The expected root is
`791ada776d80d9b30c5b0217cae11135c67658e1822296564efe3e591cb62ef8`.
The four valid 4,096-cell mutations (`selector`, `source_address`,
`island_multiplicity`, `column-swap`) must each change the root;
`noncanonical` and `short-column` must be rejected before commitment.

This closes the case07 export-to-fixed-root diagnostic equality gap for the
pinned fixture. The command accepts explicit untrusted columns and is not a
verifier. The test does not prove Merkle binding, PCS opening authentication,
or FRI.

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
