# Direct Gate LogUp: native acceptance to exact event balance

Status: proof interface and gap analysis, 2026-10-11. This note scopes one
direct-M31 `qm31_ops` component, with no chip or private bridge. It does not
assert soundness of the installed verifier.

## What is already proved

For each logical row, the Gate events are two positive reads
`(GATE, in0Address, in0[0..4])`, `(GATE, in1Address, in1[0..4])`, and one
negative output with its fixed preprocessed multiplicity:
`-mult / combine(GATE, outAddress, output[0..4])`. The external events contain
the fixed `u` wire and pinned public outputs. Here `combine(tuple)` is
`Σ tuple[i]·alpha^i - z` in QM31; the relation id is the constant coefficient.
The native `qm31_ops` component pairs the two reads in its first interaction
column and puts the output in the final singleton column.

The existing Lean chain is substantive:

- `NativeLogUpAirProof` and `NativeLogUpBatchesProof` equate symbolic native
  Horner, single/pair residual, and three-term finalizer formulas to the Lean
  model. These are formula identities, not a proof that the production bound
  AIR evaluates precisely those formulas at every committed row.
- `Qm31GateInteraction.qm31_ops_claimed_sum` derives the component claimed sum
  from all row residuals, nonzero denominators, and a permutation of the
  logical predecessor map. `GateAirRawSoundness` removes the nonzero premise
  by counting every zero-denominator challenge pair as exceptional, including
  outputs whose multiplicity is zero.
- `GateChallengePairs` and `GateAirRawSoundness.raw_false_acceptance_card_le`
  bound false closure of a **fixed** invalid event multiset. Put
  `p = 2^31-1`, `N = p^4 = |QM31|`, `R = 2^logSize`, and `s =` the number of
  distinct events in the union of uses and yields. Provided every address is
  canonical (`< p`) and each event count on either side is `< p`, at most
  `(5s² + 2s + 3R)·N` of the `N²` ordered `(alpha,z)` pairs satisfy the
  modeled raw AIR and closure. Thus an independent uniform pair has false
  acceptance probability at most
  `min(1, (5s² + 2s + 3R)/N)`.

The three terms have different causes: at most `5s²` bad compression alphas
for six-field tuples; at most `2s` denominator or rational-numerator roots in
`z` after collision-free compression; at most `3R` zero denominators in the
raw three-lookup row equations. The count `< p` premise prevents a nonzero
integer multiplicity difference from vanishing in the characteristic. The
direct compiler should establish that premise from its fixed `computeUses`
schedule; canonical encoding of each `q7` cell alone does not establish the
total event count bound.

## Exact missing native link

The verifier at `src/frontends/s31/runtime/native_verifier.zig` checks the
proof envelope's canonical Gate claimed sum and tests
`direct_arithmetic.lookupSum(outputs, claimed, z, alpha) = 0` after drawing
the lookup challenges. It then verifies the component AIR through the PCS.
The equality of claimed sums **alone** is weak: the prover chooses `claimed`
after seeing the lookup challenge, and could set it to cancel public terms.
The AIR and commitment checks must force it to equal the row fraction sum.

The next correspondence theorem should use a decoded, authenticated native
trace as input. Its result is `GateAirRawSoundness.rawInteractionAccepts` for
exactly those rows, external events, and challenge values. Its premises must
be split so the desired conclusion is not assumed:

1. **Key and row binding:** the verifier's pinned preprocessed root fixes the
   eight `qm31_ops` columns, including addresses and multiplicities; the
   main and interaction commitments bind the 12 and 8 committed columns at
   the same `R` logical rows. The row order and `at_prev` map agree with an
   explicit permutation `prev : Equiv.Perm (Fin R)`. Four M31 coordinates
   decode each QM31 cell in the pinned basis.
2. **Native evaluator correspondence:** for every logical row, the selected
   production AIR program reads the promised fixed, main and interaction
   cells and emits exactly the two `NativeLogUpBatches` residuals, alongside
   the nine local arithmetic residuals. The direct profile has one active
   `qm31_ops` component at index 1 and one Gate claimed sum. A generated
   evaluator certificate should bind the AIR program digest, column spans,
   challenge positions, row predecessor map, and claim index.
3. **Cryptographic row-satisfaction premise:** for the pinned key and
   transcript, an accepting PCS/FRI proof implies that there exist bound
   trace polynomials whose values at every logical row make every selected
   AIR residual zero, except with a separately stated error
   `epsilon_AIR_PCS_FRI`. This premise includes commitment binding,
   Merkle/opening soundness, quotient and OODS checks, degree bounds, FRI,
   and composition randomizers. It must be stated for the actual native
   configuration, not replaced with “all rows satisfy the modeled AIR.”
4. **Public and transcript binding:** the verifier recomputes the external
   Gate terms from the pinned public values and fixed `u` tuple, checks the
   claimed-sum fold in the exact native sign/order, and draws `(z,alpha)`
   after the preprocessed and main commitments and the accepted 20-bit
   interaction PoW nonce. The interaction claim and commitment follow the
   challenge. The modeled external lists must reproduce these native terms.

One useful Lean interface is a pure `DecodedDirectGateTrace.Trace` carrying the
three column groups, `prev`, and claimed sum. First prove an equation between
the production AIR evaluator's two symbolic outputs and the model's paired
and singleton residuals **for arbitrary decoded cells**. Then a small theorem
can take authenticated all-row native residual zeros plus the verifier's
explicit public closure check to construct `rawInteractionAccepts`. The
cryptographic premise sits outside this algebraic theorem, so it remains
visible during review.

## Challenge distribution and final statement

`lookup_transcript.drawLookupElements` draws `z` then `alpha`. The Blake2s
M31 channel accepts an eight-word hash draw only when all words are below
`2p`, then reduces each word modulo `p`. In the ideal random-oracle model,
each accepted draw gives eight independent uniform M31 limbs: exactly two
accepted words represent each limb. The two QM31 challenges are therefore
uniform and independent **for one fixed transcript prefix**. This is a model
assumption about Blake2s, not a Lean theorem about the concrete hash.

The prover can choose the main commitment and an accepted PoW nonce before
the challenge, and can try multiple transcript prefixes. Let `Q` bound the
number of distinct challenge-bearing prefixes it can query or submit,
including grinding opportunities. For fixed committed rows at each prefix,
an ideal random-oracle union bound gives lookup failure at most
`min(1, Q·(5s_max² + 2s_max + 3R_max)/p^4)`, where `s_max` and `R_max`
bound every admitted prefix. Add `epsilon_AIR_PCS_FRI` and any separate
binding/Fiat–Shamir reduction errors; do not silently count the 20-bit PoW
as reducing `Q` or strengthening the lookup bound. A proof with a malformed
or noncanonical address/count is outside this theorem and must be rejected by
the key/profile admission checks.

The intended conditional security claim is: if the fixed decoded event
multiset is not balanced, a native verifier can accept only through a
lookup-exceptional challenge or through the stated cryptographic/transcript
failure events. Outside them, exact Gate multiset balance follows, and the
existing unique-producer and source-row lemmas can recover the intended
logical wire values. It is **not** a deterministic `verified → balanced`
theorem and does not cover parser correctness, other components, or a full
source-to-PCS correspondence.

## Remaining native controls

1. Export one direct proof's fixed/main/interaction row cells and the bound
   evaluator program digest; independently reconstruct both native row
   residuals at `R=16` and the accepted claimed-sum fold. Include first,
   last, and nonadjacent rows to catch predecessor-order mistakes.
2. Mutate one committed input limb or `q7` multiplicity, rebuild interaction
   columns for the mutated row values, and show the reconstructed event lists
   or residuals change. Reseal package metadata for topology mutations.
3. Change only the proof envelope's Gate claimed sum and require
   `InvalidLookupSum`; this existing native control is still pending a run.
4. Build a Lean module for the decoded-cell evaluator identity and a native
   exporter fixture. Keep the cryptographic row-satisfaction statement as a
   named, documented premise until an independent PCS/FRI review discharges
   it.

## Production evaluator obligation map

The source-only Lean interface is
[`DecodedDirectGateTrace.lean`](../../../formal/s31/S31/Gadgets/Air/DecodedDirectGateTrace.lean).
Its `fixed`, `main`, and `interaction` arrays are in **semantic column order**,
not the local read order of the captured AIR bytecode. The following map is
from the installed Zig source; the equalities to the authenticated trace
remain to be proved or independently certified.

| Lean cell | Production source and index | Obligation |
| --- | --- | --- |
| `fixed[i][0..3]` | `direct_arithmetic.Circuit` columns `qm31_ops_{add,sub,mul,pointwise_mul}_flag`, commitment positions `0..3` | Match the four `Qm31Ops.Flags` in this order and prove the key's preprocessed root binds every row. |
| `fixed[i][4..7]` | `qm31_ops_{in0,in1,out}_address`, `qm31_ops_mults`, commitment positions `4..7` | Decode canonical M31 addresses and multiplicity, including the source `computeUses` bound. |
| `main[i][0..11]` | `components.qm31_ops.row`: four input-0 limbs, four input-1 limbs, four output limbs; selected main tree span expected `0..12` | Relate the committed row to the decoded `GateLookup.Row`. |
| `interaction[i][0..7]` | `direct_arithmetic.writeInteraction`: first four limbs for the paired reads, last four for the output singleton; selected interaction tree span expected `0..8` | Decode QM31 in the pinned basis and use the last four columns at the predecessor row. |

`air.bindDirectArithmetic` selects source component index `1` (`qm31_ops`),
rebases it to proof component `0`, and its manifest advertises one claimed sum
and **11 constraints**: nine local arithmetic constraints and two LogUp batch
constraints. The source package checker expects the selected captured AIR's
local preprocessed-index vector `[0,2,3,1,4,5,6,7]`. This is a permutation
of the semantic fixed-column positions, not an identity map. `trace_lease`
uses each local index to read the corresponding global committed column.
The next certificate must verify that the captured AIR program actually
uses those local reads with the intended arithmetic flags, Gate addresses,
and multiplicity; matching a manifest vector alone does not prove evaluator
semantics. The hand-written `air_eval/manual/circuit.zig` shows the intended
nine local constraints and ordered three Gate terms, while the installed
verifier executes the pinned, rebound `STWZEVA/1` AIR bundle. Their equality
is an explicit cross-implementation obligation.

The witness's final interaction column is shifted by `claimed/R` and prefix
summed in **coset order**, then serialized in bit reversed circle order.
For a storage row `i`, the logical predecessor required by the Lean
`prev : Equiv.Perm (Fin R)` is
`bitReverse(cosetToCircle((circleToCoset(bitReverse(i)) - 1) mod R))`.
This is `previousBitReversedCircleDomainIndex(i, logSize, logSize)` in the
native utilities. The verifier requests the last four interaction columns
at the previous-row OODS point; the first four have only the current sample.
A row-index mutation should show that replacing this permutation by ordinary
`i-1` changes the residual at some row.

The `DecodedDirectGateTrace.decoded_cells_to_raw_accepts` theorem accepts
separate premises that (a) the **installed evaluator outputs** agree with
the source-extracted pair and singleton residuals at each decoded row,
(b) those outputs vanish on one trace authenticated by the preprocessed,
main, and interaction commitments, and (c) the verifier's public claimed-sum
equation matches the modeled external events. A single folded composition
evaluation does not deterministically imply eleven separate zero residuals.
The random composition coefficient, quotient/OODS check, PCS opening
binding, FRI low-degree check, and transcript challenge distribution belong
in the quantitative `epsilon_AIR_PCS_FRI` reduction. No Lean theorem here
derives (a) or (b) from the installed bundle or a proof byte string.

[`DirectGateNativeIndices.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateNativeIndices.lean)
encodes the captured AIR's fixed-column read permutation as an eight-element
equivalence. Its `local_fixed_at_semantic` lemma recovers any semantic fixed
cell from the inverse local position. It also reuses the proven circle/coset
permutation to define `directPrevious` for any even row count, conditional on
the supplied bit-reversal involution, and specializes it to sixteen rows.
`decoded_last_at_previous16` explicitly requires `PreviousMaskMatches` for
the trace. This module proves index algebra only: neither the manifest bytes
nor the installed `at_prev` mask are authenticated by these lemmas.

The two modules and the `S31.Gadgets` umbrella compiled successfully with the
pinned Lean toolchain. The source bindings and inventory regenerated and
passed the plain formal source check (56 operations, 1,266 theorem names).
The reproducible commands are:

```sh
(cd formal/s31 && lake build S31.Gadgets.Air.DecodedDirectGateTrace S31.Gadgets.Air.DirectGateNativeIndices)
(cd formal/s31 && lake build S31.Gadgets)
python3 scripts/s31_formal.py --write
python3 scripts/s31_formal.py
```

Run the latter two commands from the repository root. Native acceptance and
row-index mutation controls are separate follow-ups; this increment adds no
native exporter, and the conditional Lean bridge does not prove PCS/FRI.

## Bounded evaluator-cell replay

[`DirectGateEvaluatorCells.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateEvaluatorCells.lean)
defines a pure evaluator over the selected component's eight local fixed
reads, twelve main cells, eight current interaction cells, and eight cells
sampled with the previous-row mask. It proves, for every decoded trace, that
the local fixed read permutation reconstructs the semantic Gate row and that
the nine arithmetic and two LogUp residuals equal the existing source Gate
model. `arithmetic_zero_decodes` derives the Gate operation and output from
the nine zero local residuals. `modeled_evaluator_to_raw_accepts` requires
the installed evaluator to return these modeled residuals, authenticated row
residuals to vanish, and the public claimed-sum equation to hold. It proves raw Gate interaction
acceptance under those premises; it does not prove the premises.
The later
[`DirectGateRowBytecodeBridge.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateRowBytecodeBridge.lean)
derives the evaluator equality from the selected bytecode outputs. Native
execution and proof binding remain separate premises.

The checked fixture
[`GeneratedDirectGateEvaluatorFixture.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateEvaluatorFixture.lean)
replays `functional_square4_manual.s31` at public input `[0,1,2,7]`.
The native package exports these two selected rows:

| Trace row | Semantic flag | Local fixed flags `[add,mul,pointwise,sub]` | Main input | Main output | Multiplicity |
| --- | --- | --- | --- | --- | --- |
| 502 | pointwise multiply | `[0,0,1,0]` | `[0,1,2,7]` twice | `[0,1,4,49]` | 2 |
| 503 | pointwise multiply | `[0,0,1,0]` | `[0,1,4,49]` twice | `[0,1,16,2401]` | 4 |

An independent Python replay checks the nine M31 arithmetic residuals on
these cells and computes the two QM31 LogUp residuals using the production
six-word Gate tuple order. Lean kernel computation checks the same numeric
results. Swapping the fixed mul/pointwise reads or main output limbs makes
the arithmetic residual nonzero; swapping a first/last interaction cell
changes the paired LogUp residual. The independent package checker also
rejects resealed fixed, main, or interaction span mutations in the component
manifest; the acceptance control exercises all three cases. Changing the
previous interaction sample changes the singleton LogUp residual in Lean,
but proving the native mask selects that sample remains an obligation.
The interaction values are deliberately synthetic, so their nonzero
residuals test the equation and column order only; they are not a claimed
native witness or proof opening.

Regenerate and check the fixture with:

```sh
python3 scripts/export_s31_direct_gate_evaluator_fixture.py PACKAGE \
  src/frontends/s31/examples/arithmetic/functional_square4.valid.json \
  formal/s31/S31/Gadgets/Air/GeneratedDirectGateEvaluatorFixture.lean --check
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateEvaluatorFixture)
```

The fixture checks the manifest's exact index vector and three trace spans,
but does not independently interpret the installed bytecode. The following
sections give checked bytecode extractions and Lean polynomial identities for
all eleven roots at supplied OODS samples. Authentication of full committed
columns, random composition, PCS/FRI, and Fiat–Shamir remain separate.

## Installed Gate bytecode: arithmetic correspondence

[`GeneratedDirectGateBytecodeArithmetic.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateBytecodeArithmetic.lean)
proves the arithmetic identity at base-field row cells for the bounded
`direct-m31-v4` Gate profile. A strict exporter reads the installed
`STWZEVA/1` bundle and checks its SHA-256, selected `qm31_ops` program digest,
component position, semantic hash, section table, register order, root order,
seven challenge/claim sources, and the fixed 134 base and 97 extension
instructions. The selected program came from the official bundle with a trace
log size of 23; native binding changes the log size to 9 but preserves the
instruction stream. The generated Lean definition follows its base register
assignments through register 121. Its first nine extension roots inject the
base registers `[24, 28, 31, 34, 37, 61, 85, 103, 121]` with three zero
coordinates. [`DirectGatePolynomial.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGatePolynomial.lean)
defines the nine constraints over any commutative ring. Lean proves, for
**arbitrary** eight fixed and twelve main cells in any such ring, that the
extracted bytecode arithmetic equals those constraints. Specializing to M31
recovers `DirectGateEvaluatorCells.arithmetic` and derives Gate
operation/output correctness when all nine row residuals vanish. This is a
universal polynomial identity, rather than evidence from finitely many
vectors.

The native resident verifier evaluates the base instructions at an OODS point
using **QM31** values read from the sampled trace mask. A QM31 sample can have
four nonzero coordinates even when its source column commits to M31 rows.
[`DirectGateOodsArithmetic.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateOodsArithmetic.lean)
specializes the same identity to QM31 and models the installed `secure_col`
operation. Each of the nine roots is `fromPartialEvals(r, 0, 0, 0) = r`, so the
installed arithmetic roots equal the nine modeled polynomial evaluations for
*arbitrary QM31 samples*. For example, at OODS point `ζ`, the first root is
`add(ζ) + sub(ζ) + mul(ζ) + pointwise(ζ) - 1`; the next is
`add(ζ) · (add(ζ) - 1)`. The output roots use the same packed multiplication
polynomials as the M31 row model, evaluated in QM31. The Python opcode test
also checks three sets of nonbase QM31 fixed and main samples.

This proves a local evaluator identity at the supplied samples. The theorem
does not authenticate those samples as polynomial openings, establish the
native `traceValue` mask's correspondence to the committed columns, or infer
all-row M31 zero constraints from a single OODS evaluation. Those steps need
the production random-composition, Fiat–Shamir, PCS, and FRI arguments.

The exporter is a checked extraction step, not a verified binary parser in
Lean. CI regenerates the Lean file from a freshly built, source-checked S31
package and compares its exact bytes with the committed file. The source,
component manifest, verification key, and official bundle identities pass
`check_package` first. That checker independently recomputes the selected
Gate program binding from the official AIR bytes, component index, and pinned
part semantic hash; a resealed change to the manifest/key/report binding is
rejected before export. The formal source inventory also binds the exporter,
native bundle parser/interpreter, and official bundle asset. The proof relies
on that extraction and on the native interpreter following its documented
opcode semantics. The standalone scalar replay interprets all 11 bytecode
roots on two source rows, three nonbase QM31 OODS sample sets, and changed-cell
controls. It also rejects changed-bundle and rehashed-root-order controls.

## Installed Gate bytecode: LogUp roots and mask slots

[`GeneratedDirectGateBytecodeLogUp.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateBytecodeLogUp.lean)
is extracted from extension registers 9–96 of the same pinned program. Lean
proves that roots 9 and 10 equal the pair and running-sum equations in
[`DirectGateOodsLogUp.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateOodsLogUp.lean)
for **arbitrary QM31** fixed, main, current, and previous interaction samples.
The first equation is
`first · d₀ · d₁ − (d₀ + d₁) = 0`, where each denominator is the six-word
Gate tuple compressed with `α`, minus `z`. The second is
`(last − previousLast − first + claimedScaled) · dOut + fixed[7] = 0`.
Lean separately proves that when `d₀` and `d₁` are nonzero, the first equation
is equivalent to `first = 1/d₀ + 1/d₁`; when `dOut` is nonzero, the second
equation specifies the running-sum increment. The polynomial identities
themselves hold even at zero denominators; the reciprocal interpretation
requires these nonzero premises.

### From selected bytecode to every Gate row

The row bridge embeds each of the eight fixed, twelve main, and eight
interaction M31 cells into QM31. It proves that four lifted interaction limbs
reassemble to the same secure-field value as the row model, and that the
bytecode's six-word denominator is the row model's Gate tuple denominator.
Therefore, for **every** possible row cell assignment, bytecode roots 9 and
10 equal the source Gate pair and singleton residuals. Together with the
existing nine-root arithmetic theorem, this yields all eleven row formulas
at any index of an arbitrary 512-row decoded trace.

For a last interaction column, say column 4, the current sample comes from
row `i`, while the previous sample comes from
`directPrevious512(i)`. The row bridge proves that the selected bytecode
`at_prev` read takes slot zero of `[previous, current]` and that `at_oods`
takes the current slot. The `trace.prev = directPrevious512` premise is still
required when using an abstract trace. The native index implementation is
checked exhaustively by the independent 512-index Zig test.

If an all-row argument supplies zero bytecode arithmetic roots, the bridge
derives a valid decoded operation and output for each row. If the trace's
two interaction outputs are the selected bytecode outputs, the bridge also
discharges the earlier generic evaluator equality in the raw Gate theorem.
It still assumes zero authenticated row outputs and the public claimed-sum
closure. A single OODS equality does not itself provide those all-row facts.

The exporter and native acceptance checks pin the installed bundle and
selected program digests; the theorem imports generated modules produced
from those checked bytes. The scalar opcode
replay tests an in-memory `at_prev` to current-offset mutation: the singleton
root changes, while the other ten roots do not. The strict decoder rejects
the same mutation after the program's semantic hash is recomputed.

The selected base-instruction interpreter now has a first formal slice in
[`GeneratedDirectGateBaseVm.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateBaseVm.lean).
Its source-bound list contains the exact first 38 base instructions, through
register 37. Lean interprets each read, constant, add, subtract, multiply,
and destination write over an arbitrary commutative ring, then proves that
registers 24, 28, 31, 34, and 37 equal the first five generated arithmetic
roots. These are the one-hot sum and four Boolean selector constraints. The
exporter checks the native verifier's corresponding opcode switch statements,
the complete installed bundle/program digests, and the instruction bytes.
Acceptance checks the generated Lean file byte for byte. This theorem covers
the selected instruction prefix; registers 38–133, extension opcodes, actual
Zig execution, and proof authentication remain separate correspondence work.

The exporter checks all selected interaction reads and the unique offset list
derived by native `resident_geometry.componentOffsets`: columns 0–3 use
`[0]`, while columns 4–7 use `[-1, 0]`. Its generated Lean `mask_slots` and
`last_mask_reads` theorems prove the local `traceValue` slot mapping: for each
last-column limb, offset `-1` reads sample slot 0 and offset `0` reads slot 1.
Native `verifier_proof.zig` assigns those same two slots to `at_prev` and
`at_oods`. Native `pointsFromOffsets` places the first sample at the OODS
point plus negative trace step. This is an exact shape and read-order result,
subject to the checked exporter/native-source binding.

[`DirectGateOodsMask.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateOodsMask.lean)
specializes the earlier generic source predecessor to the actual 512-row Gate
shape. It defines nine-bit reversal, proves it is an involution and equals an
explicit nine-term arithmetic formula, then composes
it with circle-to-coset conversion, coset offset `-1`, and the inverse
conversion. Its `row_mask_previous` and `row_mask_current` theorems connect
that predecessor to the selected bytecode's `interactionMaskRead`: for any
512-row trace and each column 4–7, the previous read selects the predecessor
row and the current read selects the present row. `row_mask_proof_wire`
models native proof conversion: a one-sample column stores only `at_oods`,
while a two-sample column stores slot 1 as `at_oods` and slot 0 as `at_prev`.
The Zig-to-Lean conversion step remains a reviewed source correspondence,
guarded by pinned source hashes and a targeted native-source order test.
The separate `last_sample_points` theorem gives the geometric OODS requests:
`ζ − traceStep` in slot 0 and `ζ` in slot 1. These are two models of the same
offset, at rows and at sample points; the theorem does not equate an OODS
opening with a trace-row value.

An independent [native 512-row test](../../../src/frontends/s31/tests/proofs/gate_mask_native_test.zig)
checks every index of `utils.previousBitReversedCircleDomainIndex(row, 9, 9)`
against the explicit nine-bit/coset formula and checks offset zero is the
identity. Compiler correspondence acceptance runs this test. The Zig
machine-word operation is compared against the same explicit arithmetic
formula proved equivalent to Lean `BitVec.reverse`, through this exhaustive
finite test. This is a finite validation of the pinned native function, not a
verified translation of Zig's `@bitReverse` intrinsic or proof opening logic.

The theorem does not authenticate the supplied samples as openings of
committed columns or prove random composition, Fiat–Shamir, PCS, or FRI. Nor
does a zero value at one OODS point by itself imply zero constraints on every
M31 row. Those are separate obligations in a whole-prover soundness proof.

## The selected Gate contribution to composition

The production direct Gate package contains one `qm31_ops` component with
eleven roots and composition offset zero. The installed bytecode lists roots
`0…8, 88, 96`: nine arithmetic residuals, the pair LogUp residual, then the
running-sum residual. The native resident verifier evaluates those roots at
the supplied QM31 OODS samples. It computes the inverse of its zeroifier
`V(ζ)`, multiplies each root by that inverse, and passes the results in order
to the accumulator. The accumulator starts at zero and repeats
`acc ← acc · ρ + quotientRoot`, where `ρ` is the composition coefficient.

For a small hand calculation with three roots `r₀,r₁,r₂`, the resulting value
is `((r₀/V) · ρ + r₁/V) · ρ + r₂/V`, which equals
`(r₀ · ρ² + r₁ · ρ + r₂)/V`. The eleven-root Gate contribution has exactly
the same form, with powers from `ρ¹⁰` down to `ρ⁰`.

[`GeneratedDirectGateComposition.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateComposition.lean)
is regenerated only after checking the package source, manifest, verification
key, selected bytecode root order, one-component shape, and pinned native
quotient/accumulator source statements. It proves the bytecode root list equals
the pure eleven-residual list at arbitrary supplied QM31 samples.
[`DirectGateOodsComposition.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateOodsComposition.lean)
proves the common inverse zeroifier factors out of this Horner fold. The
generated theorem therefore identifies the selected Gate contribution with
`fold(ρ, pureRoots) / V(ζ)` when `V(ζ) ≠ 0`. Native `zeroifier.inv()` rejects
zero; the algebraic factorization itself works for any common factor.

This is a local evaluator and accumulator correspondence. The source check
binds the reviewed native statements but is not a verified Zig interpreter.
The theorem assumes the supplied coefficient, zeroifier, and samples are the
ones used by the proof. Transcript ordering, committed opening authentication,
and the random composition, PCS, and FRI soundness arguments remain separate.

## Lookup draw and claimed sum supplied to Gate bytecode

The selected direct verifier reads `sums[0]` as a four-limb QM31 value from
the proof header. Its checked source path commits the main trace, verifies and
mixes the interaction nonce, draws two secure values, checks the public lookup
closure using `sums[0]`, mixes the claim, and commits the interaction trace.
The shared draw routine labels the first value `z` and the second `alpha`.
The direct Gate component then receives exactly `(z, alpha, sums[0])`.
This sequence is checked as a bounded source contract; it does not prove
Fiat–Shamir unpredictability or that a proof opening matches a commitment.

The installed Gate extension source table asks for seven values in this order:
`[alpha, alpha², alpha³, alpha⁴, alpha⁵, z, claimed / 512]`. The resident
verifier computes the last value by inverting the canonical M31 trace size
`1 << 9` and multiplying the QM31 claim by that base-field inverse.
[`DirectGateTranscriptParams.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateTranscriptParams.lean)
proves the M31 inverse lifted into QM31 equals the QM31 inverse of `512`, and
proves the seven-value list. For example, if `alpha=2`, `z=7`, and the claimed
sum is `1024`, the seven parameters are `[2, 4, 8, 16, 32, 7, 2]` modulo
M31. The final `2` enters the running-sum residual as `claimedScaled`.

[`GeneratedDirectGateTranscriptParams.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateTranscriptParams.lean)
is regenerated from the checked package after validating the selected native
draw, closure, claim-mix, interaction-commit, and resident parameter source
statements. Its theorems substitute the verified parameter order into the
eleven-root bytecode identity and the Gate composition equation, giving
`pureRoots(cells, alpha, z, claimed / 512)` at arbitrary supplied QM31 cells.
The source-to-Lean mapping of `mulM31` and the channel implementation remains
a reviewed source premise. Mutation tests reject swapped `z/alpha`, changed
claim mix, and removed claim scaling.

## The sampled OODS values used by the claim check

The core verifier computes its composition value from
`proof.commitment_scheme_proof.sampled_values`, compares that value to the
composition opening at the OODS point, and then passes the same proof to the
PCS value verifier. This is a source-checked pass-through. The claim equality
is a premise in the Lean theorem; the theorem does not authenticate the PCS
openings.

For this one Gate component, the resident bytecode reads the proof's sample
trees as follows (all entries are QM31 values):

| Tree | Local column | Proof sample list | Bytecode read |
| --- | --- | --- | --- |
| Fixed | `i = 0…7` | global fixed column `[0,2,3,1,4,5,6,7][i]`: `[current]` | slot 0 |
| Main | `i = 0…11` | main column `i`: `[current]` | slot 0 |
| Interaction | `i = 0…3` | column `i`: `[current]` | offset 0, slot 0 |
| Interaction | `i = 4…7` | column `i`: `[previous,current]` | offset −1, slot 0; offset 0, slot 1 |

For example, if the fifth interaction column has samples `[13, 29]`, its
previous read is `13` and its current read is `29`. If the fixed global
columns hold `[10,11,12,13,14,15,16,17]`, bytecode local fixed column 1
reads `12`. [`DirectGateOodsOpenings.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateOodsOpenings.lean)
models these lists, requires the selected list lengths, and proves that
each native-style read produces the corresponding `Cells` value. The checked
[`GeneratedDirectGateOodsOpenings.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateOodsOpenings.lean)
then says: **if** the native OODS equality check accepts the composition
claim formed from those sampled cells, the claim equals the pure Gate
eleven-root composition expression on those cells. The exporter checks the
installed bytecode, manifest, core verifier pass-through, and resident read
statements; mutation tests change each binding and require rejection.

This link still needs a separate proof that the PCS opening check binds each
sample to its commitment, that the composition opening itself is authentic,
and that the Fiat–Shamir and FRI arguments give the desired all-row claim.

## How the claimed composition value is read

The direct Gate component uses the native default composition split of one.
The proof's **last** sampled-value tree therefore has eight columns, each
with exactly one QM31 sample. The extractor groups the first four samples
into one secure-field value `A` and the next four into `B`, using the basis
`(1, i, u, iu)`. It reconstructs the claimed composition evaluation as

```text
A = a0 + i·a1 + u·a2 + iu·a3
B = b0 + i·b1 + u·b2 + iu·b3
claim = A + X·B
X = oods_point.repeatedDouble(composition_log_size - 2).x
```

For a hand calculation, choose samples
`[[7],[0],[0],[0],[11],[0],[0],[0]]` and an illustrative `X=3`. Then
`A=7`, `B=11`, and the extracted claim is `7+3·11=40` in QM31. In a real
proof, `X` is determined by the verifier's OODS point and composition log
size. Seven columns or a column containing two samples cause extraction to
fail; the verifier cannot fill the missing coordinate with zero.

[`DirectGateCompositionOpening.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateCompositionOpening.lean)
defines this exact split-one extraction and proves the calculation and
missing, extra, and oversized sample rejection cases. The checked
[`GeneratedDirectGateCompositionOpening.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateCompositionOpening.lean)
links a successful extracted value and the core verifier's OODS equality
check to the pure eleven-root Gate composition expression on the same proof
samples. The exporter checks the native split default, coordinate basis,
last-tree extraction, chunk reconstruction and comparison source statements.
It leaves native circle arithmetic, PCS authentication, FRI and all-row
soundness as explicit obligations.

## The OODS circle factor from the transcript seed

The core verifier draws a QM31 `oods_seed`, maps it to a circle point, and
uses the point's x-coordinate after `composition_log_size - 2` doublings as
the composition reconstruction factor. For seed `t`, the map is defined when
`d = 1+t²` is nonzero:

```text
point.x = (1-t²) / d
point.y = 2t / d
x₀ = point.x
xₙ₊₁ = 2xₙ² - 1
X = x_(composition_log_size-2)
```

For example, `t=1` gives the on-circle point `(0,1)`. Its first doubled
x-coordinate is `−1`, and its second is `1`; every later doubled
x-coordinate stays `1`. At composition log size 10, the extractor therefore
uses `X=1` and reconstructs `A+B`. The example illustrates the arithmetic,
not a claimed transcript draw.

[`DirectGateCircleFactor.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGateCircleFactor.lean)
proves the seed-derived point is on the circle when `d≠0`, that doubling
preserves the circle equation, and that the x-coordinate follows this exact
recurrence for any number of doubles.
[`GeneratedDirectGateCircleFactor.lean`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGateCircleFactor.lean)
substitutes the seed-indexed factor into the accepted composition-tree
equation. The exporter checks the native seed/point path, rational map,
doubling, and factor selection; mutation tests change each path and require
rejection.

The core prover and verifier now use the checked seed conversion and return
`InvalidOodsSeed` if `d=0`, including for `t=i`. Each draws the same single
transcript seed as before; ordinary successful proof bytes are unchanged.
In Lean, the checked map
returns `none` on exactly that case; a successful conversion implies `d≠0`.
The generated theorem requires that success, so its denominator condition
follows from the admitted verifier path. Other native callers may still use
the unchecked circle wrapper, which has `catch unreachable`. The theorem
does not establish that the transcript seed is unpredictable or that PCS/FRI
authenticates the opening.

### Committed opening boundary

The core verifier uses one decoded `sampled_values` tree for the Gate OODS
comparison and passes that same proof object and mask points to PCS. PCS
flattens tree, column, then sample order into the transcript. After Merkle
query checks, it uses the same sampled tree to form DEEP quotient answers for
FRI. In this selected Gate proof, the 40 sampled QM31 values are eight fixed,
12 main, 12 interaction, and eight composition values. The last four
interaction columns each carry `[previous, current]` in that order.

[`DirectGatePcsOpeningLink.lean`](../../../formal/s31/S31/Gadgets/Air/DirectGatePcsOpeningLink.lean)
models each column as a finite bivariate polynomial restricted to the circle.
Its evaluation function substitutes an explicit circle point into the finite
sum of monomials. Four roots and four polynomial families are separate inputs.
The opening premise says those *exact roots* bind those polynomial families
and that each of the 40 supplied values equals the matching evaluation. This
is an assumed relation: Lean does not derive it from a native verifier flag.

The OODS point is calculated from the accepted transcript seed. Fixed, main,
current interaction, and composition slots use that point. The first slot of
each of the last four interaction columns uses `oods + (-step)`, where `step`
is the canonical coset step for the verifier's **maximum degree bound**, not
the individual column's log size. The model derives that step by repeated
doubling of the M31 circle generator. The theorem requires the native bound
range `1..31`. Given the opening premise, Lean transports the sampled Gate
cells and split-one composition tree to an equation at those polynomial
evaluations, including the fixed-column permutation and previous/current
interaction slots. The
[`generated selected instance`](../../../formal/s31/S31/Gadgets/Air/GeneratedDirectGatePcsOpeningLink.lean)
is bound to the installed Gate bytecode, package source, core PCS/FRI source,
and native circle/mask geometry source. The exporter rejects changes to the
shared-sample path, maximum-bound step, previous-point shift, and fixed or
composition mask point. The native constant-polynomial PCS fixture rejects a
changed OODS sample.

This is a **conditional** opening link. Lean does not prove that a successful
Merkle/FRI verification implies the opening assumption, that the finite
bivariate polynomial model refines Stwo's circle-basis degree limits, that
transcript challenges are unpredictable, or that Zig execution refines the
reviewed source statements. In particular, OODS values are checked through
the DEEP quotient and FRI protocol; this theorem does not interpret a Merkle
path as a direct opening at the OODS point. The next proof obligation is the
cryptographic PCS soundness bridge, followed by whole-program and all-row
compiler refinement.

Recheck the bounded export and theorem with:

```sh
python3 scripts/export_s31_direct_gate_bytecode_arithmetic.py PACKAGE \
  formal/s31/S31/Gadgets/Air/GeneratedDirectGateBytecodeArithmetic.lean \
  --logup-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateBytecodeLogUp.lean \
  --composition-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateComposition.lean \
  --transcript-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateTranscriptParams.lean \
  --oods-openings-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateOodsOpenings.lean \
  --composition-opening-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateCompositionOpening.lean \
  --circle-factor-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateCircleFactor.lean \
  --pcs-opening-output formal/s31/S31/Gadgets/Air/GeneratedDirectGatePcsOpeningLink.lean \
  --base-vm-output formal/s31/S31/Gadgets/Air/GeneratedDirectGateBaseVm.lean --check
python3 -m unittest src/frontends/s31/tests/python/test_gate_bytecode_arithmetic.py
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateBaseVm)
(cd formal/s31 && lake build S31.Gadgets.Air.DirectGateOodsMask)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateComposition)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateTranscriptParams)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateOodsOpenings)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateCompositionOpening)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateCircleFactor)
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGatePcsOpeningLink)
zig test --dep stwo_utils \
  -Mroot=src/frontends/s31/tests/proofs/gate_mask_native_test.zig \
  -Mstwo_utils=deps/stwo-zig/src/core/utils.zig
zig test --dep stwo_circle \
  -Mroot=src/frontends/s31/tests/proofs/gate_circle_factor_native_test.zig \
  -Mstwo_circle=deps/stwo-zig/src/core/circle.zig
```
