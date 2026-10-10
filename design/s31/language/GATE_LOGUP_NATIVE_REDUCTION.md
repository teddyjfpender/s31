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

The remaining evaluator obligation is to show that the exact selected
`STWZEVA/1` bytecode, bound by the installed key and bundle hash, computes
this pure 11-residual function at the stated local positions. The fixture
checks the manifest's exact index vector and three trace spans, but does not
independently interpret that bytecode. The next section closes the nine
arithmetic roots of this obligation. Authentication of full committed
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
coordinates. Lean proves, for **arbitrary M31 base-field** eight fixed and
twelve main cells, that these nine roots equal
`DirectGateEvaluatorCells.arithmetic`, then derives Gate operation/output
correctness when all nine vanish. This is a universal M31 identity, rather
than evidence from finitely many vectors. The native verifier evaluates the
same base instructions at QM31 OODS points; lifting this identity to those
extension-field evaluations remains a separate formal obligation.

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
roots on two source rows and fixed/main/current/previous-cell mutations,
including changed-bundle and rehashed-root-order rejection controls.

This increment does **not** universally prove that extension roots 9 and 10
equal `pair` and `last`. The scalar replay checks them on concrete rows only.
It also does not connect the previous-row mask to `directPrevious`, show that
the proof commits/opens these exact cells, or prove the random-composition,
Fiat–Shamir, PCS, and FRI arguments. Those remain premises of the whole
compiler correspondence theorem.

Recheck the bounded export and theorem with:

```sh
python3 scripts/export_s31_direct_gate_bytecode_arithmetic.py PACKAGE \
  formal/s31/S31/Gadgets/Air/GeneratedDirectGateBytecodeArithmetic.lean --check
python3 -m unittest src/frontends/s31/tests/python/test_gate_bytecode_arithmetic.py
(cd formal/s31 && lake build S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic)
```
