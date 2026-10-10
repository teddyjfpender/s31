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

One useful Lean interface is a pure `DecodedDirectGateTrace` carrying the
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

## Focused implementation checks after the timing window

1. Export one direct proof's fixed/main/interaction row cells and the bound
   evaluator program digest; independently reconstruct both native row
   residuals at `R=16` and the accepted claimed-sum fold. Include first,
   last, and nonadjacent rows to catch predecessor-order mistakes.
2. Mutate one committed input limb or `q7` multiplicity, rebuild interaction
   columns for the mutated row values, and show the reconstructed event lists
   or residuals change. Reseal package metadata for topology mutations.
3. Change only the proof envelope's Gate claimed sum and require
   `InvalidLookupSum`; this existing native control is still pending a run
   after the V6 timed proof phase.
4. Build a Lean module for the decoded-cell evaluator identity and a native
   exporter fixture. Keep the cryptographic row-satisfaction statement as a
   named, documented premise until an independent PCS/FRI review discharges
   it.
