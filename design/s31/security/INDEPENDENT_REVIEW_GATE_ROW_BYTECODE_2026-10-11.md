# Independent review: selected Gate bytecode at trace rows

**Date:** 2026-10-11. **Decision:** Go for the bounded, conditional Gate row
correspondence increment. No go for a claim of full compiler correctness or
native STARK soundness from this increment.

I reviewed compiler branch S31 `c722f786b6719ee5d9c23b97132328d227c8f6ca`
(engine gitlink `2b169ec0b5cfb9036442a3bfe31ba5a3f76b9b25`) and its
integration snapshot S31 `7880128b7abc6de4459d52718a3c7ffd17df10de`
(engine `807530990cdb9c8fc346801e6f1f44611e9f47dc`). The later combined
S31 head was `e8186cde2911ec52507246c58c950989f7b0f728` when this memo
was written; it was not independently revalidated end to end. The integrated row theorem
has the same SHA-256, `be8c8db7d81fd85b5129f8e12a20307f53a8f53e88bcadc05042464f64cbc2af`,
as the compiler branch. The native `resident_geometry.zig`,
`resident_verifier.zig`, and `verifier_proof.zig` files inspected for mask
selection were byte-identical at both engine heads. This was a focused
source/theorem review, not an audit of the whole verifier.

## Findings and controls

No new false-proof admission was found in the stated theorem. The
M31-to-QM31 lift and LogUp equality hold for arbitrary row cells
(`DirectGateRowBytecodeBridge.lean:29-167`). The all-eleven-root theorem is an
identity at an arbitrary index of an arbitrary decoded 512-row trace
(`:169-225`); it does not assert those residuals vanish. The previous-mask
theorem requires `trace.prev = directPrevious512` (`:230-242`), while the
current-mask theorem and slot definitions select the current cell (`:244-256`,
`GeneratedDirectGateBytecodeLogUp.lean:15-59`). The row-mask values are a
model; native index arithmetic is checked by the separate exhaustive
512-index Zig test, and OODS opening authentication is not derived here.

The operation-decoding theorem requires zero arithmetic bytecode roots at
**every** row (`DirectGateRowBytecodeBridge.lean:258-277`). The raw interaction
theorem requires all-row equality to selected bytecode outputs, zero
authenticated interaction outputs, the public claimed-sum closure, and the
selected predecessor (`:279-316`). These strong premises remain visible; no
single OODS value or proof flag is silently promoted to an all-row fact.

The exporter checks the full installed AIR bundle and selected Gate program
digests (`scripts/export_s31_direct_gate_bytecode_arithmetic.py:43-85`), and
compiler acceptance compares regenerated Lean exports byte for byte
(`acceptance_compiler_correspondence.py:254-285`). The strict decoder rejects a
previous-mask-offset mutation even after its semantic hash is recomputed
(`test_gate_bytecode_arithmetic.py:412-422`). The new scalar mutation changes
only the singleton root (`:424-437`). I independently ran
`python3 -m unittest src/frontends/s31/tests/python/test_gate_bytecode_arithmetic.py`
on both the compiler branch and S31 `7880128` snapshot: 16/16 tests passed in
each. I did not independently rerun Lean AxiomAudit or native proof tests for
this review.

**P3 documentation correction, resolved in integration.** The original
`GATE_LOGUP_NATIVE_REDUCTION.md:382-383` said imported Lean modules check
digests. Those modules record SHA comments; exporter and acceptance checks
perform the validation. Integrated S31 `7880128` corrects this attribution.

## Remaining premises

Native opcode execution must continue to match the extracted semantics and
selected source bytes. Proof and commitment binding must tie the modeled cells
and public events to the accepted native proof. A separate random-composition,
Fiat–Shamir, PCS/FRI and all-row zero argument must establish the residual
premises with a quantified error bound. This review does not close any of
those obligations and does not establish a full compiler correspondence proof.
The full Lean/source-binding gate and native acceptance suite must pass on the
final combined S31/engine heads before release; the two scalar runs and
byte-identical mask sources are narrower evidence.
