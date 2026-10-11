# Independent review: verified mixed full-trace sidecar

Reviewed S31 commit `09cbb5a` and its pinned stwo-zig engine commit
`f34f6a64185e98567392a3d27492d7ccb267f6f7` on 2026-10-11. Scope is
`general_package.verifyEmbeddedWithTraceAudit`, the engine's
`auditVerifiedSourceBoundWitness`, the corresponding mutation tests, and the
current `SourceMixedAuthenticatedTrace` / `SourceMixedEventAlignment` contracts.
This review is a code and focused-test audit, not a cryptographic proof.

## Result

I found no surviving sign, denominator, logical row-order, or obvious
assignment-swap bypass in this optional path. The two concrete test/shape
gaps raised during review were fixed before the pinned commits:

1. All nine chip main columns now require the call's expected log size and
   row count. A hostile mutation of the ninth column's log size rejects.
2. A private-selector pair with **identical eight public words** now proves
   one branch and audits the other against the same accepted proof. The wrong
   assignment fails specifically at `InvalidMixedTraceAuditMainRoot`, rather
   than being caught early by the public-output evaluator.

The audit is meaningful for a caller who supplies a full private assignment:
it verifies the proof first, reconstructs source-derived fixed, main, and
interaction columns, and compares their three Merkle roots with the accepted
proof's roots. Root equality binds that supplied trace under the Merkle
commitment assumption. The ordinary succinct verifier does not receive the
assignment or run this audit.

## Checked correspondence within the sidecar

- The S31 wrapper reparses the embedded source, checks the assignment's
  computed public words with `relation.evaluate`, recompiles its witness, and
  passes source topology plus witness values to the engine. The engine runs
  `verifySourceBoundBorrowed` before any sidecar result is returned.
- The fixed trace is rebuilt from the bounded source plan. The audit checks
  every Qm31 row's four selectors, three addresses and multiplicity against
  that fixed trace, plus all twelve main limbs and the actual QM31 arithmetic.
  It checks reserved `0`, `1`, `u`, all eight public outputs, and source-owned
  Gate use/yield counts. Rows with zero output multiplicity still receive
  arithmetic and main-column checks.
- The Gate bag is counted by address, but this is sufficient *inside this
  sidecar check*: every Gate row and bridge endpoint was separately tied to
  the unique value at its canonical source address. The count therefore
  represents the full `(address, value)` event bag. It includes the nine-word
  public feeder (eight outputs and fixed `u`) and eight endpoint reads per
  call, including repeated addresses.
- Chip rows are checked at the native bit-reversed storage index for each
  logical step. The same loop checks `out = in² + c`, step tags, final state,
  and adjacent tagged-event cancellation. Bridge endpoint words must remain
  constant on all sixteen rows and agree with the compiled circuit values.
- The LogUp row audit recomputes paired and singleton fractions from checked
  fixed/main cells. It rejects a zero denominator, checks intermediate
  fraction prefixes and the final bit-reversed predecessor recurrence, and
  checks both each claimed sum and the global closure. In a field, a nonzero
  paired denominator `d₀d₁` also means both factors are nonzero. The bridge
  factor `1/16` contributes eight positive Gate reads and the endpoint term
  `1/last - 1/first`; the chip contributes positive inputs and negative
  outputs. These signs agree with the Lean event lists.
- The audit replays the source-derived column order through `selectedColumns`
  and the same PCS commitment builder. It compares fixed, main, and
  interaction roots to proof roots 0, 1, and 2 respectively. The lookup
  challenge is redrawn after the matching main root and nonce, and the
  rebuilt component sums must equal the proof's claimed sums before the
  interaction root is compared.

I independently ran the focused `test-mixed-equal-public-sidecar`,
`test-mixed-trace-mutations`, and `test-mixed-circuit-mutations` Zig build
targets; all exited successfully. The N=1/N=8 honest proof/audit target is
also present in the pinned code, but this review did not re-run that larger
target independently.

## Formal scope and remaining obligations

`GateRows` now includes an all-row `arithmeticResidual`, and
`source_gate_rows_arithmetic` projects it to each canonical source row. This
**supersedes** the earlier observation in
`INDEPENDENT_REVIEW_AUTHENTICATED_TRACE_RECORD_WIRE_2026-10-11.md` that the
then-current `GateRows` covered only Gate interaction rows. That older review
remains accurate for the revision it inspected, but not this one.

`SourceMixedEventAlignment.EventProjection.ofSourceRows` now derives the
global positive and negative event permutations from source-row identity,
empty baseline lists, public words, and local bridge/chip tuple projections.
This reduces the number of independent correspondence premises. Its inputs
are still typed Lean rows and local equations; the native sidecar returns
three roots and row counts, **not** a Lean object or independently serialized
event-list certificate. No theorem currently constructs `EventProjection`,
`AuthenticatedMixedTrace`, `SourceShape`, or `LocalPublicPath` from a native
audit or ordinary verifier success.

Most importantly, root equality for a supplied sidecar is different from
extracting every committed row from an arbitrary succinct proof. The latter
requires a stated PCS/FRI soundness or extraction assumption, Merkle binding,
and a formal mapping of native column order, row order, values, and challenge
transcript to the Lean types. A separate compiler correspondence result must
relate `relation.evaluate` and scheduled circuit rows to `LocalPublicPath`.
The fixed-witness exceptional-pair bound also remains conditional; this audit
does not prove Fiat–Shamir challenge independence or a whole-prover rejection
probability.

One further useful hostile test is to change the arithmetic value on a
**zero-multiplicity padding Gate row** while keeping its multiplicity zero,
then require `InvalidMixedTraceAuditGate`. The loop currently checks such
rows, but the existing mutation changes an ordinary Gate row. This is a
coverage recommendation, not a detected bypass.
