# Independent adversarial review: general mixed lookup boundary

Reviewed the experimental `direct-mixed-general` 1–8 call path on 2026-10-11,
with the pinned `deps/stwo-zig` revision `7d544c6839497ca19b6c7ef9b982e464f10cfeed`.
This is an independent source audit of the S31 source-embedded verifier,
compiler binding, component registry, tagged chip and bridge AIRs, and native
verifier. I did not run a new native proof or cryptographic test for this
review. No concrete false-public-result proof or malformed-proof acceptance
was found. This is not an end-to-end STARK soundness proof.

## Exact lookup ledger

The intended zero sum is the circuit claim plus the native chip and bridge
claims plus the verifier's public output terms. Write `CY` for circuit Gate
outputs counted by the fixed multiplicity column, `CU` for circuit Gate
inputs, `P` for the eight public M31 words at addresses 3–10 and the fixed
`u` wire at address 2, `BG_i` for a call's eight bridge Gate reads, `CI_i`
and `CO_i` for its chip row inputs and outputs, and `BS_i`, `BF_i` for its
bridge chip start and finish. With no compressed-key collision or pole,

```text
positive: CY + P + sum_i (BG_i + CI_i + BF_i)
negative: CU     + sum_i (CO_i + BS_i)
```

The circuit fixed-column constructor adds **one Gate yield for every endpoint
occurrence**, including a fork into two calls. The bridge's eight word
columns are constant across its 16 rows; each Gate fraction is weighted
`1/16`, so the total is one Gate read per endpoint occurrence. Its chip terms
are `-start + finish`, also weighted `1/16`. Each chip row is `+input
-output`. The public terms are supplied by `direct_trace.lookupSum` in the
native verifier, not by a bridge row. The six-word Gate tuples carry a Gate
relation ID and address; the seven-word chip tuples carry a distinct relation
ID, call ID, step and four M31 values. The registry rejects a colliding SHA
word layout under the chip relation ID.

For each call, exact multiset balance and tagged isolation force a chip row
with input step zero. A row at step `k` has output step `k+1`; by induction,
steps `0, ..., rounds-1` require at least `rounds` distinct rows. The trace
has exactly `rounds` rows, so no extra disconnected rows can replace the
path. The four local AIR equations then yield the declared square-plus-
constant result at step `rounds`. This argument depends on exact lookup
balance, authenticated all-row equations, and the enforced `rounds < p`
bound. It is **not** a proof that compressed LogUp and PCS acceptance imply
those premises.

## Adversarial cases checked in source

| Attempt | Observed guard | Remaining qualification |
| --- | --- | --- |
| Change a public result while retaining the proof. | The verifier supplies all eight canonical words to the Gate feeder and transcript. The S31 wrapper builds the borrowed proof's output slice from those same words; native lookup and PCS verification bind them to the committed circuit. | Relies on the bundled circuit Gate relation and PCS soundness. |
| Replace a bridge endpoint or reuse an output port, then recompute manifest hashes. | `compileSourceTopology`, `compileManyTopology`, `Plan.preprocessed`, and `inspection.inspectSource` rebuild exact source addresses and the fixed root; output-port freshness is checked. `registry_manifest.requireSource` compares the whole regenerated manifest. | A source *change* creates a distinct authorized program and proof identity. |
| Swap a chip and bridge, alter call ID, rounds, constant, relation ID, source kind, or claimed-sum index. | The source-generated roster fixes `circuit, chip(0), bridge(0), ...`; registry and live handle checks compare geometry and relation schemas. Ordered call data and the manifest digest enter the transcript. | The public engine adapter accepts caller-selected `Selected`; only the S31 embedded wrapper is a proof admission entrypoint. |
| Offset two claimed sums by opposite values to keep their total zero. | Each sum enters the transcript in canonical component order and the corresponding AIR component's final running-sum equation. The engine has an explicit compensated-pair negative test. | Fiat–Shamir/PCS binding is assumed; algebraic total zero alone would be insufficient. |
| Use a cycle or disconnected chip rows to avoid the required start-to-finish computation. | Exact tagged step balance plus the exact `rounds` trace length excludes extra rows, as argued above. | Requires formal exact-balance reduction and noncolliding challenges. |
| Supply truncated, trailing, oversized, or malformed proof bytes. | The envelope checks a 16 MiB cap and canonical header; geometry-aware postcard preflight precedes a bounded decoder; the stream must consume all bytes; the borrowed proof enters native verification. | This review did not fuzz decoder edge cases or establish a per-request service resource bound. |

The native path also compares the fixed preprocessed commitment, selected
AIR program binding, PCS config, source-derived geometry, live runtime AIR
handles, public statement, interaction nonce, lookup closure, and the final
borrowed STARK proof. The verifier reconstructs these before accepting
proof bytes. A re-sealed *diagnostic* manifest does not act as a verifier key.

## Open proof obligations and test scope

The compiler-to-AIR correspondence still needs a theorem that the source
evaluator, value-carrying circuit, witness-free topology, fixed Gate
multiplicities, bridge endpoint columns, and public feeder agree for **all**
admitted programs. The Lean typed boundary captures the intended exact-event
theorem, but its model inputs are not yet extracted from accepted native
proofs. A complete argument also needs the compressed LogUp collision/pole
bound under this transcript, all-row AIR testing, commitment/FRI security,
and Fiat–Shamir composition. The existing numerical lookup bound is a
conditional algebraic term, not a total soundness error.

I inspected existing unit and acceptance controls for all call counts,
changed public words, claimed sums including compensated pairs, source and
manifest changes, and endpoint aliases. I did not rerun them during the
prospective timing run. `private` is a language visibility label here: the
mixed base traces are committed without witness blinding.
