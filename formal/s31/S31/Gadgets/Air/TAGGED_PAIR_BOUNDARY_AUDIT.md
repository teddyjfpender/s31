# Tagged two-call boundary: formal correspondence audit

Scope: the staged `direct-m31-private-pair-v1` profile. This is a static
source audit of the pair engine and S31 wrapper, not a proof of the STARK
verifier or an empirical test.

## Native facts and formal premises

| Native source | Observed condition | Formal status |
| --- | --- | --- |
| `tagged_pair_chip.zig::rowConstraints` | Four lane residuals enforce `out = in² + constant` **if** all trace-row residuals vanish. The call ID is a verifier component constant; `main[0]` is a witness step. | `IndexedChipPath` assumes the local step equation. AIR residual-to-trace correspondence is not proved here. |
| `tagged_pair_chip.zig::rowConstraints` and `writeInteraction` | Each row emits `+(relation,call,step,input)` and `−(relation,call,step+1,output)` into the shared LogUp relation. No local row equation checks `step < R`, step order, or a permutation of `0..R−1`. | The `Fin R` path theorem **assumes** canonical indexing. The reduction from arbitrary witness steps and exact tagged event balance is an open Lean theorem, described below. |
| `private_pair_boundary.zig::Plan.validate` | Two call IDs must be `0,1`; `validateRounds` requires a power of two in `[16,32768]`, far below M31's `p = 2147483647`. Endpoint addresses have checked producers; coherent aliases are allowed. | Source-level admission checks are not connected to Lean. The `R < p` fact is available for the missing index theorem. |
| `tagged_pair_bridge.zig::rowConstraints` | Eight endpoint columns have residual `current−next` on all sixteen cyclic rows. Four paired Gate fractions have `1/16` weight; the fifth fraction closes `(call,0,input)` and `(call,R,output)`. | `TaggedPairBridgeRows.eight_columns_constant` proves constancy from zero residuals on the first fifteen adjacencies. Gate/chip lookup authentication remains conditional. |
| `direct_pair_arithmetic.zig::verifyBorrowed` | Reconstructs five components and trace spans, checks four commitment roots, public words, transcript identity, one shared lookup challenge and five claimed sums, then calls the native PCS/FRI verifier. | Transcript and component correspondence, the random challenge reduction, and PCS/FRI soundness are unproved in Lean. |
| `pair_source_binding.zig`, `component_manifest.zig`, `pair_native_package.zig` | Recompile source without witness, derive ordered calls/offsets, compare typed V3 manifest and byte-exact key, then decode a bounded proof envelope. | Host checks are staged, not formalized. `verifySealed` still accepts source, AIR bundle and key as caller arguments; a released verifier must pin its trusted statement and AIR identity. |

The engine has one shared seven-coordinate compression for tagged chip tuples
and six-coordinate Gate tuples, with distinct first-coordinate relation IDs.
Proving that the single random compressed closure implies the separate exact
Gate and chip event multisets needs a seven-coordinate collision/pole bound
for **the union of all five components**. The existing Gate-only bound does
not discharge this. The `1/16` bridge weight is valid because 16 is invertible
in M31, but the native paired-fraction residuals still need a formal
reduction to those rational events. The interaction running sums must be
shown to telescope with the intended cyclic row masks and claimed sums.

## Why witness step order need not be a local constraint

There is a sound route to canonical indices, but it starts from **exact**
tagged event balance, not merely a passing random compressed sum. For one
call, suppose there are exactly `R` native rows. Each row consumes
`(call,k,input)` and produces `(call,k+1 mod p,output)`. The authenticated
start produces `(call,0,start)`; the authenticated end consumes
`(call,R,end)`; all these full tuples balance as an integer multiset.

For `R > 0`, the start tuple must be consumed by a row at step 0, since the
only other consumer is at step `R`. That row produces an event at step 1.
When `1 < R`, it must be consumed by another row at step 1. Repeat through
step `R−1`. Since `R < p`, the indices `0..R−1` are distinct in M31, so the
selected rows are distinct. There are already `R` of them; they exhaust the
trace. The final produced event at step `R` therefore equals the authenticated
end. No row remains for a disconnected cycle. The same argument holds
separately for call IDs 0 and 1 because the call ID is part of every tuple.
For `R = 0`, exact balance directly equates start and end. The native profile
admits only `R ≥ 16`.

`IndexedChipPath.two_call_complete_path` states the result for rows already
named in canonical order. `RawChipIndexCoverage.lean` now closes that ideal
event-model gap. Starting with arbitrary native row indices, it projects
exact full `(index,state)` balance to index balance, proves coverage, upgrades
the injective selection to a **unique** bijection by finite cardinality, and
uses the full value-bearing permutation to prove start, adjacent-state, and
end joins. Its `two_call_joint_exact_events_complete_path` theorem takes one
multiset containing both canonical call tags and a local step rule, then
proves both `R`-step endpoint claims. Its field modulus and state type are
abstract; the actual seven-coordinate tuple and production source still need
the source correspondence and challenge reduction below.

The proof uses exact integer multiset balance, not a random-compressed lookup
identity. A forged trace with duplicate witness steps cannot satisfy this
ideal full-tuple balance when `R < p`; that does not by itself establish what
the native STARK verifier accepts.

## Malformed rows and what they establish

Take `R = 16`, constant `0`, and all sixteen committed chip rows with witness
step `0` and four-lane `input = output = 0`. Every local square transition
residual is zero. For ordinary non-pole challenges, the component's own
interaction writer can form its running sum: each row contributes
`1/q(0,0) − 1/q(0,1)`. The **local chip AIR** therefore does not certify the
canonical index sequence. The joint authenticated bridge closure adds
`−1/q(0,0) + 1/q(0,16)` and normally rejects this trace; the resulting
rational expression is

```text
15/q(0,0) − 16/q(0,1) + 1/q(0,16).
```

This is a counterexample to inferring canonical indexing from the local chip
row checker or the prover-side `writeInteraction` step bound. It is **not** a
counterexample to the complete native verifier. No full-verifier false-proof
acceptance was found in this static audit. A negative fixture should commit
these repeated-step rows before deriving the challenge and require the joint
closure to reject; it must not rely on the honest `writeBase` helper.

An even smaller abstract example shows why full index keys matter: with the
identity step, start/end `0`, and rows `0→0`, `1→1`, unindexed value multisets
balance while row 1 is an orphan. Indexed balance fails at state index 1.
The modulus bound is also necessary when interpreting both endpoint indices
inside the field. At `p = R = 2`, start/end state `0` use the same index
`0 mod p`, and rows
`(step 0, 1→1)` and `(step 1, 1→1)` form a detached modular cycle. The full
field-valued index/state event multiset balances, yet neither row is attached
to the authenticated start. `RawChipIndexCoverage` deliberately represents
the terminal index by natural `R` and is applied only under `R < p`; native
M31 admission likewise excludes this case.
Finally, projecting away values is safe only for the *index coverage* lemma:
with `R = 1 < p`, one row at step 0 with input `7`, output `8`, and claimed
start/end `3,9` has balanced indices but mismatched full state events.

## Remaining proof chain

1. Extract native local residual, shifted mask, row-count, and transcript
   semantics from the exact pinned engine source into Lean.
2. Prove the paired-fraction AIR and cyclic running sums imply the rational
   five-component closure, with nonzero denominators and `16⁻¹` accounted for.
3. Prove a joint seven-coordinate challenge exceptional-set bound that
   separates Gate and both tagged-chip event multisets.
4. Connect the now-proved arbitrary-row tagged path and bridge constancy
   theorems to the existing circuit-to-chip endpoint join using the exact
   source-generated addresses, call IDs, and four-lane tuple encoding.
5. Tie the source-generated Plan, manifest, public words, and proof verifier's
   committed trace openings to those Lean models under an explicit PCS/FRI
   and Fiat–Shamir soundness theorem or assumption.

Until these links are discharged, the formal result is conditional algebra
and event reasoning. It does not establish native proof soundness.
