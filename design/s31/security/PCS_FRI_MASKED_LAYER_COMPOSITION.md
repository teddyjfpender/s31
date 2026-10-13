# Conditional masked-query bound across FRI layers

[`MaskedLayerBound.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MaskedLayerBound.lean)
composes the arbitrary-layer acceptance count with the exact M31-masked
query distribution. It works in a finite product space of independent
uniform 32-bit words. It does **not** prove that the native transcript has
that distribution.

For a committed oracle fixed before the challenge and a set `good` of
acceptable query positions, define `alpha` as an upper bound on the uniform
mass of `good`. Native M31 reduction followed by a low-bit mask has a
maximum per-draw positive bias of `2 / 2^32` when the query domain has
`2^k` positions with `2 ≤ k ≤ 31`. The theorem gives the conditional bound

```text
Pr[accepted] ≤ MerkleFailureBudget + SamplingFailureBudget
               + (alpha + 2 / 2^32)^draws.
```

The counted event checks **every raw draw**, including repeated positions.
`draws = 0` is permitted and gives the expected trivial query term `1`.
No independence claim is made for Blake2s transcript outputs.

The theorem's premises still require:

1. Successful native verification outside the two failure events implies
   the modeled arbitrary-layer query-path checks. This Zig-to-Lean semantic
   refinement is not proved.
2. A FRI proximity result supplies a fixed good set and its `alpha` bound.
   The result must account for the actual folding schedule and committed
   oracles, rather than an arbitrary set chosen after queries.
3. Merkle and sampling failure events have justified budgets. In a real
   Fiat–Shamir proof, this includes commitment binding, BLAKE2s assumptions,
   and transcript adaptivity.

Consequently this theorem cannot turn the nominal 96-bit profile into a
published-proof justified release profile. The release preflight remains
fail closed until these premises and the whole PCS/FRI reduction are discharged.

## Check

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.MaskedLayerBound
```
