# P07: conditional lookup-pair bias of the selected M31 channel

The selected `Blake2sM31Channel` reduces each raw BLAKE2s output word modulo
`p = 2³¹−1` **before** its base-felt rejection check. The check compares a
canonical residue with `2p` and therefore cannot reject it. The shared
`drawLookupElements` call takes `z` and `α`, four M31 coordinates each, from
the eight reduced words of **one** digest block. This is the source flow pinned
by the [exact-rational diagnostic](../../../scripts/release/pcs_fri_lookup_challenge_bias.py)
and the existing [byte-level transcript audit](PCS_FRI_BCS_TRANSCRIPT_REFINEMENT.md).

## Count one fixed-prefix draw

Let `U = 2³² = 2p+2`. For a raw uniform `u32` word, the canonical residue
`r` has preimages `r` and `r+p`; `r+2p` fits below `U` only for `r=0` or
`r=1`. Thus the preimage count is

```text
c(r) = 3,  r ∈ {0,1}
c(r) = 2,  otherwise.
```

The count sums to `2·3 + (p−2)·2 = U`. Conditional on **eight independent
uniform raw words for one fixed draw input**, a pair
`x=(z₀,z₁,z₂,z₃,α₀,α₁,α₂,α₃) ∈ QM31²` has probability
`μ(x)=∏ᵢ c(xᵢ)/U⁸`. Uniform `QM31²` would assign `ν(x)=1/p⁸`. Hence for
every event `E⊆QM31²`, including an arbitrary lookup bad-challenge set,

```text
μ(E) ≤ ρ · ν(E),     ρ = (3p/U)⁸ ≈ 25.6289061545.
```

This is the **sharp universal multiplicative factor**: the all-zero pair has
eight three-preimage coordinates and attains the factor. It is a deliberately
conservative bound for a polynomial zero set, whose structure might permit a
smaller factor after a separate proof. The
[`BiasedLookupPair.lean`](../../../formal/s31/S31/Gadgets/PcsFri/BiasedLookupPair.lean)
theorem proves the exact raw-word preimage characterization, finite-event
preimage cardinality (including disjoint fibers for arbitrary output events),
weight inequality, normalized rational bound, and all-zero equality. It does
not prove independent BLAKE2s words or compiled Zig semantics.

## Apply to the existing conditional lookup ledger

The checked N1–N8 mixed lookup budget has at most `E=722185` tuple
occurrences. Its fixed-roster polynomial argument gives the **uniform-pair**
conditional bound `(7E−6)/p⁴ = 5055289/p⁴ ≈ 2⁻¹⁰¹·⁷³`. Applying the
arbitrary-event ratio gives the fixed-prefix **biased-pair** bound

```text
ρ · 5055289/p⁴
  = 5055289 · 3⁸ · p⁴ / 2²⁵⁶
  = 705400052412386823532016567781655113955961714649
    / 115792089237316195423570985008687907853269984665640564039457584007913129639936
  ≈ 2⁻⁹⁷·⁰⁵.
```

The zero-denominator event is **already included** in `7E−6`. If `Q_L`
distinct valid post-main-commitment continuations are tested with their tuple
multisets fixed before each draw, the elementary union bound is at most
`min(1, Q_L·ρ·5055289/p⁴)`, conditional on a suitable independent fresh-draw
model. This is a local lookup term only; the attacker can test valid nonces
and distinct commitments. `Q_L` is not bounded here. The previous
`2⁻¹⁰¹·⁷³` figure assumed a uniform pair and must not be used as the native
conditional lookup estimate.

Run the exact diagnostic and focused checks from the S31 root:

```sh
python3 -B scripts/release/pcs_fri_lookup_challenge_bias.py --json
python3 -B -m unittest scripts.tests.test_pcs_fri_lookup_challenge_bias -v
cd formal/s31 && lake build S31.Gadgets.PcsFri.BiasedLookupPair
```

## Remaining soundness joins

The raw-word premise concerns one fixed draw input. Selecting a valid
interaction nonce or other transcript continuation can select among many
digests. A BCS/Fiat–Shamir reduction must model that adaptive selection,
prove freshness or account for repeated/colliding hash inputs, and bound all
attacker hash work and valid continuations. The native accepted-proof to
committed fixed-roster lookup reduction and the other PCS/FRI error terms
remain open. In particular, this count closes neither P07 nor P09, supplies
no native proven security bits, and does not make the v0.1 release admissible.
