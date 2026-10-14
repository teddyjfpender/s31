# Gate PCS roster versus the published FRI batch width

**Finding:** the legacy ordinary Gate proof has a checked four-tree column
roster, but it does not implement the S-two paper's degree-corrected,
multi-domain FRI ensemble. The paper's batch width `M` for this production
proof is therefore **unidentified**, not `319`, `193`, or twice either count.
The selected `epsilon(T)/T <= 2^-96` target at `T=2^64` remains unproved;
native proven security bits are `null` and the v0.1 release gate stays closed.

The [source-bound diagnostic](../../../scripts/release/pcs_fri_gate_paper_batch_boundary.py)
starts from one sealed **legacy** Gate package accepted by its locally trusted
native `check-key` executable. It reuses the [Gate geometry
audit](PCS_FRI_GATE_FINAL_DOMAIN.md), requires the pinned stwo-zig gitlink
`59e1f115250b8af01712b9bf3d71616e53094964`, and checks exact SHA-256
bytes for ten prover/verifier PCS and FRI source files. Its report binds the package
manifest hash, verification-key hash, AIR-bundle hash, reviewed engine-source
hashes, and source-height roster into an audit digest. The package hashes
establish internal consistency, not independent binary provenance. Use only
a locally trusted package executable. The optional raw BLAKE2s Gate profile
has different proof/key semantics and is outside this diagnostic's admission.

## What the native verifier actually commits

The pinned [`native_verifier.zig`](../../../src/frontends/s31/runtime/native_verifier.zig)
commits four roots in order: fixed before public/circuit values, main before
the lookup challenge, interaction after that challenge and claimed sums, and
composition after AIR coefficients. The pinned
[`core/verifier.zig`](../../../deps/stwo-zig/src/core/verifier.zig) constructs
the composition commitment and OOD mask claims. Then
[`pcs/verifier.zig`](../../../deps/stwo-zig/src/core/pcs/verifier.zig)
authenticates queried rows and calls `quotients.friAnswers`, which returns
**one accumulated QM31 quotient word per query**. The prover's
[`pcs/scheme.zig`](../../../deps/stwo-zig/src/prover/pcs/scheme.zig) likewise
hands one `LazyQuotientProvider` to FRI. Original committed rows participate
in that quotient calculation, but no independent original-word degree test
is part of the FRI input. This is the open [P05 degree-correction
gap](PCS_FRI_DEGREE_CORRECTION_GAP.md).

For the reviewed `2^20`-row Gate geometry, the four commitment widths and
their actual native source heights are:

| Source log height | Fixed | Main | Interaction | Composition | Total |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 3 | 16 | 32 | 8 | 59 |
| 18 | 3 | 1 | 4 | 0 | 8 |
| 16 | 4 | 3 | 8 | 0 | 15 |
| 14 | 3 | 1 | 4 | 0 | 8 |
| 9 | 8 | 12 | 8 | 0 | 28 |
| 8 | 3 | 1 | 4 | 0 | 8 |
| 4 | 21 | 80 | 92 | 0 | 193 |
| **All** | **45** | **114** | **152** | **8** | **319** |

The table counts M31 committed source columns, not OOD sample claims,
periodicity-derived samples, or members of a paper FRI ensemble. In
particular, the earlier CAS07 pilot's `311` columns exclude the eight
composition columns and collapse four production epochs into one candidate
root. They cannot be used as the complete production roster.

## Exact conditional paper arithmetic

The [S-two whitepaper's multi-domain FRI soundness theorem](https://eprint.iacr.org/2026/532.pdf)
and its [authors' theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
use the full original-plus-own-quotient ensemble in the degree-corrected
evaluation protocol. The [release theorem ledger](PCS_FRI_STWO_UDR_FEASIBILITY.md)
quotes its one-list batching expression as

```text
e_batch(M) = (M - 1) · N · B² / |QM31|,  |QM31| = (2³¹ - 1)⁴.
```

If, **only for arithmetic**, one identifies the key's largest trace size
with the paper's `N=2^20` and its native blowup with `B=2`, then the paper
ensemble would start at `D₀=NB²=2^22`. The native quotient-only FRI instead
starts at `NB=2^21`. This domain mismatch is another reason there is no
protocol mapping. With no grinding credit, and at least one BCS round,
the batching term alone would contribute at least
`((T+1)/T) · e_batch(M)` to the quoted paper work-factor upper-bound
expression. Exact rational arithmetic gives:

| Hypothetical `M` | Ratio of this one expression to `2^-96` | Interpretation |
| ---: | ---: | --- |
| 64 | about 0.984375 | This term can fit; all other terms still need room. |
| 65 | about 1.0000000019 | This term exceeds the selected target. |
| 193 | about 3.000000006 | A same-height original-only bucket of the largest observed native height would exceed it. |
| 319 | about 4.968750009 | Treating all source columns as one batch would exceed it. |
| 386 | about 6.015625011 | Pairing each of the 193 same-height source columns with one own quotient in one batch would exceed it. |

Thus **64** is the largest hypothetical `M` for which this *single* quoted
term can fit at these `N,B,T` values, taking the most favorable `R=1`.
This is an upper-bound **certificate-feasibility** result: if a proved
mapping produced `M>=65` for one such batching round, the current published
bound could not certify the selected target. It is **not** a lower bound on
an attack's success probability and says nothing conclusive about the
security of a different protocol or a sharper proof. The 193, 319, and 386
substitutions are counterfactual layouts, not measured theorem `M` values.
Even `M<=64` would not certify this protocol: the other IOP/FRI terms,
adaptive transcript, Merkle/ROM reduction, native quotient relation, and
small-height hypotheses remain open. Adding queries alone cannot reduce
this batching expression.

## Required mapping before any numeric claim

1. Derive an installed-key-owned roster of each fixed, main, interaction,
   and composition column, its native height and root epoch, and every OOD
   sample and own quotient. Authenticate both the original and quotient
   words at queried rows and prove their whole-oracle degree bounds.
2. Specify whether all columns at a height share one paper batch, whether
   a new versioned protocol partitions them into several batches, and how
   each batch's errors compose. Derive the exact `M` for **every** batch;
   source column counts alone do not set it.
3. Prove the two-point native quotient and lifted domain relation refine a
   published degree-corrected theorem or prove a new one. Then identify the
   theorem's `N`, `B`, per-height domains, list bounds, AIR degree and small
   table conditions from the same accepted proof/key.
4. Compose all errors with the actual raw-query sampler, transcript epochs,
   BLAKE2s/Merkle binding and BCS/ROM at `T=2^64`. Keep
   `native_proven_security_bits=null` until that entire argument is checked.

To reproduce the local diagnostic:

```sh
python3 -B scripts/release/pcs_fri_gate_paper_batch_boundary.py \
  /path/to/locally-trusted-sealed-legacy-gate-package
python3 -B scripts/release/pcs_fri_gate_paper_batch_boundary.py \
  /path/to/locally-trusted-sealed-legacy-gate-package --require-paper-mapping
```

The second command exits 2 by design. The
[four focused regressions](../../../scripts/tests/test_pcs_fri_gate_paper_batch_boundary.py)
check the exact 64/65 boundary, all four trees and occupied heights, the
audit binding, and source/key/roster fail-closed cases.
