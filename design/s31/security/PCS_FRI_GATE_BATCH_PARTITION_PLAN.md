# P05: Gate batch partition feasibility at the selected T64/96 target

**Status:** conditional theorem arithmetic and protocol design. No native
security bits, no production selector, and no P05 discharge. Reproduce the
exact integer floor with
[`pcs_fri_gate_batch_partition.py`](../../../scripts/release/pcs_fri_gate_batch_partition.py):

```sh
python3 -B scripts/release/pcs_fri_gate_batch_partition.py
python3 -B scripts/release/pcs_fri_gate_batch_partition.py --require-proven
```

The second command exits 2. The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf)
defines per-domain batch sizes `M_i` in Protocol 3, pads each batch to the
common `M = max_i M_i`, and uses that `M` in Lemma 3's batching error. The
reviewed Gate native source roster has **193 columns at source log height 4**,
as recorded by the [source-bound Gate paper-batch diagnostic](PCS_FRI_GATE_PAPER_BATCH_BOUNDARY.md).
This partition script reuses that observed count but does not replay the
sealed package or independently bind its source. Its `N`, `B`, and `D0`
substitution is conditional.
If each maps without compression to one paper domain batch, its width is at
least 193. If its original and own-quotient functions both appear separately
in that same domain batch, width is at least 386. Neither native-to-paper
mapping is established; the actual theorem `M` stays null.

## Exact necessary arithmetic

Assume only for this calculation `N=2^20`, `B=2`, `D0=N B²=2^22`, and
`|F|=|QM31|=(2^31−1)^4`. With at least one BCS round `R`, the necessary
positive work-factor contribution is at least

```text
((T+1)/T) · (M−1) D0 / |F|,  T=2^64.
```

For the selected paper work-factor target `epsilon(T)/T <= 2^-96` at
`T=2^64`, this isolated factor can fit only when

```text
M−1 <= floor(|F| · T / (D0 · 2^96 · (T+1))) = 63,
M <= 64.
```

This is a **necessary**, not sufficient, condition even at the minimum
`R=1`. The theorem's full
batching expression has additional positive list-size factors. For an
unpartitioned 193-function batch the isolated factor alone is greater than
`2^-96` by almost 3×; for 386 functions it is greater by almost 6×. No
increase in query count reduces this batching factor.

| Conditional mapping | Functions | Minimum groups if each group only needs `M<=64` | Minimum groups if these isolated terms must add within target |
| --- | ---: | ---: | ---: |
| Original functions only | 193 | 4 | 130 |
| Original plus one own quotient each | 386 | 7 | 323 |

The last column follows from `sum_g(M_g−1)=functions−groups` for a disjoint
partition and the exact `<=63` total-excess floor. This is the isolated
**conservative union-bound scenario** if the group batching failures must be
summed. The first group count is a **hypothetical max-round scenario**: each
group's isolated batching term meets the target individually. The paper's
NIROP/BCS bound uses `(T+R) max_i epsilon_i` for a *joint IOPP whose rounds
already have valid reductions*. It does not establish that independently
running several Protocol-3 batches for one Gate relation can be composed by
max alone. The missing multi-instance correlated-agreement theorem must
decide which scenario, or another expression, applies. In the seven-group paired case,
even a balanced width near 55–56 leaves little or no room for the theorem's
positive list factors, other rounds, or BCS reduction.

## What a partitioned protocol would have to prove

1. Fix the partition deterministically from the sealed Gate source roster,
   before the post-OOD batch challenges. A group entry is a full
   `(root_epoch, column_index, OOD_sample_index, original_or_quotient)`
   identity; do not count two masks of one column as one quotient.
2. Commit the four source roots once at their existing fixed, main,
   interaction, and composition challenge epochs. Every partition reuses
   those exact roots and verifier-owned OOD claims. No group may recommit a
   copy of a column under a later root.
3. Derive a separately framed batch challenge for each group after all OOD
   values are fixed. Specify whether groups share fold challenges or have
   independent FRI tracks. This choice changes the correlated-agreement
   theorem premise and the BCS round count `R`.
4. Draw raw queries only after every group commitment, terminal vector, and
   required PoW nonce is bound. At any repeated source `(root, column, row)`,
   all groups must read the **same authenticated M31 word** from the same
   original four-root opening. Quotient values must be recomputed from that
   word and their own OOD claims. Sharing one opening proof is an
   implementation optimization; the proof must still show equality of every
   value consumed by every track.
5. Prove a multi-instance correlated-agreement and degree-correction result
   that composes the groups' soundness errors, including adaptive challenge
   timing, group selection, shared source roots, query reuse or independence,
   all fold/terminal errors, and the BCS `(T+R)` factor. Only then compute the
   actual theorem `M_g`, total error, proof size, and prover cost.

This plan could be prohibitively expensive even if a theorem exists. The
conditional additive floor requires hundreds of FRI instances for one
bucket; shared source openings save Merkle work but do not remove those line
commitments, challenge draws, or terminal checks. A larger challenge field,
different batching theorem, or different commitment design may be a better
path. No option is selected until the theorem and measured costs agree.
