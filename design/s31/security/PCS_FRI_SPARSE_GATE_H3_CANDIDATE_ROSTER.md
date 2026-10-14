# Accepted sparse Gate H3 candidate roster

The accepted `arith4` sparse Gate proof now has an exact four-root OOD claim
map. This note turns that map into a **candidate** list of independent
original and own-quotient functions. The proof that produced the map still
uses one accumulated legacy DEEP quotient; it has not proved these candidate
functions low degree. The [machine-readable roster](evidence/sparse-gate-p05-h3-candidate-roster-2026-10-14.json)
binds the accepted key, proof, and canonical 73-claim map by SHA-256.

## What is placed into each height

For each source column, place its original function once in its FRI-extended
height. For each of that column's verifier-owned OOD claims, place a separate
own-quotient function in the same height. Preserve fixed, main, interaction,
composition root order within a height; those roots were committed at four
different challenge epochs. The source column is reused for two claims where
needed, but it is not duplicated as an original function.

| Extended log | Source originals | Explicit OOD own quotients | Direct candidate width | Two-sample columns | Width if each legacy periodicity word is another function |
|---:|---:|---:|---:|---:|---:|
| 17 | 14 | 18 | 32 | 4 | 36 |
| 11 | 28 | 32 | 60 | 4 | 64 |
| 5 | 19 | 23 | 42 | 4 | 46 |
| Total | 61 | 73 | 134 | 12 | 146 |

The `73` quotients refer to **actual accepted QM31 points and values**, in
the [claim map](evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json).
The [theorem-facing occupancy map](PCS_FRI_SPARSE_GATE_PAPER_ENSEMBLE.md)
distinguishes this shared-original `61+73` list from a literal pair per
accepted claim (`73+73`, widths `36/64/46`). The latter has the same numeric
maximum `64` as the periodicity-added row below for a different reason; the
lists of functions are not interchangeable.
The twelve extra periodicity words are separate from those 73 explicit
claims. The existing native sampled-row adapter constructs one such word
before the two explicit samples for each two-sample interaction column: it
shifts sample 1's point by the native period step and keeps sample 1's claim.
Whether this becomes a separate function in the published S-two ensemble is
unproved. The manifest therefore records both candidate widths and leaves
the actual native-to-paper batch width `M` null.

### One column by hand

Interaction root 2, column 20 has extended log 17. It is original slot 2 in
the height-17 candidate. Its two accepted OOD claims are global indices 57
and 58, so they occupy direct own-quotient slots 2 and 3 at that height.
Claim 57 is sample 0 at the shifted QM31 point; claim 58 is sample 1 at the
base OOD point. In canonical four-limb form:

| Claim | Point x | Point y | Claimed value |
|---:|---|---|---|
| 57 | `[1720477104, 1628715618, 1676490995, 791680055]` | `[1517122051, 1221150412, 186212545, 1933488693]` | `[634728825, 1899555768, 332269956, 401485162]` |
| 58 | `[2083843127, 1653782313, 1513710029, 743042316]` | `[944408642, 962976616, 1604300235, 1050785851]` | `[861003889, 720206652, 1097072835, 1344070642]` |

At an authenticated source row `P=(x,y)` with value `v=f(P)`, the current
native row adapter computes each sample's own quotient as

```text
Q_s(P) = [c_s v − a_s y − b_s]
         / [(x_s⁰ − x)y_s¹ − (y_s⁰ − y)x_s¹]
```

Here `(a_s,b_s,c_s)` is `complexConjugateLineCoeffs` for that exact OOD point
and claim. This equation is checked locally in
[`p05_own_quotient_rows.zig`](../../../formal/s31/tests/lib/p05_own_quotient_rows.zig).
It says how to calculate an opened row's quotient. A whole-oracle degree
test must still bind every original and own quotient to low-degree committed
functions across the domain.

## What Lean checks, and what the paper still needs

[`SparseP05AcceptedH3Roster.lean`](../../../formal/s31/S31/Gadgets/PcsFri/SparseP05AcceptedH3Roster.lean)
checks the full 61-column finite roster: every `(root,column)` appears once
as an original and every claim index `0..72` appears once as a direct own
quotient. It derives the three exact height counts and the `32/60/42` and
`36/64/46` candidate sizes from generated source-bound column data. Its
paper-facing results are **conditional**: if these candidate functions are
exactly the paper's per-domain batches without compression or extra
functions, Protocol 3's common zero-padded width would be `M=60`, or `M=64`
if each periodicity word is a separate function. That mapping is not proved.

Under that premise, both widths satisfy the prior *isolated ungrinded*
batching-term cap `M≤1024` for candidate `N=2^16`, `B=2`, `T=2^64`,
`D₀=N B²`, minimum BCS `R=1`, and **zero certified batch grinding credit**.
This says nothing about the other positive error terms, the joint IOPP/BCS
composition, or native security bits. The accepted legacy verifier never
selects a paired whole-oracle degree test, so P05 and release admission stay
open.

## Reproduce the map

From the S31 repository root, first run the accepted-proof fixture, then
check the derived roster and its Lean data:

```sh
bash formal/s31/tests/run_pcs_fri_p05_sparse_accepted_geometry.sh
python3 scripts/release/pcs_fri_sparse_p05_h3_roster.py --check
python3 -m unittest scripts.tests.test_pcs_fri_sparse_p05_h3_roster
cd formal/s31 && lake build S31.Gadgets.PcsFri.SparseP05AcceptedH3Roster
```

The report's source-bound accepted proof remains identified by key SHA-256
`7d4cdaab4e446aaa2c357e28f077e469412f45a17c660e8d4434cca216dccfc7`
and proof SHA-256
`04eaca23d8a6c7fc977b24a3d925aaabcbb727fa4fa30f30c81864e24a158e39`.
