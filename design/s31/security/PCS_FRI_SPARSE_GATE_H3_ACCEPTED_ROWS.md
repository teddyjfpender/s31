# Accepted sparse Gate H3 row semantics

This is a candidate-only bridge from one accepted sparse Gate proof to the
separate original and own-quotient rows that a paired FRI protocol would need.
The verifier still accepts that proof using its legacy accumulated DEEP
quotient. The checks here do **not** commit or degree-test separate quotient
oracles, identify the S-two paper's padded batch width `M`, or certify security
bits.

## Which values come from the accepted proof

`inspect-p05` first runs the ordinary sealed-key native verifier and capture
admission. Its opt-in report now includes the first raw lifted query position
and the 61 source-column values authenticated at that query. The report also
contains the previously captured 73 exact QM31 OOD points and claims. The
[accepted geometry file](evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json)
is reproduced by the honest proof fixture for every accepted claim, query,
and source-row field; the local package manifest hash can vary between build
directories. A wrong key emits no report. Its accepted key and proof SHA-256
values are respectively
`7d4cdaab4e446aaa2c357e28f077e469412f45a17c660e8d4434cca216dccfc7`
and `04eaca23d8a6c7fc977b24a3d925aaabcbb727fa4fa30f30c81864e24a158e39`.
The native fixture separately pins SHA-256
`cb93d734058ac7f0cca69838e265e4447d9a5f26b67aa28d012c1426ddb9f5d7`
over the lifting log, first raw query, and all 61 ordered source values.

The first raw lifted query is `90,528` in the log-17 domain. Its native
bit-reversed circle-domain index is `2,829`, giving the native circle point
`(X,Y)=(422,774,917, 1,575,360,667)`. For interaction root 2, column
20, the authenticated source value at that query is `449,376,028`. That
column has two different accepted OOD samples, global claim indices 57 and
58:

| Claim | OOD x in four M31 limbs | OOD y in four M31 limbs | Claimed value in four M31 limbs |
|---:|---|---|---|
| 57 | `[1720477104,1628715618,1676490995,791680055]` | `[1517122051,1221150412,186212545,1933488693]` | `[634728825,1899555768,332269956,401485162]` |
| 58 | `[2083843127,1653782313,1513710029,743042316]` | `[944408642,962976616,1604300235,1050785851]` | `[861003889,720206652,1097072835,1344070642]` |

## The row calculation

Write the OOD point as `(x₀+u x₁, y₀+u y₁)`, its claimed value as
`v₀+u v₁`, and the queried base-circle row as `(X,Y)` with authenticated
source value `f(X,Y)`. Native `complexConjugateLineCoeffs` constructs the
conjugate-point interpolation line `(a,b,c)`. The separate row word is

```text
              c·f(X,Y) − a·Y − b
Q(X,Y) = ───────────────────────────────
         (x₀−X)·y₁ − (y₀−Y)·x₁
```

The denominator is a `CM31` determinant; the numerator and quotient are
`QM31`. A zero denominator or a degenerate OOD line rejects this candidate
row. In the accepted example above, the two **lifted-domain** quotient words
are respectively `[0,0,1541021748,1079523661]` and
`[0,0,1882278765,392788821]`. Those are field limbs, not decimal encodings
of one large integer. The [native fixture](../../../formal/s31/tests/pcs_fri_p05_sparse_h3_accepted_rows_native.zig)
checks these exact results and checks the same direct formula against the
production `friAnswers` row evaluator for **all 73 claims**.

The candidate H3 roster has source log sizes 17, 11, and 5. For a lower
height `h`, its source row is the native projection of raw query 90,528 onto
the log-`h` domain. The candidate OOD point is the accepted point doubled
`17−h` times. The fixture independently evaluates this **source-domain**
quotient and compares it to `friAnswers` at log `h`. This distinction matters:
the accepted legacy DEEP answer evaluates every column at the lifted log-17
row, whereas a separate function assigned to height `h` must use its own
domain. The fixture checks the proposed row arithmetic; a future selected
protocol must commit and test those functions.

Twelve interaction columns have two explicit samples. Native PCS inserts a
third, periodicity relation word before samples 0 and 1. The fixture checks
the exact periodic shift and the ordered weighted sum
`Q_periodic + α Q_0 + α² Q_1`, with `α=7` as a local test constant, in both
lifted and source domains. It does not claim that this test constant is a
transcript challenge or that the periodicity word is an additional paper
batch function.

## Formal boundary

[`SparseP05AcceptedH3Rows.lean`](../../../formal/s31/S31/Gadgets/PcsFri/SparseP05AcceptedH3Rows.lean)
proves the row quotient's cross-multiplication identity when its determinant
is nonzero and its exact scaling to the two-point affine interpolation
residual when the imaginary y-coordinate is nonzero. Combined with the
[finite accepted roster](../../../formal/s31/S31/Gadgets/PcsFri/SparseP05AcceptedH3Roster.lean),
the guarded identity transfers to every accepted claim index `0..72` under
explicit per-row premises. The concrete first queried rows satisfy those
guards in the Zig fixture. Lean does not yet prove that the native committed
columns are low-degree circle-basis polynomials, or that the separate
quotients agree at every source-domain row. It also does not replace the
four-root authenticated opening or BCS reductions.

## Run the checks

From the S31 repository root:

```sh
bash formal/s31/tests/run_pcs_fri_p05_sparse_accepted_geometry.sh
bash formal/s31/tests/run_pcs_fri_p05_sparse_h3_accepted_rows_native.sh
python3 -m unittest scripts.tests.test_pcs_fri_sparse_p05_h3_roster
cd formal/s31 && lake build S31.Gadgets.PcsFri.SparseP05AcceptedH3Rows
```

P05 remains open. The source-bound H3 candidate sizes are still
`32/60/42` direct and `36/64/46` if each periodicity word is separate, but
the actual native-to-paper `M` remains null.
