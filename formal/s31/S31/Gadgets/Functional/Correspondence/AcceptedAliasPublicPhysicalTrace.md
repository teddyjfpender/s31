# A public boundary witness for every admitted alias DAG

`AcceptedAliasPublicPhysicalTrace.lean` extends the constructive source and
public-boundary witness from direct spelling to every program accepted by the
exact three-file alias checker. The theorem takes source `.s31` bytes,
normalized relation bytes, compact canonical IR bytes, a checked certificate,
and any four-lane public input. It **constructs** one wire assignment that
satisfies all modeled source, input-pack, input-copy, output-mask,
output-inverse, and output-copy arithmetic cells. The same assignment gives a
512-row decoded trace whose installed local arithmetic roots all vanish.

The proof factors the existing witness construction at its real semantic
boundary: `executeNormalized certificate input = some output`. The direct
and alias byte checkers each establish that equation from their own source
bytes. The subsequent source and public cell construction is shared.

For example:

```s31
circuit early_alias(public x: [m31; 4]) -> public [m31; 4] {
  let base = (x);
  let a = ((base) .* (base));
  let saved = (a);
  let b = base + saved;
  let c = ((saved) .* (b));
  let returned = saved;
  returned
}
```

The aliases `base`, `saved`, and `returned` add no arithmetic producers. The
checked certificate has three instructions: `a = x .* x` at circuit address
23, `b = x + a` at address 24, and `c = a .* b` at address 25. The output ID
is **1**, selecting `a`; `c` is still evaluated and constrained even though
its output has zero Gate uses. With input `[1, 2, 3, 4]`, the source values
are `a = [1, 4, 9, 16]`, `b = [2, 6, 12, 20]`, and
`c = [2, 24, 108, 320]`. The public result is `a`.

Two source pointwise multiplications leave 474 grouped add rows. The source
add occupies physical row 3 and the two source pointwise multiplications
occupy rows 502 and 503. The modeled projected roster contains three source
cells, fourteen input cells, and eleven output cells. All twenty-eight cell
equations use one coherent wire assignment. The stronger
`checked_alias_projected_physical_trace_exists` theorem proves that these
twenty-eight cells occupy **distinct rows below 512** and that the fixed tuple
at each row equals its modeled selector, input/output addresses, and output
use count. Three source rows are easy to inspect by hand:

| Physical row | Producer | `(add, sub, mul, pointwise)` | `(in0, in1, out)` | Output uses |
|---:|---|---|---|---:|
| 3 | `b = x + a` | `(1, 0, 0, 0)` | `(22, 23, 24)` | 1 |
| 502 | `a = x .* x` | `(0, 0, 0, 1)` | `(22, 22, 23)` | 6 |
| 503 | `c = a .* b` | `(0, 0, 0, 1)` | `(23, 24, 25)` | 0 |

`a` is read once by `b`, once by `c`, and four times by the public output
masks. `c` is still locally constrained at row 503 despite having zero output
uses. The other 484 rows are synthetic zero-add padding in this theorem's
trace construction.

This is a **modeled local arithmetic satisfiability** result for the admitted
bounded public direct-Gate fragment, including aliases and early returns. It
establishes exact **modeled projected** row placement and fixed tuples. It
does not establish equality to native full fixed columns, native constant and
padding witness values, exact Gate balance, committed trace authentication,
or PCS/FRI soundness. Those remain separate joins to the release verifier.

After building formal dependencies, check the theorem with:

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace)
```
