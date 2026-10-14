# Static left fold: Horner evaluation

[`horner.s31`](horner.s31) evaluates one quadratic polynomial at
four field values in parallel. `horner_step(x)` returns a closure that captures
the four-lane `x` wire. The source-only array `[b, c]` and the closure are
compile-time structure: neither is a proof value or an AIR column.

```s31
let step = horner_step(x);
let out = std::array::fold(step, a, [b, c]);
```

The left fold means `step(step(a, b), c)`. The function, initial
value and array elements are evaluated once before its step calls; then each
step is specialized in order. The result is `(a*x+b)*x+c`, modulo
`p = 2³¹−1`, for each of the four array positions. Position means one
independently constrained M31 field element, not one separate proof.

| Position | Private `x` | Private `a` | Private `b` | Private `c` | Claimed `out` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 1 | 5 | 9 | 9 |
| 1 | 1 | 2 | 6 | 10 | 18 |
| 2 | 2 | 3 | 7 | 11 | 37 |
| 3 | 7 | 4 | 8 | 12 | 264 |

[`manual.s31`](manual.s31) writes the same two steps with first-order
arithmetic. Both forms emit exactly these four relation nodes, with the same
operand order and no fold node:

```text
t0  = a * x          // mul
t1  = t0 + b         // add
t2  = t1 * x         // mul
out = t2 + c         // add
```

Starting the fold at `a` avoids a useless `0*x` gate. For each position `i`,
the AIR constrains the four residuals `t0[i]−a[i]*x[i]`, `t1[i]−t0[i]−b[i]`,
`t2[i]−t1[i]*x[i]`, and `out[i]−t2[i]−c[i]` to zero modulo `p`.
Four positions fit one packed QM31 group wherever the backend schedules a
node; the backend adds binding and
proof-system rows around these source equations.

The [native acceptance](../../../tests/acceptance/functional/static_fold.py)
compares canonical IR hashes and the complete reported AIR cost tuple of the
fold and handwritten source. It checks this table independently, accepts a
native proof, and rejects a changed claimed output. The comparison measures
this program; it does not prove correspondence for all possible folds.
On the pinned `direct-gate` profile, both programs have 318 raw QM31 rows,
512 padded QM31 rows, and 4,096 preprocessed cells. Those counts include
the backend's input, output, and proof machinery.

`fold` admits a named function or captured closure of type `(A, X) -> A`,
where `A` and `X` are first-order circuit types. The source-only array must
have 1–64 equally typed `X` elements. Partial effects in any element or step
remain visible to the conditional effect checker.
