# Lexical `let … in` has no AIR cost

[`functional.s31`](functional.s31) uses a nested source expression:

```s31
fn square(v: [m31; 4]) -> [m31; 4] { v .* v }
circuit lexical4(public x: [m31; 4]) -> public [m31; 4] {
    let result = let squared = square(x) in squared + squared;
    result
}
```

The bound expression is evaluated first. Because it has no explicit circuit
result name, the production compiler gives its multiplication the wire name
`_s31_0`. The lexical name `squared` refers to that wire inside the `in`
body. The body emits `result = add(_s31_0, _s31_0)`. The lexical binding
itself emits no gate, row, or witness cell. The
[`manual.s31`](manual.s31) source writes these two gates directly.

For public `x = [0, 1, 2, 7]`, the public result is `[0, 2, 8, 98]` modulo
`2³¹−1`. Each of the four lanes satisfies `_s31_0[i] = x[i]²` and
`result[i] = 2·_s31_0[i]`. The independent release checker reparses the
source and compares the complete normalized relation, canonical SSA and
native fixed-gate topology. The
[native acceptance gate](../../../tests/acceptance/compiler_correspondence/lexical_release.py)
builds both sources, compares their AIR geometry, proves the functional
source, runs `verify-release`, and rejects a changed public result.

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/lexical_release.py
```
