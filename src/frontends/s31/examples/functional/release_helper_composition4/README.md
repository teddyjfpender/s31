# Nested helper bodies and inline captured functions

[`functional.s31`](functional.s31) composes three pure helpers. Inside
`composed`, an inline `fun` captures `a`, while `twice(a)` computes the array
argument passed to `apply`:

```s31
fn composed(a: [m31; 4]) -> [m31; 4] {
    apply(fun(v: [m31; 4]) -> [m31; 4] => a + v, twice(a))
}
```

The source evaluates the function argument and then the array argument.
Creating and passing the function emits no relation operation. The residual
relation is exactly:

```text
_s31_0 = add(x, x)
result = add(x, _s31_0)
```

[`manual.s31`](manual.s31) writes those two gates directly. On each M31 lane,
the constraints are `w − 2x = 0` and `result − x − w = 0`. For public
`x = [0, 1, 2, 7]`, the required result is `[0, 3, 6, 21]` modulo `2³¹−1`.
Both programs report 322 raw QM31 operation rows and 512 padded rows in the
native direct-gate profile.

The [native release acceptance](../../../tests/acceptance/compiler_correspondence/helper_composition_release.py)
requires the independent checker, production compiler and handwritten form
to agree on the complete relation. It compares canonical IR and native AIR
geometry, proves the functional program, accepts it through `verify-release`
with explicit package hashes, and rejects a changed public result. The hashes
in that test are derived from a fresh package; deployment must obtain them
from a separately trusted channel.
