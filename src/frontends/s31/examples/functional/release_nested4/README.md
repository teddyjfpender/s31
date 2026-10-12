# Nested static applications erase to three gates

[`functional.s31`](functional.s31) passes the result of `make(x)` as a
function argument to `identity`, then passes `double(x)` as an array argument
to the returned function:

```s31
let result = identity(make(x))(double(x));
```

The source evaluates these arguments from left to right. `make(x)` computes
`x²` and returns a function capturing that wire. `double(x)` computes `2x`.
Applying the returned function adds the two results. The complete residual
relation is:

```text
_s31_i1_0 = mul(x, x)
_s31_0    = add(x, x)
result    = add(_s31_i1_0, _s31_0)
```

[`manual.s31`](manual.s31) writes these three gates directly. On each M31
lane, the constraints are `w₁ − x² = 0`, `w₂ − 2x = 0`, and
`result − w₁ − w₂ = 0`. For public `x = [0, 1, 2, 7]`, the required output is
`[0, 3, 8, 63]` modulo `2³¹−1`. The function values, captures and applications
add no witness columns or AIR rows. Both forms report 323 raw QM31 operation
rows and 512 padded rows in the native direct-gate profile.

The [native acceptance](../../../tests/acceptance/compiler_correspondence/nested_release.py)
compares the normalized relation, canonical IR, native AIR geometry, and
strict release proof with the direct program. It also rejects a changed
public result. The fixture derives its pin hashes from a fresh package;
deployment must receive those hashes through a separately trusted channel.
