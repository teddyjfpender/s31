# Returning a captured function and applying it directly

[`functional.s31`](functional.s31) computes `x²` inside `make`, returns a typed
function that captures that wire, and immediately applies the returned value:

```s31
fn make(a: [m31; 4]) -> Fn([m31; 4]) -> [m31; 4] {
    let squared = a .* a;
    fun(v: [m31; 4]) -> [m31; 4] => v + squared
}

circuit curried4(public x: [m31; 4]) -> public [m31; 4] {
    let result = make(x)(x);
    result
}
```

`make(x)` creates a static closure. The inner multiplication is an actual
computation, so it emits a gate. The returned function value and the two
applications emit no gate of their own. The complete residual relation is:

```text
_s31_i1_0 = mul(x, x)
result    = add(x, _s31_i1_0)
```

[`manual.s31`](manual.s31) writes exactly those gates. For each of the four
M31 lanes the constraints are `w − x² = 0` and `result − x − w = 0`. For
public `x = [0, 1, 2, 7]`, the required result is `[0, 2, 6, 56]` modulo
`2³¹−1`.
Both programs report 322 raw QM31 operation rows and 512 padded rows in the
native direct-gate profile.

The [native release acceptance](../../../tests/acceptance/compiler_correspondence/curried_release.py)
compares the complete normalized relation, canonical IR, and native AIR
geometry against the handwritten program. It proves the functional program,
runs `verify-release` with explicit package hashes, and rejects a changed
public result:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/curried_release.py
```

The test derives its pin hashes from the fresh package; deployment must obtain
them through a separately trusted channel. This strict certificate admits
returned unary `Fn([m31; 4]) -> [m31; 4]` values and bounded pure captures.
Other closure types remain in the ordinary S31 frontend.
The [Lean captured-square model](../../../../../../formal/s31/S31/Gadgets/Functional/Graph.lean)
proves strict graph output binding for the corresponding scalar `x²+x`
computation. It models the residual graph; the independent checker and native
acceptance above cover the checked-in source and package bytes.
