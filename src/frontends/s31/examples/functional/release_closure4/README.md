# A captured lambda with a shadowed source name

[`functional.s31`](functional.s31) constructs a static function whose body
reads `saved`. That name refers to `x .* x` at the point where the function is
created. The later lexical `let saved = x + x in …` supplies the argument to
`apply`; it does not change the function's capture.

```s31
fn apply(f: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) -> [m31; 4] { f(v) }

circuit closure4(public x: [m31; 4]) -> public [m31; 4] {
    let saved = x .* x;
    let f = fun(v: [m31; 4]) -> [m31; 4] => let squared = v .* v in saved + squared;
    let result = let saved = x + x in apply(f, saved);
    result
}
```

The independent checker resolves the capture when `f` is bound, expands
`apply`, and assigns anonymous wire names to the two inner gates. The
complete residual relation is:

```text
saved    = mul(x, x)
_s31_0   = add(x, x)
_s31_1   = mul(_s31_0, _s31_0)
result   = add(saved, _s31_1)
```

[`manual.s31`](manual.s31) writes those same four gates. For each of the four
M31 lanes, the relation requires `saved − x² = 0`, `_s31_0 − 2x = 0`,
`_s31_1 − _s31_0² = 0`, and `result − saved − _s31_1 = 0`. With public
`x = [0, 1, 2, 7]`, the required public result is `[0, 5, 20, 245]` modulo
`2³¹−1`. The already computed `saved` wire is a witness value; the lambda
and its reference to `saved` add no additional witness word, relation node,
AIR row, or public ABI field.
Both programs report 324 raw QM31 operation rows and 512 padded rows in the
native direct-gate profile.

The [native release acceptance](../../../tests/acceptance/compiler_correspondence/closure_release.py)
compares the exact normalized relation, canonical IR, and reported AIR geometry
with the handwritten source. It proves this claim, runs `verify-release` with
explicit package hashes, and rejects a changed public result:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/closure_release.py
```

The strict certificate admits a unary `fun(v: [m31; 4]) -> [m31; 4]`
whose body contains up to sixteen `+` or `.*` operations, parentheses and
lexical `let … in` bindings over the argument and wires available at function
creation. General closures remain in the ordinary S31 frontend;
this is a bounded independent source-to-AIR check. The test obtains its pin
hashes from the package it just built; deployment must supply them through a
separately trusted channel.
