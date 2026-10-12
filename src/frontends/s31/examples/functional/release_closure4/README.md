# A captured lambda with a shadowed source name

[`functional.s31`](functional.s31) constructs a static function whose body
reads `saved`. That name refers to `x .* x` at the point where the function is
created. The later lexical `let saved = x + x in …` supplies the argument to
`apply`; it does not change the function's capture.

```s31
fn apply(f: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) -> [m31; 4] { f(v) }

circuit closure4(public x: [m31; 4]) -> public [m31; 4] {
    let saved = x .* x;
    let f = fun(v: [m31; 4]) -> [m31; 4] => saved + v;
    let result = let saved = x + x in apply(f, saved);
    result
}
```

The independent checker resolves the capture when `f` is bound, expands
`apply`, and assigns the inner lexical gate its anonymous wire name. The
complete residual relation is:

```text
saved    = mul(x, x)
_s31_0   = add(x, x)
result   = add(saved, _s31_0)
```

[`manual.s31`](manual.s31) writes those same three gates. For each of the four
M31 lanes, the relation requires `saved − x² = 0`, `_s31_0 − 2x = 0`, and
`result − saved − _s31_0 = 0`. With public `x = [0, 1, 2, 7]`, the required
public result is `[0, 3, 8, 63]` modulo `2³¹−1`. The already computed `saved`
wire is a witness value; the lambda and its reference to `saved` add no witness
word, relation node, AIR row, or public ABI field.
Both programs report 323 raw QM31 operation rows and 512 padded rows in the
native direct-gate profile.

The [native release acceptance](../../../tests/acceptance/compiler_correspondence/closure_release.py)
compares the exact normalized relation, canonical IR, and reported AIR geometry
with the handwritten source. It proves this claim, runs `verify-release` with
explicit package hashes, and rejects a changed public result:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/closure_release.py
```

The strict certificate admits only a unary `fun(v: [m31; 4]) -> [m31; 4]`
whose body is one `+` or `.*` operation over the argument and wires available
at function creation. General closures remain in the ordinary S31 frontend;
this is a bounded independent source-to-AIR check. The test obtains its pin
hashes from the package it just built; deployment must supply them through a
separately trusted channel.
