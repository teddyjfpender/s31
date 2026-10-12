# Passing an inline lambda through a typed function parameter

[`functional.s31`](functional.s31) supplies an anonymous function directly to
`apply_twice`. The function value is static. Both calls specialize its body:

```s31
fn apply_twice(f: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) -> [m31; 4] {
    let once = f(v);
    f(once)
}

circuit inline4(public x: [m31; 4]) -> public [m31; 4] {
    let result = apply_twice(fun(v: [m31; 4]) -> [m31; 4] => v .* v, x);
    result
}
```

The independent checker parses the inline argument as a typed unary lambda,
substitutes it for `f`, and emits these two residual gates:

```text
_s31_i1_0 = mul(x, x)
result    = mul(_s31_i1_0, _s31_i1_0)
```

[`manual.s31`](manual.s31) writes exactly those gates. For each lane, the AIR
relation requires `w − x² = 0` and `result − w² = 0`; therefore the claimed
output is `x⁴` modulo `2³¹−1`. For public `x = [0, 1, 2, 7]`, the result is
`[0, 1, 16, 2401]`. The lambda, function parameter, and both applications
add no relation node, witness word, AIR row, or public ABI field.
Both packages report 322 raw QM31 operation rows and 512 padded rows in the
native direct-gate profile.

The [native release acceptance](../../../tests/acceptance/compiler_correspondence/inline_lambda_release.py)
compares the complete normalized relation, canonical IR, and reported AIR
geometry of both sources. It proves the functional program, runs
`verify-release` with explicit package hashes, and rejects a changed public
result:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/inline_lambda_release.py
```

The test derives its pin hashes from the fresh package; deployment must obtain
them through a separately trusted channel. The strict certificate supports
inline lambdas only as arguments to monomorphic unary `Fn([m31; 4]) -> [m31; 4]`
parameters, with the same bounded pure body grammar as bound lambdas.
