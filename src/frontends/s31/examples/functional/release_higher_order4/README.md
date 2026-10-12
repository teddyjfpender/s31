# A function value with no circuit representation

[`functional.s31`](functional.s31) passes a named function as a value to
`apply`. The lexical `let f = twice_square in …` and the `Fn` parameter are
source-stage values. They disappear before the relation is built:

```s31
fn square(v: [m31; 4]) -> [m31; 4] { v .* v }
fn twice_square(v: [m31; 4]) -> [m31; 4] {
    let squared = square(v);
    squared + squared
}
fn apply(f: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) -> [m31; 4] { f(v) }
circuit higher_order4(public x: [m31; 4]) -> public [m31; 4] {
    let result = let f = twice_square in apply(f, x);
    result
}
```

The checker resolves `f` to `twice_square`, substitutes `x` for `v`, then
expands its call to `square`. The complete residual relation is
`_s31_i2_0 = mul(x, x); result = add(_s31_i2_0, _s31_i2_0)`.
[`manual.s31`](manual.s31) writes exactly those two gates. The function value
has no witness word, circuit gate, AIR row, or public ABI field.

For public `x = [0, 1, 2, 7]`, the public result is `[0, 2, 8, 98]` modulo
`2³¹−1`. The
[native acceptance gate](../../../tests/acceptance/compiler_correspondence/higher_order_release.py)
compares the full reported AIR geometry of both sources, proves the functional
program, passes `verify-release`, and rejects a changed public claim. The
certificate covers named unary `Fn` values of type
`Fn([m31; 4]) -> [m31; 4]`; lambdas, closures, and general higher-order
types remain outside this strict fragment.

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/higher_order_release.py
```
