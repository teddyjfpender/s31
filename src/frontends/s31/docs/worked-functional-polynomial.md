# One functional polynomial, from source to proof

This example uses a typed closure and a higher-order function, then proves the
same four-lane polynomial that a direct circuit would. The complete source is
checked in as [functional_poly4.s31](../examples/arithmetic/functional_poly4.s31):

```s31
use std@1;

// Applying a source function emits the polynomial's field operations only.
fn apply4(f: Fn([m31; 4]) -> [m31; 4], value: [m31; 4]) -> [m31; 4] {
    f(value)
}

circuit functional_poly4(private x: [m31; 4]) -> public [m31; 4] {
    let constant = splat<4>(7_m31);
    let quadratic = fun(v: [m31; 4]) -> [m31; 4] =>
        std::math::poly_eval(v, [constant, splat<4>(3_m31), splat<4>(2_m31)]);
    let result = apply4(quadratic, x);
    result
}
```

`Fn` and `fun` live at compile time. `quadratic` captures `constant`, but the
capture is a source binding, not a proof witness. The `apply4` call specializes
its body with `v = x`. Coefficients in `poly_eval` are ordered from **low to
high degree**, so this source means $f(x)=7+3x+2x^2$ in
$\mathbb{F}_{2^{31}-1}$, independently in four lanes. `x` is private: the
public claim is that some valid four-word private input produces `result`.
Private here describes the public statement; see [proof privacy](proof-privacy.md)
for the separate zero-knowledge status.

## What the compiler retains

Horner evaluation rewrites the expression as $(2x+3)x+7$. The normalized
relation contains these four nodes, in order:

```text
w1     = mul_const(x, 2)
w2     = add_const(w1, 3)
w3     = mul(w2, x)
result = add_const(w3, 7)
```

The [direct source](../examples/arithmetic/functional_poly4_manual.s31)
emits exactly the same normalized relation, including operation order,
constants, types and references. The function value, call, capture, and
static coefficient group add no relation nodes. They also add no AIR rows.
Different source-file hashes remain bound to their respective build packages.
Under `direct-gate`, the complete native circuit has **318 raw QM31 operation
rows**, padded to 512, and 4,096 fixed preprocessing cells. The four retained
relation nodes account for only part of that total; input, address and public
binding gates are included. The direct source has the same canonical relation,
AIR geometry, fixed-column root, public-binding parameters and FRI settings.

For the checked [input assignment](../examples/arithmetic/functional_poly4.valid.json),
the arithmetic can be done by hand. A **lane** is one position in a
four-word M31 array; the same constrained operation acts on every position.
The four lane values pack into a QM31 circuit wire, then the verifier's public
binding checks each output word.

| Value | Lane 0, `x=0` | Lane 1, `x=1` | Lane 2, `x=2` | Lane 3, `x=7` |
| --- | ---: | ---: | ---: | ---: |
| `w1 = 2x` | 0 | 2 | 4 | 14 |
| `w2 = w1+3` | 3 | 5 | 7 | 17 |
| `w3 = w2·x` | 0 | 5 | 14 | 119 |
| `result = w3+7` | 7 | 12 | 21 | 126 |

These inputs are small enough that no modular wrap appears. With larger
inputs, each cell is reduced modulo $p=2^{31}-1$.

## What the proof constrains

At the arithmetic rows, the gate AIR requires zero for the selected operation
equation in each of the four field coordinates. Written schematically for
lane $j$:

$$
\begin{aligned}
C_{1,j}&=w_{1,j}-2x_j,\\
C_{2,j}&=w_{2,j}-w_{1,j}-3,\\
C_{3,j}&=w_{3,j}-w_{2,j}x_j,\\
C_{4,j}&=y_j-w_{3,j}-7.
\end{aligned}
$$

The actual circuit also has input packing, constant, address lookup and
public-output gates. Its fixed columns identify each operation and wire
address. The witness columns hold values such as `w1`, `w2` and `w3`. Gate
lookup forces a consumer of `w2` to read the same value that its producer
wrote; the public-output boundary forces `y` to equal the claimed four words.
The prover commits trace columns as polynomial evaluations. The verifier
checks random openings, the composition constraints and FRI degree bounds, so
it does not need to read every row. [AIR and polynomials](air.md) derives this
mechanism on a tiny trace.

The [Lean math theorem](../../../../formal/s31/S31/Gadgets/Functional/MathLibrary.lean)
proves Horner's field meaning and that arbitrary satisfying witnesses in its
strict field graph bind the claimed result. The [native library gate](../tests/acceptance/functional/library.py)
compiles functional and direct forms, compares circuit/AIR geometry, runs the
independent value oracle, proves a fixture and rejects a changed claim. Lean
does not yet prove that the Python compiler or production Zig AIR implements
its formal graph for every source program.
