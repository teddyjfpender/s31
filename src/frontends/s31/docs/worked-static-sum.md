# Static choices and an erased payload, by hand

An S31 `enum` chooses a circuit shape **while the source is compiled**. Its
tag is not private proof data. A `match` on a known constructor selects one
arm, and the source evaluator still checks every arm and evaluates the
constructor's payload. A later, conservative dead-code pass removes an
unused payload calculation only when it is total and cannot fail.

The following is the source used by the
[native acceptance gate](../tests/acceptance/functional/static_sum_dce.py),
with the same computation and declarations laid out for reading:

```s31
enum Choice { Left: [m31; 4], Right: [m31; 4] }

fn step(v: [m31; 4]) -> [m31; 4] {
    v .* v + splat<4>(7_m31)
}

circuit p(public x: [m31; 4]) -> public [m31; 4] {
    let ignored = Choice::Left(x .* x);
    let result = iterate<16>(step, x);
    result
}
```

If $x=[0,1,2,7]$, the ignored payload computes
$x\mathbin{.*}x=[0,1,4,49]$ during source specialization. It has no path
to an output, assertion, or retained effect. The 16-step recurrence starts
with $x$ itself, and its first step is
$x\mathbin{.*}x+[7,7,7,7]=[7,8,11,56]$ in M31. Further steps repeatedly
square each of the four array positions and add 7 modulo
$p=2^{31}-1$.

```text
source:      Choice::Left(x .* x)       iterate<16>(step, x)
                         │                       │
specialize: static Left tag + `mul`       one `repeat` node
                         │                       │
live roots:          no consumer                public result
                         │                       │
DCE:             remove total `mul`       keep `repeat`
                                                 │
AIR:                         circuit endpoints + recurrence chip
```

The normalized relation after the pass contains one computation node:

```json
{
  "name": "result",
  "op": "repeat",
  "lhs": "x",
  "rounds": 16,
  "body": [
    {"op": "square"},
    {"op": "add_const", "constant": 7}
  ]
}
```

This is the same node as the hand-written source with the `ignored` line
removed. No `Choice` tag, match selector, or discarded multiplication is
placed in the circuit. The generated `direct-chip` package still has a
generic circuit for public endpoint binding and a dedicated repeated-step
AIR. In one measured native run, both sources had the same canonical
relation and full reported AIR geometry: 292 raw QM31 circuit rows, 512
padded QM31 rows, and 4,096 preprocessed cells. The counts include the
circuit boundary, not just the single relation node. See the
[acceptance script](../tests/acceptance/functional/static_sum_dce.py) for a
fresh measurement on the current checkout.

For the first recurrence row, the chip checks, independently for each array
position $j$, the equation

$$\operatorname{out}_j-\operatorname{in}_j^2-7=0.$$

For position 2 (zero-indexed), that is $11-2^2-7=0$. Other chip constraints
and the authenticated endpoint lookup connect the 16 rows into one path
from public $x$ to public `result`; otherwise a prover could assemble
unrelated valid square-plus-seven rows. [AIR and polynomials](air.md) works
through those exact chip equations and their quotient-polynomial check.

## Why the pass is conservative

`x .* x` is total field multiplication: every well-typed M31 input has a
result. Removing its unused node cannot make a previously invalid
assignment valid. This does **not** license removal of an unused checked
integer operation, inverse, division, hash, assertion, or future unknown
operation. Some are partial or impose proof obligations even when their
value is unused. The current erasable set is only `constant`, `add`, `sub`, `mul`,
`add_const`, and `mul_const` in sources that declare an enum. The compiler
typechecks/effect-checks before the pass, retains every non-allowlisted
node, keeps all ancestors of live outputs and assertions, and revalidates
the public ABI after pruning. The [DCE design note](../../../../design/s31/language/STATIC_SUM_DCE.md)
specifies the graph roots and fail-closed schema behavior.

The tag remains static by construction. A witness-dependent `if` does not
turn an enum into a private variant; such a boundary is rejected because a
single compiled relation needs a fixed shape. The proof for this program
claims that the public `result` is the 16-step recurrence of public $x$.
It does not prove that a runtime branch chose `Left`, and it does not reveal
an `ignored` payload because no payload witness remains.

The focused native test proves an honest instance, runs the generated
verifier, rejects a changed public result, and compares complete reported
AIR geometry with the direct source. These tests establish behavior for
this example. A full compiler correspondence theorem and the native
PCS/FRI soundness argument remain separate obligations in the
[correspondence ledger](../../../../design/s31/language/COMPILER_CORRESPONDENCE.md).
