# Static enum choice inside a circuit conditional

The [functional source](functional.s31) has two kinds of choice. `Choice::Safe`
is a **source-only** enum constructor: the compiler knows its tag before it
builds a circuit. `flag` is a public bit whose value is known only when a
proof is made, so its `if` must become a constrained circuit selector.

```s31
fn choose(choice: Choice, flag: bit) -> [m31; 1] {
    match choice {
        Choice::Safe(v) => v + v,
        Choice::Risky(v) => if flag then std::math::inv(v) else v
    }
}

let result = if flag then choose(Choice::Safe(x), flag) else x;
```

The static call selects `Safe(v)` and substitutes `v = x`. Its `Risky` arm,
including the inverse and its inner dynamic `if`, is absent from the relation.
The remaining program is the [handwritten selector](manual.s31):

```s31
let result = select(flag, x, x + x);
```

The normalized relation has exactly two nodes: `a = x + x` and
`result = select(flag, x, a)`. For a constrained bit `b`, this means
`result = x + b(a − x) = x(1 + b)` in `Fₚ`, where `p = 2³¹ − 1`.
The bit constraint requires `b(b − 1) = 0`. There is no enum tag wire, inverse
gate, or selector for the static match. The acceptance gate compares the full
normalized relation and complete native AIR cost tuple with the handwritten
source. Both programs use the `direct-m31-v4` profile with **280 raw** and
**512 padded** QM31 operation rows and **4,096 preprocessed cells**. The
test pins these numbers and verifies these claims:

| Public `flag` | Private `x` | Public `result` | Meaning |
| ---: | ---: | ---: | --- |
| 1 | 7 | 14 | Selected doubling |
| 0 | 7 | 7 | Selected original value |
| 0 | 0 | 0 | Discarded inverse of zero imposes no constraint |

Replacing `Choice::Safe(x)` with `Choice::Risky(x)` fails compilation: the
selected inner `if` would require an inverse witness even when `flag = 0`.
Putting `std::math::inv(x)` in the `Safe` constructor payload also fails if
that constructor is built inside the outer dynamic branch; payload evaluation
is eager. These two rejections are checked before any native build.

Run the source and the native acceptance gate from the repository root:

```sh
python3 src/frontends/s31/python/s31.py explain \
  src/frontends/s31/examples/functional/static_enum_if/functional.s31
python3 src/frontends/s31/tests/acceptance/functional/static_enum_if.py
```

The acceptance test proves and verifies all three assignments with the
generated native verifier and rejects a changed public result in each case.
It is example-level evidence for the compiler and AIR. Static enums are not
yet in the independent four-lane `verify-release` certificate grammar, and
the full compiler-to-production-AIR correspondence remains open.
