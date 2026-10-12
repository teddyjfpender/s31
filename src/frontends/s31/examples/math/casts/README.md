# Checked numeric casts

The three sources here preserve an integer's **numeric value** while changing
its fixed-width representation. `cast_checked_i16(i8(-1))` emits `0xffff`;
`reinterpret_i16` is a same-width bit reinterpretation and cannot do that job.

| Program | Source pattern | Result pattern | Numeric value |
| --- | --- | --- | ---: |
| [`i8_to_i16.s31`](i8_to_i16.s31) | `0xff` | `0xffff` | −1 |
| [`i16_to_i8.s31`](i16_to_i8.s31) | `0xff80` | `0x80` | −128 |
| [`i128_to_i64.s31`](i128_to_i64.s31) | Eight limbs ending in `0xffff` | Four limbs ending in `0xffff` | −5 |

To inspect and prove the second example:

```sh
python3 src/frontends/s31/python/s31.py lower src/frontends/s31/examples/math/casts/i16_to_i8.s31
python3 src/frontends/s31/python/s31.py trial src/frontends/s31/examples/math/casts/i16_to_i8.s31 src/frontends/s31/examples/math/casts/i16_to_i8.valid.json --lowering sparse-wide-gate --out zig-out/s31/i16-to-i8
```

The [fixed-width integer chapter](../../../docs/fixed-width-integers.md#checked-numeric-casts-by-hand)
shows the byte and sign equations. The [`casts.py`](../../../tests/acceptance/math/casts.py)
gate proves all three and rejects narrowing overflow in the native prover.
