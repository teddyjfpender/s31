# Four public words from a packed control result

This is the public-output continuation of [the control gadget AIR bridge](ControlGadgetAir.md).
The accepted source shape is still exactly one public scalar `x`, two private
four-lane M31 values, and `is_zero(x)`, `select`, then `inv`. The source has
one public four-lane result. The native Gate compiler stores that result in
one packed QM31 wire; the public statement uses four separate 32-bit words.

```s31
use std@1;
circuit control_air(public x: [m31; 1], private a: [m31; 4],
                    private b: [m31; 4]) -> public [m31; 4] {
    let z = std::field::is_zero(x);
    let picked = std::field::select(z, a, b);
    let result = std::math::inv(picked);
    result
}
```

For `x=0` and `b=[1,2,4,8]`, the earlier AIR equations force `picked=b` and
`result=[1,1073741824,536870912,268435456]` modulo `p=2³¹−1`.
Here is the rest of the computation by hand. Let `eᵢ` be the QM31 basis word
with a one in lane `i`, and `Q` the packed `result` wire.

| Lane | Extract from `Q` | Scalar after basis inverse | `M31ToU32` low, high u16 | Public pin |
|---|---|---:|---:|---|
| 0 | `m₀ = Q .* e₀` | `1` | `(1, 0)` | `P₄` |
| 1 | `m₁ = Q .* e₁`, then `m₁ · e₁⁻¹` | `1073741824` | `(0, 16384)` | `P₅` |
| 2 | `m₂ = Q .* e₂`, then `m₂ · e₂⁻¹` | `536870912` | `(0, 8192)` | `P₆` |
| 3 | `m₃ = Q .* e₃`, then `m₃ · e₃⁻¹` | `268435456` | `(0, 4096)` | `P₇` |

The basis inverse multiplication puts each coordinate into the **base M31
coordinate** of a QM31 wire. `M31ToU32` changes representation: a scalar
`r` becomes `(r mod 65536, floor(r / 65536), 0, 0)`. The pin Gate adds the
constant zero to that converted wire. Thus each pin decodes as
`low + 65536·high = r`, with `high < 32768`. `P₃` is the similarly converted
public input `x`; `P₈`, `P₉`, and `P₁₀` are zero padding. `P₂` is the
compiler's reserved basis wire.

The opt-in package audit, `scripts/compiler/control_air_audit.py`, verifies
package artifacts and exact source bytes, then captures the topology from the
validated native prover. Its v2 receipt checks the four basis masks, three
inverse-basis multiplication rows, five ordered `M31ToU32` rows, five live
pin Gate rows, three zero-padding pin rows, and the exact pin array. These
15 new Gate rows and five conversion rows are bound to the key-sealed fixed
column roster. Mutating an extraction, conversion input, pin producer, pin
order, or padding row is rejected by focused tests.

`ControlGadgetPublicPins.lean` proves that every modeled assignment satisfying
the matched generic Gate AIR rows and the stated conversion component law has
`decodeU32(P₄₊ᵢ) = result[i]` for all four lanes. It composes this with the
earlier zero-test, selection, and inverse theorem, so each decoded public
word is the inverse of its selected nonzero lane. Lean also proves the encoded
u16 limbs are canonical and decode to the original M31 representative.

The [conversion AIR continuation](ControlGadgetConversionAir.md) now derives
the component law from the installed `m_31_to_u_32` arithmetic residuals and
explicit `RangeCheck_16` and Gate tuple closure facts. It handles the
wraparound alias at `low=65535, high=32767` explicitly. It does not prove
that an accepted cryptographic proof authenticates the modeled pin cells or
binds the proof's
public statement to them. Those boundaries, PCS/FRI soundness, and complete
native physical-trace construction remain open. The separate local control
gadget completeness theorem handles the selected-lane existence condition.
The v0.1 release blocker remains closed.
