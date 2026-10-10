# Nominal static records

Status: implemented in the `.s31` source frontend, 2026-10-10. The record is
a compile-time product over existing first-order values. The relation and
native verifier ABI remain first order.

## Why this shape

Programs such as Bitcoin header validation and fixed-width math produce
several values with different meanings but identical low-level limb shapes.
A named record lets a helper return these together and lets callers refer to
`division.quotient` or `header.target` without making the field name a
runtime witness. Nominal identity prevents two same-shaped records from
silently interchanging. Tuple products remain available for short positional
results.

The source form is a closed declaration followed by fully named construction:

```s31
struct DivResult { quotient: i32, remainder: i32 }

fn divide(a: i32, b: i32) -> DivResult {
    let (q, r) = std::int::div_rem(a, b);
    DivResult { remainder: r, quotient: q }
}
```

Fields are evaluated in declaration order even when the constructor spells
them in another order. Every field expression is evaluated exactly once.
Types are nominal: `DivResult` cannot be passed where another struct of the
same field types is expected. Field access is static and has no witness or
index input. Structs can nest and contain tuples of first-order values.
Function-valued fields, recursive layouts, record mutation, whole-record
`if`/`assert_eq`, and record-valued circuit boundaries are outside this
version. A function can take and return records; a circuit can construct and
use them internally.

## Type and lowering rules

For a declaration `R { f₀:T₀, …, fₙ:Tₙ }`, construction is well typed iff
the literal supplies every declared name exactly once, supplies no other
name, and each expression has exactly the declared type. `e.fᵢ` has type
`Tᵢ` iff `e` has nominal type `R`. There are no implicit record conversions.
All function bodies, including unused ones, pass this check before relation
emission.

After type checking, specialization applies the following layout in
declaration order:

```text
erase(R { f₀: e₀, …, fₙ: eₙ }) = (erase(e₀), …, erase(eₙ))
erase(e.fᵢ)                  = projectionᵢ(erase(e))
```

This is a source-stage equivalence, not a claim that computing `eᵢ` is free.
The constructor and projection emit no normalized relation node; arithmetic,
hashing, checks, and partial effects inside field expressions remain. Because
S31's normalized graph can share expressions, the useful cost invariant is
exact relation equality against the positional translation, rather than an
additive cost estimate. Equal normalized relations compile to the same
canonical IR and AIR geometry under the same profile. The
[worked source](../../../src/frontends/s31/examples/arithmetic/record_square_sum.s31)
and [positional translation](../../../src/frontends/s31/examples/arithmetic/record_square_sum_manual.s31)
are byte-for-byte equal at that boundary.

## Soundness and resources

- The type checker rejects missing, extra, duplicate, and mistyped fields,
  unknown field projections, nominal mismatches, function-valued fields, and
  record-valued circuit inputs or outputs.
- Construction is eager. The effect checker unions failures from every
  field before projecting one. A partial unused field cannot be concealed
  inside an inactive witness-dependent branch.
- No field label or record object crosses into the normalized relation,
  circuit, AIR, proof, verification key, or public statement. Existing
  first-order field constraints are unchanged.
- The parser caps declarations at 128 structs, fields at 64 per struct,
  nested layout depth at 32, and flattened first-order fields at 1,024.
  Forward references and recursive layouts are rejected.
- [Lean's erasure model](../../../formal/s31/S31/Gadgets/Functional/RecordValues.lean)
  proves that typed named construction and projection specialize to the
  direct residual polynomial and that accepted graph outputs have the
  specified value. The formal source-binding gate also recompiles two
  record/manual pairs and requires exact normalized relation equality.
- The [native acceptance gate](../../../src/frontends/s31/tests/acceptance/acceptance_records.py)
  compares canonical IR, AIR rows and preprocessing for both the field and
  signed-division examples, then requires generated native verification and
  changed-statement rejection. The [cost record](../measurements/language/record-zero-cost-2026-10-10.json)
  holds one local run. Timing is not used to establish the zero-cost claim.

The Lean theorem describes the typed erasure model; it is not a
machine-checked refinement of Python parsing, Zig gate emission, or Stwo
verification. Those production correspondence obligations remain part of the
broader S31 formalization.

## Boundary extension

Record-valued circuit parameters would require an explicit flattened public
ABI, field names and order in the sealed key, canonical assignment encoding,
per-field visibility, and native verifier checks for every leaf. This source
release deliberately leaves that boundary versioned separately. The current
records already make pure helper APIs and internal circuit logic substantially
clearer without changing proof soundness parameters or fixed costs.
