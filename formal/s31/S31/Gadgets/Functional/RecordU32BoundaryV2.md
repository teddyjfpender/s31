# Public `u32` record boundary: two limbs, one value

The source program below passes one 32-bit word through a named record. A
second output name illustrates the ABI's result-alias rule. The production
`direct-gate` profile admits a public `u32` input and same-type public result
aliases; the Lean module
[`RecordU32BoundaryV2.lean`](RecordU32BoundaryV2.lean) models the corresponding
integer and statement operations after a descriptor has been validated.

```s31
struct Request { amount: u32 }
struct Result { first: u32, again: u32 }

circuit echo_amount(public req: Request) -> public Result {
    Result { first: req.amount, again: req.amount }
}
```

For `req.amount = 0x12345678 = 305419896`, the two little-endian `u16`
limbs are `low = 0x5678 = 22136` and `high = 0x1234 = 4660`:

```text
integer value = low + 2^16 × high
              = 22136 + 65536 × 4660
              = 305419896

named statement leaves:
  req.amount     [22136, 4660]   public input wire w0
  result.first   [22136, 4660]   result reference to w0
  result.again   [22136, 4660]   result reference to w0

eight native public-word slots:
  [22136, 4660, 22136, 4660, 0, 0, 0, 0]
             input       one distinct result
```

The result has two *named* leaves, but both refer to one relation wire.
The statement parser checks that both result claims match the input claim.
Only one distinct result wire is projected into the proof's public-word
vector. Aliasing does not create an arithmetic node, an AIR row, or another
public proof word. The source and ABI metadata still change the key and
statement identity.

For each limb `L`, the direct-gate circuit supplies 16 Boolean witnesses
`b_0,...,b_15` and checks these equations over M31:

```text
b_j × (b_j − 1) = 0              for j = 0,...,15
L − Σ(j=0..15) 2^j × b_j = 0
```

The Boolean equations force every bit to 0 or 1. The reconstructed sum is
at most `65535`, below the M31 modulus, so the equation cannot hide a larger
integer by field wraparound. This applies separately to low and high. There
is no M31 element equal to the whole 32-bit word: `0xffffffff` exceeds M31.
The 32-bit meaning comes from the ordered pair of bounded limbs. The AIR
checks the emitted arithmetic gates row by row; the verifier binds their
public input and result cells to the four nonpadding statement words.

The Lean theorems prove both directions of this *integer* encoding:

```text
pack(unpack(value)) = value       for 0 ≤ value < 2^32
unpack(pack(low, high)) = [low, high]
                                  for low, high < 2^16
```

`checked_u32_claim_packs` proves that a modeled `u32` descriptor with width
two and an accepted claim has two bounded limbs and one value below `2^32`.
`admitted_u32_alias_same_value` combines this fact with the existing modeled
same-wire alias check. The finite examples check the exact public vector,
a changed alias, and an out-of-range high limb (`65536`).

The scope starts after source parsing, nominal type checking, relation
descriptor validation, and canonical JSON/key binding. Lean does not yet
prove those production Python/Zig steps refine this model. Nor does this
module prove the Boolean gates were emitted by the compiler, that the native
AIR/PCS enforces those gates, confidentiality, or end-to-end STARK soundness.
The existing native acceptance for
[`record_public_u32.s31`](../../../../../src/frontends/s31/examples/arithmetic/record_public_u32.s31)
checks concrete proofs and mutations independently.

Focused check from `formal/s31`:

```sh
LEAN_NUM_THREADS=1 lake build S31.Gadgets.Functional.RecordU32BoundaryV2
LEAN_NUM_THREADS=1 lake env leanchecker S31.Gadgets.Functional.RecordU32BoundaryV2
```
