# Optimized source to a bounded physical AIR roster

[`OptimizedPhysicalRoster.lean`](OptimizedPhysicalRoster.lean) closes a layout
premise in the modeled optimized source-to-AIR path. The exact source,
normalized JSON, and compact canonical IR byte checker admits a direct
four-lane add/multiply program with up to 16 arithmetic lets. The optimizer
sorts commutative operands and shares repeated expressions.

The Lean theorem `optimized_compact_cost_bound` proves that every accepted
optimizer result has **no more arithmetic producers than the source**, and
that the source has at most 16. A CSE hit reuses the earlier compact node;
the proof inspects both branches of the optimizer step and inducts over its
fold. `optimized_bytes_partition` then determines the grouped AIR layout:

```text
add rows = 476 - compact pointwise-multiply count
add rows + 1 subtraction row + 27 ordinary-multiply rows
         + compact pointwise-multiply rows + 8 fixed pointwise rows = 512
```

`optimized_bytes_exact_row_roster` proves that the modeled source and public
boundary cells have distinct physical positions within those 512 rows. It
also proves the source instruction selector sequence and that each compact
instruction has a corresponding projected AIR cell. The caller supplies the
three byte streams and one successful `checkBytes` result; it cannot choose
an alternative add-row count or an unbounded compact program.
`optimized_bytes_public_claim_with_roster` joins this result to the existing
local-polynomial/public-boundary theorem: under explicitly observed fixed
cells, locally accepted arithmetic, and pinned public I/O, the claimed output
equals the exact optimized source meaning and the modeled rows are in bounds.

## By hand: one shared source expression

```s31
circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {
  let a = x + x;
  let b = x .* x;
  let c = a + b;
  let d = b + a;
  d
}
```

The source has four arithmetic lets. Canonical operand order maps `d` to
`c`, so the compact circuit has three arithmetic producers. The proof checks
three source AIR cells and 25 public input/output cells: **28 distinct
physical row positions**. Their source positions are 3, 503, and 4; grouped
AIR rows can differ from source order because the native layout groups gate
kinds. The cell at row 503 is a four-lane pointwise multiplication, so its
four packed M31 values are multiplied independently.

For an input `[1, 2, 3, 4]`, the source values are:

| Value | Lane 0 | Lane 1 | Lane 2 | Lane 3 |
| --- | ---: | ---: | ---: | ---: |
| `a = x + x` | 2 | 4 | 6 | 8 |
| `b = x .* x` | 1 | 4 | 9 | 16 |
| `c = d = a + b` | 3 | 8 | 15 | 24 |

Each **lane** is one of the four M31 coordinates packed into one QM31 circuit
wire. This table shows ordinary field arithmetic on small values; operations
in general reduce modulo `2^31 - 1` independently in each lane. The modeled
AIR polynomial for an add cell forces its output wire to equal the sum of its
two input wires. The pointwise-multiply cell forces the four M31 coordinate
products. The source-to-output theorem in
[`OptimizedSourceAirRows.md`](OptimizedSourceAirRows.md) uses those local
equations and an explicit public input/output boundary to recover the
source's claimed result.

## Exact boundary

This is a universal Lean theorem about the **modeled** byte checker,
optimizer, and physical schedule. It does not show that production Zig emits
the modeled roster for every accepted source, that a committed fixed column
equals the exported column, or that an accepted STARK proof authenticates
its decoded rows. The independent Python v3 package checker compares a
bounded optimized source to native topology and all eight exported fixed
columns, but that is an executable check of a finite build. The normal v2
package admission remains separate. Gate lookup, PCS openings, FRI, and
Fiat–Shamir are further proof-system obligations.

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.OptimizedPhysicalRoster
lake env leanchecker S31.Gadgets.Functional.Correspondence.OptimizedPhysicalRoster
```
