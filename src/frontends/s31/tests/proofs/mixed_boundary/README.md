# Mixed boundary native base trace fixture

`trace_correspondence.zig` checks the exact `N=1..8` square/add chain used by
the [typed boundary correspondence fixture](../../acceptance/mixed_boundary/typed_boundary_correspondence.py).

Run the focused test from the S31 repository root:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-trace-correspondence -j1
```

The test compiles the pinned source and witness, then calls the **same native
base trace writers** as `direct_mixed_general_arithmetic.proveSourceBound`.
It independently calculates each field recurrence and checks all 512 fixed
rows, all 512×12 main cells, every gate equation, and:

1. The source-derived endpoint addresses, including the exact allocation for
   this chain family; all eight Gate endpoint words per call are read from the
   native bridge base columns.
2. Every bridge endpoint column contains its expected word on all 16 rows,
   and the native Gate tuple has the expected relation, address, and word.
3. Every one of the 16 chip steps has the expected input and output words in
   the chip's bit-reversed base trace storage; native tagged start and finish
   tuples match the boundary words.
4. The circuit base trace's eight public output words match an independent
   calculation of the final `sum` and `product` nodes.
5. For `N=1` and `N=8`, the production mixed package proves these exact source bytes, and its
   embedded-source native verifier accepts the serialized proof with the eight
   independently calculated public words. The proof header carries the same
   source digest, generated registry manifest digest, and circuit identity as
   the reconstructed schedule.
6. For those two proofs, changing any one of those three header digests, the interaction nonce, a
   claimed-sum byte, a proof-body byte, a public word, or the embedded source
   causes native verification to reject the proof.
7. Changing the main Merkle commitment root inside a decoded proof, then
   reserializing it, still passes the exact structural proof preflight. Native
   verification rejects this well-formed changed commitment.

This joins a concrete base-trace construction check to a serialized proof and
native verifier for two fixtures. It does not extract committed polynomial
values from the proof, establish AIR soundness independently of the Stwo
engine, or prove compiler correspondence for arbitrary programs.

## Logical producer roster

`producer_roster_correspondence.zig` covers the pinned direct source family for
every call count `N=1..8`:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-producer-roster -Doptimize=ReleaseFast -j1
```

It independently hashes each exact source, checks its compiled endpoint
schedule and 512-variable bound, then compares every production Qm31 operation
output address and multiplicity with the emitted fixed columns. The producer
categories map to Lean's modeled `checkedRoster` as follows:

| Native producer | Lean roster position |
| --- | --- |
| Zero, one, `u`, and derived basis/other constants | Finalization Qm31 Add/Mul rows |
| Private input and intermediate chip endpoint guesses | Finalization Qm31 PointwiseMul rows |
| Eight public output words | Qm31 Add copy rows; the verifier's public feeder **uses** these words and `u` |
| Ordinary packed arithmetic, unpack, and padding | Their Qm31 operation rows, only when output multiplicity is positive |
| Other component or permutation scratch yields | Empty for this family: those components have zero rows and there are no permutations |

The bridge consumes one Gate event per endpoint occurrence and contributes to
the corresponding producer row's fixed multiplicity. The fixture checks that
count, scans active output addresses for uniqueness and bounds, and rejects
mutated fixed addresses, multiplicities, duplicate producers, and out-of-range
producers. A dead output with multiplicity zero is intentionally absent from
Lean's `activeRows` list, although its fixed row and address are still checked.

This establishes the **address and multiplicity projection** of the Lean
logical roster for the honest compiled source, with an empty baseline-yield
suffix. It does not establish full `(address, value)` event equality, identify
arbitrary committed main-trace values with Lean events, or derive exact lookup
balance from an accepted proof. The verifier's authenticated fixed-root path
and the circuit AIR/PCS soundness remain separate obligations.
