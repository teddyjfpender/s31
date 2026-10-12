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
   The fixture also finds the unique positive-multiplicity Gate producer for
   the source's zero, four basis units, packed first and last states, and
   three inverse-basis constants. It checks those expected values in the
   emitted main output cells. These are the concrete writer-side `ValueAt`
   pins used by the N1/N8 Lean public-output schedule.
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
every call count `N=1..8` and a three-call fork in which two chips consume the
same arithmetic result:

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
producers. In the fork, it independently recomputes all 512 fixed
multiplicities from ordinary circuit reads plus one read per bridge endpoint;
each shared chip input receives two additional reads. A dead output with
multiplicity zero is intentionally absent from Lean's `activeRows` list,
although its fixed row and address are still checked.

This establishes the **address and multiplicity projection** of the Lean
logical roster for the honest compiled source, with an empty baseline-yield
suffix. It does not establish full `(address, value)` event equality, identify
arbitrary committed main-trace values with Lean events, or derive exact lookup
balance from an accepted proof. The verifier's authenticated fixed-root path
and the circuit AIR/PCS soundness remain separate obligations.

## Queried opening authentication

`opening_authentication.zig` proves one source-pinned three-call private
program and decodes its accepted proof. It changes one queried value in the
first and last column of the fixed tree and of every native slot's main and
interaction span: circuit, two pair chips, two pair bridges, one many chip,
and one many bridge. It also changes one Merkle authentication-path sibling
in each of the four commitment trees (fixed, main, interaction, quotient). The 34
changed proofs pass structural postcard preflight and fail native verification
at `RootMismatch` for their own PCS tree. The path controls first require
byte-exact proof decode/encode round-trip and then exactly one changed proof
byte. Run it with:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-opening-authentication -Doptimize=ReleaseFast -j1
```

This checks that a queried value in every admitted component role and one
sampled path sibling per commitment tree are authenticated to the accepted
roots. It does not independently prove PCS soundness or authenticate unopened
rows outside the verifier's cryptographic assumptions.
