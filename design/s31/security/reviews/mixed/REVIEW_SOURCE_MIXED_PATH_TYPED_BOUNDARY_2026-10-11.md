# Independent review: typed mixed source path

Reviewed the S31 mixed one-to-eight-call source-pinned profile against the
native chip and bridge AIRs in pinned `deps/stwo-zig` at `7d544c683`.
The first draft of `SourceMixedPath.lean` proved a conditional exact-event
statement but omitted public and bridge Gate terms from its premise and did
not connect circuit Gate words to chip endpoints. It could therefore not be
instantiated directly with the production claimed-sum fold. The replacement
typed `Boundary` gives the same eight bridge words to Gate events and chip
start/finish states, and places the public feeder and bridge Gate events on
the positive Gate side.

## Native event ledger

For the mixed verifier's zero claimed-sum fold, write `CY` for circuit Gate
output multiplicity events, `CU` for circuit Gate input events, `P` for eight
public output Gate events at addresses 3–10 plus the fixed `u` event at
address 2, `BG` for all eight bridge Gate endpoint reads per call, `CI` and
`CO` for chip row input and output events, and `BS` and `BF` for bridge start
and finish events. Conditional on accepted row equations, nonpole challenges,
and exact lookup reduction, the intended multiset equation is

```text
(CY ++ P ++ BG ++ CI ++ BF) ~ (CU ++ CO ++ BS)
```

The sign orientation follows `direct_mixed_general_arithmetic.zig`'s
`direct_trace.lookupSum` plus all component claims, the circuit's
input-positive/output-negative fractions, the chip's input-positive and
output-negative fractions, and the bridge's Gate-positive/start-negative/
finish-positive fractions. The Lean `jointGateSource.externalYields` is a
*joint Gate list* (`baselineYields ++ P ++ BG`), not the native circuit
component claim in isolation. The typed file proves `BG` has `8N` entries,
each bridge tuple has the native Gate coordinate layout, and its public
feeder is the same ordered tuple list as the modeled verifier fold.

## Scope and remaining obligations

`SourceMixedPath` now proves, given exact seven-word joint balance and each
chip row's local square-plus-constant equation, Gate event balance and each
call's complete indexed path. Its `Boundary` values are typed model inputs.
No theorem yet identifies them with the compiler's actual call plan, fixed
Gate addresses/multiplicities, bridge columns, public statement words, or
generated component manifest. Gate local arithmetic and producer uniqueness
are also separate premises. The native verifier authenticates a compressed
LogUp and PCS proof; deriving the exact balance and local equations from its
acceptance, with Fiat–Shamir and PCS/FRI error bounds, remains open.

The Python `source_pinned_general.py` projector checks family call metadata,
chain continuity, freshness and relation IDs for each tested count. It does
not derive absolute addresses from source topology: for its N=1 static
fixture, replacing the first input address 100 with fresh 12345 and first
output address 104 with fresh 23456 still passes that projector. The native
source-embedded verifier rebuilds the topology and does not trust a caller
manifest. This is a projector-scope limitation, not a demonstrated forged
proof path.

## Local evidence

- `lake build S31.Gadgets.Air.SourceMixedPath`: passed, 3376 jobs.
- `lake build S31.Gadgets`: passed, 3521 jobs.
- `LEAN_NUM_THREADS=1 lake env leanchecker -v S31.Gadgets.Air.SourceMixedPath`: passed.
- `python3 scripts/s31_formal.py --write`: 56 operations, 1730 inventoried
  theorems. The source-binding refresh for concurrent Python controls is
  deferred to their companion commit.
- `source_pinned_general.py --static`: passed for counts 1, 3 and 8 before
  the projector control was extended; no native proof was run for this review.
