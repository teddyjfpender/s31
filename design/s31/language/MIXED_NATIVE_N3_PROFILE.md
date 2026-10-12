# Experimental mixed native N=3 proof profile

Status: **source-pinned, proof-backed experimental profile**. The only public
proof-byte verifier entrypoint embeds S31 source and official AIR bytes at
compile time. This profile proves exactly three calls: the first two use the
pair chip/bridge AIRs, and the third uses the many chip/bridge AIRs. V3 and V4
proof bytes and transcripts remain separate.

## What the proof authenticates

The source compiler derives the three call IDs, node IDs, rounds, constants,
and eight compiled endpoint addresses per call. The verifier recompiles source
without a witness, binds the selected circuit AIR program and fixed-column
root, and rebuilds the interleaved live component schedule before decoding the
STARK proof. The selected manifest digest includes source and canonical IR
hashes, V4 circuit audit anchor, call/endpoint records, all seven component
slots, PCS parameters, exact trace column log sizes and sample widths, a hash
of mask points at a deterministic audit point, composition geometry, and the
pinned local pair/many AIR dependency closure. Core and prover code is bound by
the engine revision used to build the verifier.

| Index | AIR | Main columns | Interaction columns | Claimed sum |
| ---: | --- | ---: | ---: | ---: |
| 0 | Bound direct circuit | 12 | 8 | 0 |
| 1 | Pair chip, call 0 | 9 | 8 | 1 |
| 2 | Pair bridge, call 0 | 8 | 20 | 2 |
| 3 | Pair chip, call 1 | 9 | 8 | 3 |
| 4 | Pair bridge, call 1 | 8 | 20 | 4 |
| 5 | Many chip, call 2 | 9 | 8 | 5 |
| 6 | Many bridge, call 2 | 8 | 20 | 6 |

For the tested source, the trees have eight fixed, 63 main, and 92
interaction columns. The source determines each column's trace height; the
live handles determine its mask. One lookup challenge pair serves all seven
components. The prover and verifier use the same selected schedule for trace
columns, claimed sums, AIR handles, quotient evaluation, and PCS log sizes.

The transcript mixes, in order: a distinct mixed profile tag plus the
source/manifest digest and calls; channel salt; FRI config; fixed commitment;
mixed circuit identity; eight public words; main commitment; interaction PoW
nonce; lookup challenges; seven interleaved claimed sums; interaction
commitment; then PCS/FRI proof. The verifier checks the public lookup sum plus
all seven claimed sums is zero. Each AIR must also constrain its own claim:
the negative test changes a chip claim by `+1` and its bridge claim by `−1`,
preserving the global sum, and verification still rejects.

## Byte admission

The envelope begins with disjoint magic `S31MIX05`, call count `3`, sum count
`7`, schema bytes `01 00`, then 32-byte source digest, 32-byte selected
manifest digest, 32-byte circuit identity, an eight-byte interaction nonce,
and exactly seven canonical QM31 sums (16 bytes each). Bounded postcard STARK
bytes follow. Total proof bytes are capped at 16 MiB. The verifier checks the
header, reconstructs source and live geometry, and runs postcard shape
preflight before allocating decode memory. It rejects noncanonical limbs and
extra bytes. The wire carries exactly seven sums; the in-memory engine adapter
also rejects nonzero values in its unused backing-array slots. That adapter cannot
authenticate arbitrary caller-supplied S31 manifest digests by itself and is
not a standalone proof-byte admission API.

The focused tests prove and verify one honest source in Debug and ReleaseFast.
They pin the complete 98,363-byte proof's SHA-256 so envelope, transcript,
commitment, and PCS serialization changes require an explicit fixture update.
They reject each sum-position mutation, compensated chip/bridge sums,
reordered source calls with a resealed header, a changed compiled endpoint
with a resealed header, public-output changes, header/schema changes, trailing
bytes, and V4/V5 cross-profile replay. An [independent lookup and boundary
equation review](../security/INDEPENDENT_REVIEW_MIXED_N3_LOOKUP_2026-10-11.md)
found no concrete false-proof path in this fixed profile. It does not prove
cryptographic LogUp/PCS/FRI soundness or full compiler correspondence.
The separate mixed-schedule inspection test rejects altered relation IDs,
program bindings, PCS geometry, and local AIR dependency hashes; the engine
native test rejects changed main and interaction commitment roots.

`private` is a language visibility marker. The committed base trace contains
endpoint values without zero-knowledge masking; this profile makes no witness
confidentiality claim. A single local timing is descriptive and does not
establish a speedup or validate the whole-prover cost model.

Run the focused controls with:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-native -Doptimize=Debug -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-native -Doptimize=ReleaseFast -j1
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned.py
```

## Source-file commands

`-Ds31-lowering=direct-mixed` and `-Ds31-version=1` now build a source-embedded
prover, native verifier, and witness-free manifest inspector. The build runs
the inspector in check mode, so a valid source with any call count other than
three fails the build. See the complete command example in
[`runtime/mixed_boundary/README.md`](../../../src/frontends/s31/runtime/mixed_boundary/README.md).
The saved `s31-mixed-public-words-n3-v1` statement contains eight public
words and the source, selected manifest, and circuit identity digests. The
verifier rederives each digest from its embedded source and AIR, then checks
the proof and statement. A separately built verifier with even a whitespace
change in its embedded source rejects the earlier proof. The inspector's JSON
shows the seven interleaved slots and their claimed-sum positions, call
endpoints, AIR source hashes, column spans, relation IDs, and PCS geometry;
it does not supply verifier authority.
