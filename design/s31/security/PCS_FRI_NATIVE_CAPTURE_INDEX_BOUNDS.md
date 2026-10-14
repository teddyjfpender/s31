# P06: native Merkle capture index bounds

The lifted Merkle verifier receives positions as machine-word `usize` values.
It checks `position < 2^height` when `height` is below the word width, then
builds compressed paths, and finally copies one full path back to each caller
slot. Two pieces of index arithmetic matter to P06:

1. A position with high bits set must not reuse the low-bit path of a leaf in
   the declared tree.
2. A duplicate position must select the correct deduplicated path, and the
   flat path buffers must be large enough for every copied slice.

[`NativeCaptureIndexBounds.lean`](../../../formal/s31/S31/Gadgets/PcsFri/NativeCaptureIndexBounds.lean)
proves these structural facts for **every** representable index and finite
query list. `nativeRangeGuard_iff` proves that the native branch, including
its no-shift case at machine-word height, has exactly the mathematical
`position < 2^height` meaning. `nativeFinalIndex_zero` proves that a guarded
position shifted by the complete path depth becomes zero. This rules out the
arithmetic alias `q + 2^height` at the model boundary.

The Lean `dedupAdjacent` and `copyCursors` functions transcribe the native
post-sort transitions. `copyCursors_in_unique_range` proves that every
emitted cursor is below the deduplicated count, even for an empty list or
arbitrary duplicates. `gateTrace_copy_model_safe` composes that result with
flat-array slice bounds for all query lists of at most 70 positions and trace
path depths at most 21. On a machine with at least 11-bit words, all path
**element** offsets fit. With 32-byte digests, `gateTrace_bytes_lt_word`
proves at most `70 × 21 × 32 = 47,040` bytes, below `2^16`, so the selected
trace capture also fits byte-address arithmetic on 32- and 64-bit targets.

For a hand calculation, the caller submits positions `[7, 1, 7, 3]`. The
native sort orders the original slots as `[1, 3, 0, 2]`, with positions
`[1, 3, 7, 7]`. Adjacent deduplication gives `[1, 3, 7]`; the source-shaped
copy cursor is `[0, 1, 2, 2]`. At path depth 3, the three unique paths occupy
9 hash elements. The four caller paths occupy 12. Source cursor 2 reads
elements `[6, 9)` for both original slots 0 and 2; each destination gets its
own 3-element slice. The theorem covers any finite position list, not just
this example.

The [source guard](../../../scripts/s31_formal_lib/pcs_fri_capture.py) pins
the native range check, adjacent deduplication, path allocations and copy
offsets. It also pins the selected raw Gate verifier's `70`-query constructor,
raw-query capture route, configured lifting-height formula and S31 capture
admission. Mutation tests reject changes to these stages. The height bound
`21` is conditional on the reviewed local Gate key having trace log size
`20` and blowup log `1`; the [Gate geometry audit](PCS_FRI_GATE_FINAL_DOMAIN.md)
checks that selected key. A different key needs its own bound check.

These are all-input **Lean arithmetic and list theorems** plus source-bound
checks, not a proof that arbitrary Zig execution implements the Lean model.
The native sort, row assembly, hashing, compressed decoder and binary-to-Lean
join remain open. BLAKE2s collision resistance and the full BCS/ROM budget
also remain open. P06 stays open; native proven security bits remain null and
the v0.1 release gate remains closed.

Focused commands:

```sh
cd formal/s31 && lake build S31.Gadgets.PcsFri.NativeCaptureIndexBounds
python3 -B -m unittest scripts.tests.test_pcs_fri_capture -q
python3 -B scripts/s31_formal.py
python3 -B scripts/release/pcs_fri_v01_blockers.py --check
```
