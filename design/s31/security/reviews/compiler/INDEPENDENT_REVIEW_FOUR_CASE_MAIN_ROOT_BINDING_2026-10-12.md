# Independent four-case public main-root review — 2026-10-12

**Reviewed revision:** shared `4c82f97` (isolated implementation `8a33923`), limited to the [four-case acceptance checker](../../../../../src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py) and its [README](../../../../../src/frontends/s31/tests/acceptance/compiler_correspondence/README.md). Verdict: **no concrete blocker found for the stated honest, public-only diagnostic**. The check does not establish a general source-to-proof or arbitrary-opening theorem.

## Binding and parser

For each of sources 00, 07, 14 and 15 (fixture suffixes `case00`, `case07`, `case14`, `case16`), `native_case` builds one source-pinned package and invokes both inspection commands with the **same assigned path**. `native_proof_binding` invokes `s31.trial` on that package and assignment. In [`runtime/trials.py`](../../../../../src/frontends/s31/python/runtime/trials.py), the trial invokes the generated native verifier on its staged proof, copies those exact proof bytes, and records their length and SHA-256. The new checker verifies those bytes against the trial report **before** `proof_roots` interprets the bounded direct-Gate postcard header. It checks the first root against the sealed verification key and the second against the separate `inspect-physical-root` result. That result must report the same normalized program hash and public words as the row export; its main-word SHA-256 must match the canonical 12-column × 512-row, column-major little-endian `u32` serialization of the fresh `inspect-physical-rows` export. The ordinary `--native` mode also hashes the checked-in fixture's words and requires the entire fresh JSON export to match the fixture byte-for-byte.

The helper's root parser assumes the pinned `S31NAT7G` profile, five PCS parameters `(26,1,70,0,1)`, absent lift, and four commitments. It only reads the first two roots. Its placement after generated verifier acceptance and the exact proof-byte check makes it suitable for this pinned regression check; it should not be described as a general proof parser. Both inspection commands are required to reject nonempty private assignments and a real private-input source without emitting fixed/main column or root JSON keys. Fixture refreshes are queued until all cases and private-source controls pass. A deliberate `--write` can still replace fixtures, so a reviewed fixture diff remains part of the release process.

## Evidence

In the implementation worktree, `python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --plan-only`, the default static checker, and `git diff --check` all exited 0 in my review. The implementation agent's exact fresh-native command was:

```sh
set -o pipefail
/usr/bin/time -p python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --native --work zig-out/s31/formal/v18-roster-main-root 2>&1 | tee zig-out/s31/formal/v18-roster-main-root.log
```

It exited 0 in **297.51 s**. The retained log and proof/package/assignment artifacts are under `zig-out/s31/formal/` in the isolated `s31-roster-root-v18` worktree. All four honest native verifiers accepted; the exact ABI-valid changed public result was rejected at `InvalidInteractionNonce` for each pinned run. Each case retained 512 physical rows, 6,144 main cells, and eight rejected checker mutations. Both inspection commands rejected the nonempty private assignments and the real private-input source. No fixtures changed.

I independently decoded the first two roots from each retained proof's pinned header, hashed the complete proof bytes, read each sealed key and trial report, and hashed all 6,144 M31 words from each checked-in fixture using `struct.pack('<I', value)` in column order. These matched the native log and key in all four cases:

| Source | Proof bytes | Main-root prefix | Main-word SHA-256 prefix |
| --- | ---: | --- | --- |
| `00:direct` | 52,027 | `0d7aa4ba0861` | `c19341cbb63f` |
| `07:aliases` | 55,911 | `276f6cd0f93c` | `41f25932d85e` |
| `14:direct` | 53,421 | `ce2338e60f48` | `2d0766abcd47` |
| `15:comments` | 52,286 | `dd57d9ed13b0` | `b6c206f1650f` |

The independent saved-artifact check is **not** a second native proof verification. The fresh-native run above performed the verifier and rejection controls. The [single-source main-root test](../../../../../src/frontends/s31/tests/acceptance/compiler_correspondence/public_main_root_binding.py) separately mutates one row value and one proof main-root byte; this four-case extension adds cross-case equality checks, not a new root-mutation control.

## Remaining obligations

`inspect-physical-rows` and `inspect-physical-root` both depend on the native `writeBase` path. Their digest/root equality, under SHA-256 collision resistance and the backend's commitment implementation, links the exported public rows to the main commitment of these **honestly generated, accepted** proofs. It does not authenticate arbitrary prover-supplied openings as evaluations of those rows, establish PCS/FRI/LogUp soundness, or extend the private/mixed boundary. The compiler's source-to-physical semantics and the verifier-to-trace correspondence remain separate obligations.
