# Mixed proof full-trace sidecar audit

`general_package.verifyEmbeddedWithTraceAudit` is an **opt-in** check for a
caller who already has the complete private assignment. It accepts the same
embedded S31 source, embedded AIR bundle, eight public words, and serialized
proof as `verifyEmbedded`, plus the assignment. The ordinary verifier and proof
format are unchanged.

The audit first admits the proof through the normal source-derived verifier.
It then recompiles the assignment and recomputes all three witness-bearing
commitments with the same PCS code. The fixed, main, and interaction roots must
equal the corresponding roots in the verified proof. The public words,
source-derived call plan, and individual claimed sums must also match. A root
equality binds the supplied sidecar to those commitments under the Merkle hash
binding assumption. It does **not** mean a succinct proof reveals every trace
cell, nor does it independently prove Stwo's PCS/FRI soundness.

The full-trace checks run before returning the audit result:

| Component | Checks |
| --- | --- |
| Circuit fixed/main | Every Qm31 operation row, including padding and zero-multiplicity yields: four opcode selectors, source addresses, multiplicity, twelve main limbs, and the entire field operation. The reserved `0`, `1`, and `u` values and all eight public words are checked. |
| Gate relation | A signed bag of actual row uses/yields balances the source-owned public feeder (`u` plus eight outputs) and every bridge endpoint occurrence. The key is `(address, value)` after the row/bridge checks have tied each occurrence to that source address's value. Global list order is irrelevant. |
| Chip | Every tagged call step follows `out = in² + c` in the bit-reversed storage row, and each `out` event cancels the next row's `in` event for that call. |
| Bridge | All eight endpoint columns match the compiled circuit words on **all 16 rows**. Each row's Gate and tagged endpoint fractions use `1/16`; the bridge cancels the chip's first and last tagged events. |
| Interaction | Every LogUp fraction is recomputed from the checked main and fixed row. The audit checks the per-row fraction prefixes, the final column's previous-row mapping in bit-reversed circle order, the `claimed_sum / row_count` shift, the exact claimed sum, and every denominator for a pole. |

The source-pinned general profile currently rejects a permutation-bearing
source in this audit path because its base-row projection has not been added.
The normal proof path may support more shapes. This API is intentionally
expensive, requires disclosure of the private assignment to the auditor, and
does not replace independent compiler correspondence or formal PCS proofs.

Focused checks from the S31 repository root:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-trace-audit -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-circuit-mutations -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-trace-mutations -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-equal-public-sidecar -j1
```

The first test proves and audits source-pinned `N=1` and `N=8` programs, then
rejects a changed private assignment and claimed sum. The neighboring
[`trace_correspondence.zig`](../../tests/proofs/mixed_boundary/trace_correspondence.zig)
fixture changes a decoded proof's main Merkle root, reserializes it, and checks
native verification rejects it. The two mutation tests reject changed
reserved `u`, Gate/main/fixed cells, a bit-reversed chip row, a non-first bridge
row, chip/bridge interaction cells, a non-first chip column's log size, and a
denominator pole. Circuit mutations also change arithmetic on a
zero-multiplicity padding Gate row and change a constrained private selector
from an honest bit to `2` while leaving the eight public words equal; both
fail at `InvalidMixedTraceAuditGate`. These are precommitment row mutations,
not forged accepted proofs. The last test holds all eight public words fixed while
switching a private selector whose two branches happen to compute the same
result; the verifier accepts the proof, but the sidecar audit rejects the
different circuit trace specifically at the main commitment root.
