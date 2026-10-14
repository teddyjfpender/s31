# P05: ordinary Gate cannot reach a smaller maximum domain by choosing a small program

**Finding:** the currently accepted ordinary `gate` AIR has a fixed
`VerifyBitwiseXor_12` table with trace log size **20**. A small source program
can reduce its variable arithmetic component, but the sealed key's maximum
trace size remains `N=2^20`. Moving the conditional paper batching cap to
`N<=2^17` therefore requires a **new authenticated AIR/key profile** and a
fresh source-bound roster. It is not a FRI parameter change on the current
Gate proof. The published theorem ensemble width `M` for that proof is still
unmapped; no native security bits follow from this observation.

## Accepted small-program control

I built the checked-in
[`arith4.s31.json`](../../../src/frontends/s31/examples/arithmetic/arith4.s31.json)
with the pinned engine gitlink `59e1f115250b8af01712b9bf3d71616e53094964`,
ordinary `--lowering gate`, legacy channel and FRI fold step 1. Its variable
`qm31_ops` component needed log size **10**, while the fixed
`verify_bitwise_xor_12` component stayed at log size **20**. The generated
native verifier accepted the sealed key, and accepted the proof produced from
[`arith4.valid.json`](../../../src/frontends/s31/examples/arithmetic/arith4.valid.json)
against the checked-in public statement. The proof was 434,740 bytes. Local
artifact SHA-256 values make the observation reviewable:

| Artifact | SHA-256 |
| --- | --- |
| source | `427f523329a26901a8abe7125def9ce185c96d1358db71c59024c623bb1e2441` |
| assignment | `e47451b752b9ce35fc1fdd5e553089efd8a42aa9bc9b47828df93616623d23fe` |
| package manifest | `af11cea26ea74ea6b9e6ca1c525d451557f3520800537700728be6b3f900626a` |
| verification key | `a9eae613102674983a1e281544348354c33ab8f1d81f1990412380405fb30bbe` |
| proof | `1e93eb2211809bd51dab98dba2a9ab62c25a560b030d7a0071ed3cb578eaf084` |

The [full source-bound diagnostic report](evidence/gate-small-program-paper-batch-boundary-2026-10-14.json)
records the package/key/AIR/source hashes, four commitment-tree widths
`[45,114,152,8]`, the seven occupied heights, and a native FRI input domain
of `2^21` rows. It keeps the paper ensemble `M` null and release admission
false. Its conditional `N=2^20`, `B=2`, `T=2^64` calculation again yields the
isolated cap `M<=64`. Even this small program retains the 193-column
source-log-4 bucket. The reported source heights differ from the earlier
larger example at one variable component (log 10 here versus log 9 there);
the fixed log-20 floor and 193-column bucket remain the same.

## Source reason and engineering consequence

The pinned engine's
[`component_list.zig`](../../../deps/stwo-zig/src/frontends/circuit/common/component_list.zig)
assigns `.log_size = .{ .fixed = 20 }` to `verify_bitwise_xor_12`. The S31
[`gate_component_roster.py`](../../../src/frontends/s31/python/package/gate_component_roster.py)
duplicates that reviewed fact in `FIXED_LOGS[6] = 20` and rejects a sealed
Gate roster with another height. The native verifier reconstructs that
component roster from the source/key instead of trusting an arbitrary
package field. Thus the ordinary Gate profile includes the table even when
the program uses no Blake-G gate; the sample's Blake-G dynamic trace has log
size 4 while the fixed table remains at log 20.

To lower `N`, design and authenticate a different component set or smaller
fixed table, then regenerate the AIR bundle, preprocessed columns/root,
verification key schema, component manifest and source roster, native
verifier, OOD claim roster, four-root challenge schedule and PCS/FRI theorem
mapping for that new profile. A selective component design would also need
to prove the omitted lookup relations are unused for every admitted program.
The smaller `N` arithmetic is useful only **after** a new accepted proof and
source-bound diagnostic confirm the new key. No current release selector is
changed by this result.

Reproduce the local control from an isolated S31 checkout:

```sh
python3 src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/arithmetic/arith4.s31.json \
  --lowering gate --out /tmp/s31-gate-small-control
/tmp/s31-gate-small-control/bin/s31-arith4-native-verifier \
  check-key /tmp/s31-gate-small-control/verification-key.json
/tmp/s31-gate-small-control/bin/s31-arith4-prover prove \
  src/frontends/s31/examples/arithmetic/arith4.valid.json \
  /tmp/s31-gate-small-proof.json
/tmp/s31-gate-small-control/bin/s31-arith4-native-verifier \
  /tmp/s31-gate-small-proof.json \
  src/frontends/s31/examples/arithmetic/arith4.statement.json \
  /tmp/s31-gate-small-control/verification-key.json
python3 -B scripts/release/pcs_fri_gate_paper_batch_boundary.py \
  /tmp/s31-gate-small-control
```

This is a locally trusted accepted proof and source-geometry control. It is
not compiler correctness, a degree-corrected Gate proof, or a native P05
soundness certificate.
