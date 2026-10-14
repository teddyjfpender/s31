# Sparse Gate P05 paired geometry from an accepted proof

This is a candidate route around ordinary Gate's fixed `2^20` trace floor. A
real `arith4` sparse Gate package has a sealed `sparse-v3` key and an accepted
native proof at maximum trace domain `N=2^16`. The existing production proof
still uses legacy accumulated-quotient FRI. The geometry below describes the
separate original and own-quotient tracks a *future* paired protocol would
need. No such paired sparse Gate proof is selected or admitted by this result.

## Reproduce the source-bound capture

From the S31 repository root:

```sh
python3 src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/arithmetic/arith4.s31.json \
  --lowering sparse-gate --out /tmp/s31-p05-sparse-package
/tmp/s31-p05-sparse-package/bin/s31-arith4-native-verifier \
  check-key /tmp/s31-p05-sparse-package/verification-key.json
/tmp/s31-p05-sparse-package/bin/s31-arith4-prover prove \
  src/frontends/s31/examples/arithmetic/arith4.valid.json \
  /tmp/s31-p05-sparse-proof.bin
/tmp/s31-p05-sparse-package/bin/s31-arith4-native-verifier \
  /tmp/s31-p05-sparse-proof.bin \
  src/frontends/s31/examples/arithmetic/arith4.statement.json \
  /tmp/s31-p05-sparse-package/verification-key.json
python3 -B scripts/release/pcs_fri_sparse_p05_accepted_geometry.py \
  /tmp/s31-p05-sparse-package /tmp/s31-p05-sparse-proof.bin \
  src/frontends/s31/examples/arithmetic/arith4.statement.json
```

The release script verifies all package artifact digests, calls native
`check-key`, and then invokes opt-in `inspect-p05`. That verifier command runs
the *same* sealed-key, public statement, native STARK, Merkle, FRI, and capture
admission checks as ordinary verification. It reads the capture only after
those checks succeed. An invalid key fails before geometry is emitted. Run
`formal/s31/tests/run_pcs_fri_p05_sparse_accepted_geometry.sh` for the honest
proof and wrong-key control. It uses a temporary package and proof.

## Source-bound roster and OOD schedule

Root order is fixed, main, interaction, composition. The accepted capture has
root column counts `[12, 17, 24, 8]` and OOD sample counts `[12, 17, 36, 8]`.
Its composition log-degree bound is `17` with split `1`, yielding eight
composition columns at extended log height `17`. The FRI blowup log is `1`, so
each committed input log is one less than the capture's extended log.

| Extended log | Input log | Source columns | OOD claims | Fixed claims | Main claims | Interaction claims | Composition claims | Future separate track width if one original plus one quotient per claim |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 17 | 16 | 14 | 18 | 1 | 1 | 8 | 8 | 32 |
| 11 | 10 | 28 | 32 | 8 | 12 | 12 | 0 | 60 |
| 5 | 4 | 19 | 23 | 3 | 4 | 16 | 0 | 42 |
| Total | | 61 | 73 | 12 | 17 | 36 | 8 | 134 |

The 61 originals split as 53 fixed/main/interaction source columns and eight
composition columns. Some interaction columns have two OOD samples, explaining
the 73 claims. The inspector emits every source root/column index, its height,
claim count, and proposed within-height original/quotient slot. These slots
describe a deterministic candidate for a paired original-plus-own-quotient
ensemble; the current verifier does **not** commit or independently degree-test
those 134 tracks. The four source roots occur at different challenge epochs,
so their columns cannot be silently flattened under one pre-OOD root.
The report records each column's ordered OOD sample count, but does not
serialize the QM31 point coordinates. The existing `p05_claim_roster.derive`
recomputes the verifier-owned points from accepted AIR objects; joining it to
this sparse capture is still required for a full paired OOD wire.

## Paper feasibility boundary

The sealed key uses `N=2^16`, blowup `B=2`, 70 legacy raw FRI queries, and
`2^26` FRI PoW. For the selected target `epsilon(T)/T <= 2^-96` at `T=2^64`,
the isolated necessary S-two batching factor

`((T+1)/T) * (M-1) * (N*B^2) / |QM31|`

allows integer `M <= 1024` under the *conditional* substitution `D0=N*B^2`
and minimum BCS round count `R=1`. Here the published common batch width is
`M=max_i M_i` after per-domain zero padding. Native source columns and the
candidate widths `32/60/42` are **not** a proved mapping to those `M_i`; a
multi-height embedding, weighted batch definition, additional claims, or
protocol transformation may change them. The full theorem has further
positive terms. `M`, proven security bits, and release admission remain null.

The production sparse Gate accepted proof was 226,475 bytes. One local
ReleaseFast run reported 0.036049 s proving and 0.048885 s through local
verification, versus an ordinary Gate proof of 434,740 bytes and 0.545 s in a
different one-off run. These measurements compare different proof profiles
with different unresolved soundness premises. They demonstrate geometric and
performance potential, not a soundness-equivalent speedup.

The remaining critical path is a selected four-epoch native protocol that
independently tests all original and own-quotient oracles; an exact mapping of
the accepted sparse roster and OOD masks to the published multi-domain batch
ensemble and `D0`; and the full AIR/FRI/BCS/collision/PoW work-factor
composition. A line-tree commitment/profile and statement descriptor binding
also need selection. The current production verifier remains on its legacy
proof format.
