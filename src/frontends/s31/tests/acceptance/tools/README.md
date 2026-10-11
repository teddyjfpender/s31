# Canonical IR audit tools

`canonical_ir_digest.zig` is a tiny native oracle used by
`../acceptance_canonical_ir_fidelity.py`. The acceptance check compares the
independent Python reconstruction of compact canonical IR with Zig's actual
`relation.parseProgram` and `canonical.build` digest across seven handpicked
fixtures and 512 generated bounded programs. Each generated program is checked
in both direct and zero-cost-alias spellings. It runs without building a proof
package:

```sh
python3 src/frontends/s31/tests/acceptance/acceptance_canonical_ir_fidelity.py
```

`export_package_canonical_ir.py` exports the exact compact IR bytes from a
previously built bounded direct-gate text package. It snapshots and verifies
the package, checks its independent correspondence certificate, and compares
the reconstructed IR digest with the manifest, verification key, cost report,
and component manifest:

```sh
python3 src/frontends/s31/tests/acceptance/tools/export_package_canonical_ir.py \
  /path/to/package --output /path/to/canonical-ir.json
```

For an additional byte-level check by the executable Lean model:

```sh
cd formal/s31 && lake build s31-alias-relation-check && cd ../..
python3 src/frontends/s31/tests/acceptance/tools/export_package_canonical_ir.py \
  /path/to/package --output /path/to/canonical-ir.json --lean-check
```

The output path must be new and outside the package. The optional Lean audit
checks the source, normalized relation, and reconstructed canonical IR bytes
against its bounded alias grammar. Package consistency does not authenticate
who produced the package; neither utility verifies proof bytes or establishes
PCS/FRI soundness.
