# Rebuild the sealed Gate verifier before running it

The [rebuild diagnostic](../../../scripts/release/pcs_fri_gate_binary_rebuild.py)
narrows the package executable provenance gap for the legacy fold-step-1
Gate profile. It makes a bounded private copy of the package and checks its
internal artifact hashes **without executing the packaged verifier**. It
requires the package's compiler fingerprint and Zig version to equal the
trusted checkout, then rebuilds the verifier using the copied normalized
source, verification key, recursive keys, fixed-fold key, and standard-library
lock. It compares the executable files before `check-key`: exact SHA-256
identity passes directly. On macOS it otherwise requires valid code signatures
and compares all bytes after normalizing only the linker UUID, one Zig object
timestamp and cache key, and ad hoc signature. Code, constants, load commands,
dynamic-linking data, and indirect symbols remain under comparison. A supplied
proof and statement are checked with the freshly built verifier.

```sh
python3 -B scripts/release/pcs_fri_gate_binary_rebuild.py /path/to/package \
  --proof /path/to/proof --statement /path/to/statement.json
python3 -B scripts/release/pcs_fri_gate_binary_rebuild.py /path/to/package \
  --require-proven
```

The build uses at most 70% of the host's reported logical CPU count and caps
Zig jobs at twelve; the default is eight. The report is **conditional build
reproducibility**, not an authenticated release signature. A trusted checkout,
Zig binary, dependency tree, build system, macOS code-signing validation, and
the narrow Mach-O comparison are still assumptions. Matching executable images
do not prove that their compiled
instructions implement the intended Zig semantics, that the compiler emits
the intended AIR, or that accepted PCS/FRI proofs are sound. The diagnostic
keeps `native_proven_security_bits` null and `proven_release_admissible` false;
`--require-proven` exits 2 after a successful diagnostic.

This check is intentionally separate from package creation and verifier
execution. It is useful for reviewing one exact executable and proof without
silently treating a package's self-authored manifest hash as a trust root.
