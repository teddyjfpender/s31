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

When both are supplied and accepted, the report now includes
`accepted_proof_gate_geometry`. This joins that particular proof and public
statement to the source-derived **native** FRI input domain using their
SHA-256 digests, the key and package digests, the pinned engine commit, and
the rebuilt verifier image digest. For the reviewed `affine_guard` geometry,
the native FRI domain is `2²¹` rows; the conditional S-two Protocol 4
original-plus-quotient domain would be `N B² = 2²²` rows. The report keeps
both values separate. Without an accepted proof, the joined field is null.
The [2026-10-14 local result](evidence/gate-native-fridomain-accepted-proof-2026-10-14.json)
uses the checked-in `arith4_m31.s31` source and its valid assignment. The
normal trial accepted a 438,157-byte proof and rejected a changed public
statement. The separate rebuild used four Zig jobs, matched the packaged
verifier's execution image after the documented Mach-O normalization, and
accepted that proof with the rebuilt verifier. The report binds the accepted
proof, statement, key, package manifest, engine gitlink, and rebuilt image by
digest. Its native FRI domain is `2²¹`; the candidate paper Protocol 4
`NB²` domain is `2²²`. The generated package and proof remain local; the
checked-in report records one observation, not an independently reproducible
proof transcript or a published-theorem reduction. The focused unit test
uses a mocked verifier to test the join's rejection conditions. P01 still
needs a native-to-paper oracle and degree mapping for every released program.

Equivalent reproduction commands are below. The local trial used a temporary
`zig` PATH wrapper that appended `-j4` to its build invocation to respect the
machine's concurrency limit; the second command has its own `--jobs 4` cap.

```sh
python3 -B src/frontends/s31/python/s31.py trial \
  src/frontends/s31/examples/arithmetic/arith4_m31.s31 \
  src/frontends/s31/examples/arithmetic/arith4.valid.json \
  --lowering gate --out /tmp/s31-gate-accepted-geometry-live
python3 -B scripts/release/pcs_fri_gate_binary_rebuild.py \
  /tmp/s31-gate-accepted-geometry-live/package --jobs 4 \
  --proof /tmp/s31-gate-accepted-geometry-live/proof.bin \
  --statement /tmp/s31-gate-accepted-geometry-live/statement.json
```

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
