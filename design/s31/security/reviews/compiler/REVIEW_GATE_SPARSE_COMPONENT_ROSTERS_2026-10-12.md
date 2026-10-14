# Independent review: gate and sparse component rosters

Scope: commits `db4bf8cb` and `ab9ba309`, the transparent `gate` and
`sparse-gate` package paths, and their native verification paths. This review
does not cover other profiles or establish a general compiler soundness proof.

## Binding checked

- `inspect` constructs each roster from the finalized source circuit. The
  native verifier recompiles its embedded source, recomputes the fixed
  preprocessing, and compares the roster digest in its sealed key before
  accepting a proof. It also checks the source and canonical IR digests, AIR
  bundle digest, preprocessed commitment root, circuit identity hash, and
  proof statement through their existing paths.
- The full gate roster has 11 entries in the evaluator and claimed-sum order.
  Its 45 fixed columns are listed in commitment order with hashes of their
  little-endian M31 words. The sparse roster has three proof entries, mapping
  source AIR indices `1,3,10` to proof and claimed-sum indices `0,1,2`.
  This matches `serializeSparse`, `verifySparse`, and the sparse AIR binder.
- Both new native key schemas require their roster digest. A key whose digest
  is coherently resealed to altered geometry fails native source reconstruction.
  Changing the sidecar and its package file hash alone also fails the Python
  package consistency check. The focused unit suite passes all 10 tests.

## Bounded caveat

The rosters extend the **verification key**, not the legacy Fiat–Shamir proof
transcript. Their geometry comes from the pinned component facts and finalized
fixed columns; the JSON sidecar alone is not an independent source of truth.
An attacker who can author every package file and replace its verifier binary
can author a different package. Consumers must anchor the expected verifier
or key digest outside such a package.

The Python gate roster validator deliberately permits a historical
`s31-verification-key-v1` package without a roster. Its sparse counterpart
rejects the old `v3` schema. The new installed gate verifier requires the
roster-bearing schema and exact embedded key bytes; a test now checks that a
stripped legacy-style key fails `check-key`. This compatibility behavior is
safe for native proof acceptance, but package metadata validation by itself
must not be presented as proof that a package was produced by the current
compiler. The candidate release gate should pin the current compiler and key
schemas, as its scoped evidence policy already does.

## Disposition

No release-blocking proof bypass was found in these two roster slices. Include
them in the scoped candidate once their native acceptance gates and current
compiler fingerprint gate pass. Do not describe them as transcript-level
component-manifest binding or as a complete compiler correspondence theorem.
