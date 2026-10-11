# Sealed packages

`context.py` owns repository paths, source hashes, the compiler fingerprint,
source lowering and public ABI metadata. The fingerprint includes the CLI,
every Python implementation file in this directory, the language, library and
inspection modules, the Zig sources, pinned AIR assets, the pinned engine
commit and the Zig version.

`build.py` compiles a JSON relation or `.s31` source into a staging directory.
It checks the compiler and source identities before atomically installing a
package. A text package also contains the original source, its normalized
relation, source map, typed interface and standard-library lock.

`verify.py` checks the manifest, artifact hashes, source-to-relation lowering,
library lock, verification keys, AIR identifiers and profile-specific recursive
keys before package data is used by the CLI. This is **package integrity**, not
a proof check: the installed native verifier checks a proof and public claim.

`trust.py` checks externally supplied SHA-256 pins for the normalized source,
key, prover and verifier before full package validation; a text package also requires
the exact `.s31` source pin. The `verify-pinned` CLI command uses this admission
on a private package snapshot immediately before native verification. Pins
obtained from the package itself provide no authentication. A trusted release
channel must supply them; the verifier executes from the checked snapshot.

`inspect-record-proof` also executes from a private copy of the package,
proof, and statement. Its `unpinned_snapshot` check establishes internal
package consistency and prevents caller path changes during inspection from
changing the displayed record claim. The readback also rejects changes to its
copied source, key, verifier, proof, or statement while the verifier runs. It does not establish an externally
trusted source or verifier identity. `inspect-record-proof-pinned` uses the
same readback with `admitted_snapshot` and the exact `verify-pinned` digest
contract, so externally trusted pins gate both verification and display in
one command.

`correspondence.py` independently reparses the exact source bytes for a bounded
public four-lane add/multiply/static-let fragment. For direct-gate text packages
in that grammar, build attaches `correspondence-certificate.json` and verification
requires it. The checker compares the complete normalized relation, canonical
SSA, public ABI, native source-map gate schedule, value-free gate topology,
all eight emitted selector/address column hashes, the exact input/source/ABI
gate allocation and base-256 constant and padding schedule, fixed QM31 basis
derivation,
AIR asset hashes and key core.
The certificate still marks native Gate lookup and AIR/PCS soundness as assumptions.
It is a **package-admission** certificate: the standalone native verifier does
not read it. See the [design brief](../../../../../design/s31/language/DIRECT_GATE_CORRESPONDENCE_CERTIFICATE.md).

The public Python API remains in `../s31.py`; its functions import these
modules. The dependency direction is `context -> verify -> build -> CLI`.
