# P01 package geometry extractor

Run the read-only diagnostic on a sealed **leaf** package with the engine
submodule checked out at the S31 gitlink:

```sh
python3 -B scripts/release/pcs_fri_package_geometry.py /path/to/package
python3 -B scripts/release/pcs_fri_package_geometry.py /path/to/package --require-complete
```

The second command exits 2 while any P01 theorem input remains open. Package
verification first checks the manifest's artifact hashes, source and key
agreement, supported profile, and component roster or manifest when present.
The extractor checks the installed native verifier's `check-key` command when
available and records whether that command accepted. SHA package verifiers do
not expose a standalone key check. A verifier from an older package may also
lack it; the report records that limit instead of claiming native custody.
The diagnostic checks the current S31 and engine source shapes that select the
FRI tuple and configure lifting, then records their hashes and gitlink. These
source checks are not a proof that an installed binary was compiled from those
exact files.

`candidate_N_trace_rows` is `2^key.trace_log_size`. It is a candidate maximum
trace size, not an identified parameter of Circle STARKs Theorem 7.
`configured_trace_lifting_rows` is `2^(key.trace_log_size + log_blowup_factor)`
from `PcsConfigV2.fromFriAndTraceSize`. The configured per-component extended
rows use the same blowup. The final FRI input domain `D` remains null: native
`finalLiftingLogSize` also takes the maximum with the composition degree
bound, which the verification key does not publish. No paper rate or proximity
claim is calculated from these values.

The current gate and sparse-gate keys bind separate component rosters; direct
keys embed a component manifest. The diagnostic reports each reviewed roster
entry's trace height and configured extended height, plus the bound
preprocessed-column heights. Chip, sparse-chip and sparse-wide-gate keys have
no complete component-domain or preprocessed-column roster. SHA keys give
only four circuit logs, without a full named component-to-domain map. For
these profiles `component_roster_complete` is false and the missing geometry
is explicit. Legacy schemas and unexpected FRI tuples fail closed.

Even when a roster is complete, the package does not supply the complete
published theorem inputs: the split composition log-degree bound, per-component
constraint degrees, `C`, `d`, `L`, `m`, rate, list bound, finite-domain and
small-table preconditions, and a verified-oracle/IOP correspondence. They stay
null or listed as missing, `status` stays `incomplete`, and
`proven_release_admissible` stays false. This report cannot discharge P01 or
produce native soundness bits.

Generated-key tests cover all four extractor layouts and hostile tuple,
schema, height, order, and evaluation-domain changes:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_package_geometry -v
```

A local read-only run on a sealed gate package reported `N=2^20`, configured
lifting `2^21`, 11 component heights, and 45 preprocessed-column heights; its
native `check-key` accepted.
A sealed SHA joint package reported `N=2^18`, configured lifting `2^19`,
four unnamed circuit logs, and no standalone native key check. These are
observed package diagnostics, not frozen release-profile constants.
