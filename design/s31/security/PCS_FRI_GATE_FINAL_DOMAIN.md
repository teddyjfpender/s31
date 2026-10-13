# P01: sealed gate composition bound and final FRI domain

The diagnostic below handles only a sealed `gate` leaf package with the
`circuit-v1` verification-key schema. It does not modify package artifacts,
but it executes the package's own native verifier for `check-key`. Run it only
with a locally trusted package binary. It extends the general package
geometry report and leaves the P01 release gate closed.

```sh
python3 -B scripts/release/pcs_fri_gate_final_domain.py /path/to/sealed-gate-package
python3 -B scripts/release/pcs_fri_gate_final_domain.py /path/to/sealed-gate-package --require-complete
```

The second command exits 2 even for an accepted key. The tool verifies the
package hashes and roster, requires its installed native verifier's
`check-key` acceptance, requires the checked-out engine to equal the S31
gitlink, checks the relevant native source shapes, and matches the key's AIR
digest against the actual bundled bytes and the engine constant. It reads
only the bundle envelope and component geometry; the native AIR parser checks
the full program. The report includes source hashes so a source change is
visible. The package manifest's hashes check internal artifact consistency;
the manifest is not an external trust anchor. Neither those hashes nor a
source guard authenticates the installed executable's provenance or proves it
was compiled from the checked-out source.

## Conditional derivation

For each of the 11 bound gate components, let `t_i` be its sealed roster trace
log and `delta_i` the official AIR bundle's `evaluation_log_size -
trace_log_size`. The CPU binding path sets its evaluation log to `t_i +
delta_i`. The runtime component reports that value as its constraint log
degree bound. The verifier takes their maximum, then the default one-level
composition split:

```text
U = max_i(t_i + delta_i)                 unsplit composition log bound
S = U - 1                               split composition column log bound
M = max(S, key.trace_log_size)           committed composition column log
H = key.trace_log_size + blowup_log      configured lifted tree height
```

The diagnostic requires `M + blowup_log <= H`; otherwise the native
`treeHeight` check would reject that composition commitment. In the pinned
`proving_5a7c5ed` revision, `PcsConfigV2.fromFriAndTraceSize` configures each
tree to height `H`. The PCS verifier constructs the composition tree at that
height and passes the *last tree's height* to `FriVerifier.commit` as a degree
bound of `H - blowup_log`. `FriVerifier.commit` constructs its first circle
domain at log size `(H - blowup_log) + blowup_log = H`. Thus, conditional on
successful execution of this exact verifier path, the FRI input-domain size is
`D = 2^H`. This is the actual CPU gate path; `PcsConfigV2.finalLiftingLogSize`
is a helper and is not used to construct this verifier's FRI input domain.

For the local sealed `affine_guard` package used in the diagnostic, all
11 official bundle offsets are 1, the maximum roster trace log is 20, and
the FRI blowup log is 1. Hence `U=21`, `S=M=20`, `H=21`, and the conditional
domain size is `D=2^21=2,097,152` rows. These numbers belong to that sealed
package, not to every possible gate package.

## Preconditions and limits

The source-to-domain argument requires: (1) the key, roster and official AIR
bundle are those accepted by the installed gate verifier; (2) the installed
binary executes the pinned source and the `Blake2sM31MerkleChannel` revision;
(3) its AIR binding, component vtable, composition commitment and PCS/FRI
calls execute as the guarded source indicates; and (4) verification reaches
success. The diagnostic checks data consistency and source syntax, but it does
not machine-prove Zig control-flow semantics or compiled-binary provenance.
There is no inference from `check-key` acceptance to proof acceptance.

The derived `D` and split bound are a narrow P01 input. The diagnostic does
not identify the published theorem's `C`, `d`, `L`, `m`, rate or list bound;
does not discharge finite-domain or small-table assumptions; and does not
prove constraint degree adequacy, authenticated-oracle equality, IOP
proximity soundness, or Fiat–Shamir reduction for the native verifier.
`status=incomplete` and `proven_release_admissible=false` remain mandatory.
Other lowerings are rejected by this diagnostic and retain their prior P01
geometry gaps.

Focused tests create a bundle envelope, mutate its header/body, mutate the
sealed component order and degree offset, reject a missing native key check,
and compare the real pinned bundle offsets and source guards when the engine
submodule is checked out:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_gate_final_domain -v
```
