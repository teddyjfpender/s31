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
package, not to every possible gate package. The same official bundle reports
57 native constraints across those 11 components. That count is a concrete
AIR-program inventory, not a theorem `k_t` substitution.

The published Protocol 4 starts its **full degree-corrected ensemble** at
`D₀=N B²`. If the gate key's maximum trace rows instantiate the paper's `N`,
then this example has candidate `D₀=2²²`, while its native quotient-only FRI
starts at `D=2²¹`. The diagnostic reports both sizes and their inequality;
it rejects a key whose candidate `N B²` exceeds the paper's `2³⁰` circle
domain cap, even when native `N B` fits. This is a necessary parameter check
under the candidate `N` identification. It neither identifies the native
quotient-only oracle with the paper ensemble nor establishes that all paper
domain and degree premises hold.

For the paper's unique-decoding interval `0<θ<(1−1/B)/2`, every candidate
table satisfies its small-table OOD inequality if its row count `N_t` obeys
`(B−1)N_t≥4`. The report checks this using the smallest gate component;
the reviewed Gate has `B=2` and every component has at least 16 rows, so
the numeric implication holds for every θ in that interval. Identifying
each native component with a paper table is still an open premise.

## Preconditions and limits

The source-to-domain argument requires: (1) the key, roster and official AIR
bundle are those accepted by the installed gate verifier; (2) the installed
binary executes the pinned source and the `Blake2sM31MerkleChannel` revision;
(3) its AIR binding, component vtable, composition commitment and PCS/FRI
calls execute as the guarded source indicates; and (4) verification reaches
success. The diagnostic checks data consistency and source syntax, but it does
not machine-prove Zig control-flow semantics or compiled-binary provenance.
There is no inference from `check-key` acceptance to proof acceptance.
The [verifier rebuild diagnostic](PCS_FRI_GATE_BINARY_REBUILD.md) can now join
this exact conditional native domain to a particular proof that the rebuilt
verifier accepts. It reports the paper's larger candidate `NB²` domain
separately and still does not identify the published oracle relation.

The derived `D` and split bound are a narrow P01 input. The diagnostic does
not identify the published theorem's `C`, `d`, `L`, `m`, rate or list bound;
does not discharge the remaining finite-domain or small-table assumptions;
and does not prove constraint degree adequacy, authenticated-oracle equality, IOP
proximity soundness, or Fiat–Shamir reduction for the native verifier.
`status=incomplete` and `proven_release_admissible=false` remain mandatory.
Other lowerings are rejected by this diagnostic and retain their prior P01
geometry gaps.

The report also lists each bound component's `native_constraint_count` and
`native_program_parts` from the official AIR bundle envelope, and their total.
The native bundle parser checks that each program's own constraint count sums
to the recorded component count; this diagnostic checks the envelope count,
component order, and total independently. These counts describe the installed
AIR program. They are **not yet identified with** the paper's `k_t`: that
requires proving the native AIR component and interaction relation match the
paper's table relation, including all multiplicities and committed columns.
The report therefore leaves `identified_as_published_k_t=false` and the
release gate closed.

## Native trace and fold inventory

`gate_trace_and_fri_schedule` adds a checked inventory for this **Gate-only**
path. It reads the package's 11 native-reconstructed component entries and 45
fixed columns, compares their names, indices and heights to the already
checked package report, and records each component's main and interaction
trace widths. It also records the four PCS commitment trees in source order:

```sh
python3 -B src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/arithmetic/arith4_m31.s31 \
  --lowering gate --out /tmp/s31-p01-arith4-gate
python3 -B scripts/release/pcs_fri_gate_final_domain.py \
  /tmp/s31-p01-arith4-gate
```

| Tree | Columns for a fresh local `arith4_m31` Gate key | Lifted Merkle height |
| --- | ---: | ---: |
| Preprocessed | 45 | `2^21` positions |
| Main | 114 | `2^21` positions |
| Interaction | 152 | `2^21` positions |
| Composition | `2^1 · 4 = 8` | `2^21` positions |

The composition columns themselves have log size 20; all four trees are
*lifted* to log height 21. The 11 component heights are not all 20. For
example, `qm31_ops` has 1,024 trace rows and widths 12 main plus 8
interaction columns, while `verify_bitwise_xor_12` has `2^20` trace rows and
widths 16 main plus 32 interaction columns. For this key the report computes
17,266,176 main trace column cells, 35,203,520 interaction trace column
cells, and 4,252,752 preprocessed column cells before lifting. These are
geometry counts, not proof size or prover time.

The source-pinned FRI configuration has log blowup 1, fold step 1, terminal
degree log 0, and 70 raw query draws. Its verifier requires one first circle
commitment at domain log 21 and degree log 20. That commitment is followed by
one circle-to-line fold. It then requires 19 inner line commitments, each
followed by one fold. The inner commitment domains descend from log 20 to log
2; the final line domain has log 1 and at most one polynomial coefficient.
There are 20 folding challenges in this conditional schedule. The 70 raw
draws may collapse to fewer unique Merkle positions; the unique count is
proof-dependent and remains `null` in a key-only report.

The diagnostic guards the native source expressions for tree commitment
order, composition column count, layer count, fold-step clamp, terminal
degree check and query sampling. These guards are change detectors, not a
Zig control-flow proof. The report does not identify the native degree
bound or oracle with the published theorem's `N`, `D`, `C`, `d`, `L`, `m`,
rate or list bound. In particular, these counts cannot certify the selected
`epsilon(T)/T <= 2^-96` target at `T=2^64`; native security bits remain null.

Focused tests create a bundle envelope, mutate its header/body, mutate the
sealed component order and degree offset, reject a missing native key check,
compare the real pinned bundle offsets and source guards, and reject altered
trace widths, heights, fixed-column rows, fold step and FRI degree:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_gate_final_domain -v
```
