# General mixed generated verifier binding review

Scope: normalized source version 1, `direct-mixed-general`, one through eight
calls; `build.zig`, `runtime/mixed_boundary/general_{manifest,prover,verifier}_main.zig`,
`general_package.zig`, and the black-box `source_pinned_general.py` acceptance.

## Authority path

The build requires an explicit normalized source path and matching declared
version. It embeds the same source bytes and official AIR bundle in the
prover, verifier, and manifest inspector. The inspector's `--check` is a
build dependency for both binaries. Its JSON report is an audit view, not a
file supplied to the verifier.

The verifier parses its **embedded** source, derives public words from the
supplied statement, and calls `verifyEmbeddedAndInspect`. That package
rebuilds the selected source schedule, live native component geometry,
registry manifest digest, and circuit identity. It checks the proof's call
count, slot count, source/registry/identity header digests, and canonical
claimed sums before bounded postcard decoding. The native engine then checks
the fixed root, PCS config, public output, interaction nonce, lookup closure,
component handles, and STARK proof. For v1, the separately saved statement's
source/selected-manifest/registry/identity metadata is checked against the
verified inspection result. There is no caller-selected verifier key or
component manifest in this CLI.

## Acceptance weakness and repair

The positive black-box matrix covers N=1..8. Header and statement mutations
run for every count; lane-wise public-word, compensated-claim, malformed-wire,
and changed-source controls run for N=1,3,8. The prior changed-source branch
reused one source path and install prefix across counts. It only checked that
the new inspector source digest differed from the current original source.
A stale verifier from an earlier count could therefore reject a resealed
proof at the **count** check and make the source-binding control vacuous.

The test now gives every changed-source count its own source file and build
prefix. Before proof mutation, it requires the inspector's digest to equal
SHA-256 of those exact changed bytes, its call/slot counts to equal this case,
and its registry digest to recompute from the displayed manifest. The test
reseals source, registry, and circuit identity fields in both proof and saved
statement. It rejects success, process crashes, and rejection solely through
the outer envelope or statement-identity checks. A remaining rejection is
therefore attributable to deeper native proof binding for these fixtures.

## Limits

The changed source appends whitespace, preserving program semantics and row
geometry while changing source identity. The static source-to-call projector
checks endpoint continuity and freshness but cannot derive absolute circuit
addresses on its own; native inspection recompiles them. The executable
tests do not prove that verifier acceptance authenticates every AIR cell,
that the lookup argument has no exploitable collision, or that PCS/FRI and
Fiat–Shamir are sound. The registry JSON is a reproducible audit report; the
verifier's authority is its embedded source and its own reconstructed typed
registry, not that JSON file.
