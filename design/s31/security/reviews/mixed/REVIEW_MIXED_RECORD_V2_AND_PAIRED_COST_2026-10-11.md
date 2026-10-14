# Mixed public-record v2: static admission and paired-cost review

Reviewed S31 commit `809d02a82744ffa942e7a137b63c64590cbe3e2d`
against the pinned `deps/stwo-zig` engine. This is a read-only source review:
no native proof, build, Lean proof, or end-to-end soundness claim was made.

## Proof admission

No concrete P1/P2 false-proof path was found in the reviewed mixed v2 route.
The [build selector](../../../../../src/frontends/s31/build.zig) requires the
`-Ds31-version=2` option to agree with the embedded source and confines it to
`direct-mixed-general`. [Bounded admission](../../../../../src/frontends/s31/language/bounded_call_admission.zig)
accepts one public four-lane M31 input and one derived four-lane output,
with one through eight live square/add-constant repeat calls. The
[record ABI parser](../../../../../src/frontends/s31/language/record_abi.zig)
validates field paths, leaf shapes and visibility, then accepts only a
canonical statement whose ABI digest and eight M31 words match the source.
The [prover](../../../../../src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig)
compares those supplied words with independently evaluated assignment words.
The [verifier](../../../../../src/frontends/s31/runtime/mixed_boundary/general_verifier_main.zig)
passes the same typed projection to the source-embedded
[proof wrapper](../../../../../src/frontends/s31/runtime/mixed_boundary/general_package.zig).
That wrapper regenerates the selected manifest, topology, fixed root, AIR
binding and PCS schedule before checking the native proof. The engine mixes
all eight public words into the transcript and the lookup closure.

The [N1/N8 acceptance gate](../../../../../src/frontends/s31/tests/acceptance/mixed_boundary/record_general_v2.py)
tests honest verification, a changed input word, a changed output word,
malformed paths, duplicate statement version and a wrong assignment. At the
reviewed commit, the workflow ran `source_pinned_general.py` but did not yet
invoke `record_general_v2.py`. The reviewer recommended extending the gate
with cross-source and cross-count verifier replay, ABI digest mutation,
other word positions, proof corruption, direct-gate key mutation and mixed
proof-header manifest mutation.
The existing [general mixed review](INDEPENDENT_REVIEW_MIXED_GENERAL_DRAFT_2026-10-11.md)
records engine-level soundness assumptions and proof limits.

After this read-only review, S31 commit `41d022f` wired the v2 gate into
CI. The expanded local gate now passes native N1/N8 proofs (69,488 and
163,853 bytes). It rejects mutations of every public word and claimed-sum
slot, the ABI digest and nominal record name, source/manifest/identity
headers, proof tail, leaf order and path, same-count changed arithmetic
source, cross-count replay, noncanonical M31 words and sums, truncated and
trailing proof bytes, and wrong assignments. The expanded gate still needs
CI on its final pushed revision. Direct-gate key mutation remains part of
the separate paired-package admission gate.

## Minimum safe paired-cost admission

The same **byte-identical normalized v2 source** can feed both lowerings.
The [direct-gate package builder](../../../../../src/frontends/s31/python/package/build.py)
embeds v2 source while using `-Ds31-version=1` as the generic build-route
selector; the mixed builder requires `-Ds31-version=2`. This option difference
does not license changing the relation. Freeze each N1/N8 source SHA-256, each
flat assignment SHA-256, both build fingerprints, and the typed statement
bytes. Check both verifiers against the same typed statement and independently
compare its eight-word projection with the flat assignment. Require original
acceptance, changed input and output rejection, cross-source/cross-count
rejection, and proof corruption rejection before publishing costs.

**Raw prover wall times are not directly comparable.** The generic
[direct-gate prover](../../../../../src/frontends/s31/runtime/mvp_runtime.zig)
self-verifies the committed proof before writing it. The mixed
[general prover](../../../../../src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig)
does not self-verify before writing. Report separately named witness, setup,
prove and verification phases, or instrument both paths to one aligned
definition, before making any proving-speed claim. End-to-end user-facing
wall times can be reported if the difference in work is stated explicitly.

## Engine PR CI provenance

At stwo-zig PR [#237](https://github.com/teddyjfpender/stwo-zig/pull/237),
the [focused circuit CPU integration job](https://github.com/teddyjfpender/stwo-zig/actions/runs/38113522687/job/114393896015)
passed, as did circuit frontend, native CPU, core and circuit recursion CPU.
The engine PR changes `src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig`.
The [AIR source-binding failure](https://github.com/teddyjfpender/stwo-zig/actions/runs/38113522673/job/114393923183)
and [coverage failure](https://github.com/teddyjfpender/stwo-zig/actions/runs/38113522673/job/114393923251)
have the same first errors on [main run `38047739349`](https://github.com/teddyjfpender/stwo-zig/actions/runs/38047739349):
packaged production AIR `add` does not match a fresh unsigned export, and
the production `add` AIR is not canonically bound to the current source.
The aggregate, package, static, native-oracle, RISC-V and CUDA failures also
recur on predecessor [PR #235](https://github.com/teddyjfpender/stwo-zig/pull/235);
the Metal circuit integration runner reports
no Metal device. These red jobs still block the PR's overall CI status;
their first errors do not implicate the changed mixed engine file. Recheck
against a refreshed CI run if the PR head changes.
