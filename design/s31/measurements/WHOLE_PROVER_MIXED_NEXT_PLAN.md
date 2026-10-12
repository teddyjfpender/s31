# Prospective whole-prover study for mixed circuit/chip composition

Status: **design only**. This study starts after the one-to-eight-call native
profile passes its engine, source-pinned verifier and black-box acceptance
gates. The V7r1 corpus is frozen on an earlier compiler/engine revision and
does not include mixed proofs. Its fitted coefficients must not be applied to
the new profile or silently transferred to a later source revision.

## Questions and measurements

For the *same* normalized source and each same assignment, compare the
general mixed circuit/chip lowering with the generic direct-gate lowering.
Both paths must have source-pinned native verifiers and the same eight public
words. Record fresh-process prover wall, native-verifier wall, their sum,
proof bytes, prover peak RSS, package build time, and native witness,
interaction PoW, FRI PoW, composition, PCS/FRI and verifier stages when
instrumentation exposes them. Keep stage sums and unattributed process time
separate. Save the sealed component manifest and public statement for every
package. A successful proof from either path is insufficient unless its
native verifier accepts the honest statement and rejects a changed canonical
public claim.

The mixed feature record must be recomputed from a source-pinned manifest
and checked against live geometry, not supplied by the benchmark caller. At
minimum it contains circuit raw/padded rows, preprocessed cells, pair/many
chip round counts and trace cells, 16 bridge rows per call, component count,
ordered main and interaction column spans, maximal composition domain, PCS
and FRI settings, and proof-of-work bits. The direct-gate feature record
uses the corresponding sealed cost report. Models should fit process stages
from training data and leave PoW variation visible; a tiny training set is
not a reason to invent a precise universal speedup formula.

## Prospective protocol

1. Freeze compiler, engine gitlink, AIR bundle, source grammar, package and
   verifier binaries, host/compiler identity, benchmark/oracle/tool digests,
   assignments, target definitions and gates. Include five training and five
   held-out programs in each stratum: one or two calls, three or four calls,
   and five to eight calls. Vary power-of-two rounds and circuit arithmetic
   while respecting the admitted limits. Source and assignment bytes must
   be disjoint across splits and prior corpora; disclose repeated shapes.
2. For each program, use at least 100 assignments shared by the two
   lowerings. Randomize which lowering runs first for each paired assignment
   and record order and timestamp, so drift is visible. Build packages before
   timing proofs. Run prover and verifier in fresh processes. Independently
   evaluate each statement from source semantics and retain both proof files.
3. Anchor the protocol hash and commit externally before the first training
   package build. Fit all coefficients, intervals and any lowering policy on
   training only. Commit and externally timestamp the model hash before the
   first held-out build. No held-out tuning, replacement programs or changed
   gates are permitted.
4. On held-out programs, evaluate per-stratum wall, proof-byte and RSS
   prediction errors and empirical interval coverage with the predeclared V7
   accuracy gates as the minimum. Report paired speedup ratios and their
   distribution per program and stratum; never compare unmatched program
   family means. Reopen all packages, manifests, statements and proof hashes,
   rerun honest and changed-claim native verification, and provide a portable
   content-addressed replay before declaring the result.

Passing on one pinned host supports only local prediction and paired
comparison for the tested profile. A recommendation to select a lowering
automatically also needs verifier-equivalence review and a separate
changed-stack/host transfer study. Failed accuracy must remain visible; a
new prospective study may be designed from training diagnostics, but cannot
retrofit the frozen held-out split.
