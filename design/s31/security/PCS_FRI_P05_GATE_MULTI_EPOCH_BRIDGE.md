# P05 Gate source bridge: four transcript epochs to two degree tracks

**Status:** experimental source contract. No production selector, native
security-bit claim, or theorem discharge follows from this module.

The executable [plan](../../../formal/s31/tests/lib/p05_gate_multi_epoch_plan.zig)
accepts the *same objects* used by a successful native Gate verification:
the commitment scheme, AIR handles, proof sampled values, and `ProofCapture`.
It invokes the verifier-owned [claim roster](../../../formal/s31/tests/lib/p05_claim_roster.zig),
which rederives every OOD mask point from the AIR and the accepted OOD seed,
checks all four commitment roots and column logs, and matches values in proof
order. The caller is responsible for accepted-object identity; constructing
lookalike objects does not authenticate them.

For each source height, the plan reserves one **original degree-test track**
per committed column and one **own-quotient degree-test track** per OOD claim.
The latter multiplicity matters: a column with two mask samples needs two
quotients but only one original. Every column, including all eight composition
columns, receives an explicit tree/column identity, source height, degree
bound, claim interval, and track slots. Source heights sort descending for the
future multi-domain insertion schedule; the order within one height remains
fixed, main, interaction, composition.

## Why the four roots cannot be flattened

The pinned Gate verifier makes these transcript transitions in order:

```text
fixed root
  -> circuit identity + public outputs -> main root
  -> interaction nonce + lookup challenges/claims -> interaction root
  -> composition challenge -> composition root
  -> OOD challenge -> verifier-owned AIR masks and sampled values
  -> DEEP challenge -> FRI commitments -> PoW -> query positions
```

The composition root is committed **after** the composition challenge. The
interaction root is committed after lookup challenges. CAS09's experimental
XDM05 source root precedes OOD and contains all source columns under one
Merkle root. Replacing these four roots with that root, or recommitting the
same columns under a new root, changes what each challenge can depend on.
`Plan.requireSinglePreOodRoot` therefore rejects this conversion regardless
of whether any root bytes happen to coincide. The plan records native
composition, OOD, and DEEP challenge values for the integration contract; it
does not assert that native DEEP randomness is the paper's required new batch
challenge.

The selected Gate key has 45 fixed, 114 main, 152 interaction, and eight
composition columns: **319 physical columns**. The CAS07 synthetic source
pilot covers 311 source columns at seven nonadjacent heights and has a
193-column largest bucket. Its geometry is useful for implementation sizing,
but its synthetic low-degree words and one source root are not an accepted
Gate proof. The new plan has a focused synthetic four-root control; it has
not yet been run on an accepted 319-column Gate capture.

## Protocol revision needed for a degree test

The next versioned experimental prover/verifier must keep the four original
roots and their challenge timing. After the verifier-owned OOD roster is
fixed, it must build the original and own-quotient multi-domain batches,
commit their separate circle-to-line and line-to-line FRI tracks, then derive
the same raw query positions for all four source roots and both FRI tracks.
Each raw query must authenticate the source-height original pair under its
*original epoch root*; the quotient pair is recomputed from those values and
that column's own OOD claim. Every inserted height, pair fold, line opening,
and terminal coefficient must be checked. Existing production decommitments
cannot retroactively supply the extra pairs or transcript challenges.

The [native sampled-row adapter](../../../formal/s31/tests/lib/p05_own_quotient_rows.zig)
and [native pair-fold control](../../../formal/s31/tests/lib/p05_native_height_pair_fold.zig)
already establish local formulas for authenticated rows. Neither checks the
degree of every committed oracle. Engine CAS09 tests both degrees for a
synthetic one-root multi-height proof, but needs this multi-epoch source and
query protocol revision before it can serve Gate.

The [official S-two theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
states the cross-domain batching error using the maximum batch width `M` of
the **weighted extended ensemble**. It does not identify `M` for this sparse
native Gate roster. The executable plan deliberately leaves
`theorem_batch_width_M = null`: 319 physical columns, 319 original tracks,
and the OOD-claim-dependent quotient track count cannot be substituted for
the paper's `M` without deriving its per-height ensemble definition and
weighting. The paper's theorem also proves a single-point quotient; the
native conjugate two-point quotient needs its own filtration and agreement
reduction. The [theorem bridge](PCS_FRI_CAS05_THEOREM_BRIDGE.md) tracks those
obligations, and the [v0.1 blocker matrix](pcs-fri-v01-blockers.json) remains
closed to this experiment.

Focused source-contract test:

```sh
bash formal/s31/tests/run_pcs_fri_p05_verifier_roster_native.sh
```
