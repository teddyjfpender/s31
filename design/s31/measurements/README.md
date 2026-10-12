# S31 measurements

For the current process-inclusive measurement contract and reproducible
arithmetic, hash, and fixed-width corpus, see
[whole-prover cost evidence](WHOLE_PROVER_COST.md).
The [twelve-program held-out record](language/whole-prover-heldout-2026-10-10.json)
pins the measured latency-model failure, proof-byte and RSS errors, and
native trial controls.
The latest [V24 independent audit](INDEPENDENT_V24_CONDITIONAL_REPEAT_AUDIT_2026-10-12.md)
reports a passed frozen conditional-repeat forecast on one source and host;
the [V23 failure](MIXED_COST_V23_N8_HOLDOUT_RESULT.md) and earlier V17
failure are retained. These results do not establish cross-host calibration
or an automatic lowering policy.

These are retained records of specific experiments, not current performance claims. The JSON payloads are kept byte-for-byte when files move so their command lines, source names, and hashes remain historical evidence.

| Directory | Workload |
| --- | --- |
| [bitcoin/](bitcoin/) | Bitcoin header, chain, work, and fold profiles. |
| [sha/](sha/) | SHA AIR and circuit profiles. |
| [hash/](hash/) | General hash and Poseidon/BLAKE comparisons. |
| [payments/](payments/) | Blinded hash-note payment proving audit and matched runtime measurements. |
| [recursion/](recursion/) | Recursive proof and verifier costs. |
| [language/](language/) | Language lowering and Cairo comparisons. |
