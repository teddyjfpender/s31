# Paired record ABI v2 cost study

Read the [design and runbook](../../../../../design/s31/measurements/PAIRED_RECORD_V2_RUNBOOK.md)
before using this directory. `design.py` generates a native-free inventory;
`protocol.py` freezes its source, assignment, statement, compiler, engine,
tool and host identities; `runner.py` builds two source-equivalent arms and
accepts timed trials only after external native verification. `integrity.py`
durably records raw build and process observations in separate hash-chain
ledgers and requires a separately timestamped phase root before audit or
summary. `test_static.py`
checks inventory uniqueness, balanced order and mutation rejection.

Status: **anchored and audited paired study complete**. The
corrected prospective protocol SHA-256 is
`c1177e83d3e0fb7f37fc232601cc3d20ea6ebe06eda229bee34950968d4cd302`
and its anchor commit is `6091a0773a02e9445946402df0435ab38e1f06a9`.
The [result](../../../../../design/s31/measurements/PAIRED_RECORD_V2_RESULT.md)
finds no whole-workflow speedup for mixed on this pinned relation family.
Untimed generic N=1 and mixed N=1/N=8 native admission controls passed; those
proofs are separate from the paired timing corpus. Automatic lowering remains
disabled.

A later, separate [mixed stage diagnostic](../../../../../design/s31/measurements/MIXED_STAGE_DIAGNOSTIC_V1.md)
measures new source-pinned mixed prover intervals and the external native
verifier process. It does not alter or backfill this anchored study.
