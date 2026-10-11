# Paired record ABI v2 cost study

Read the [design and runbook](../../../../../design/s31/measurements/PAIRED_RECORD_V2_RUNBOOK.md)
before using this directory. `design.py` generates a native-free inventory;
`protocol.py` freezes its source, assignment, statement, compiler, engine,
tool and host identities; `runner.py` builds two source-equivalent arms and
accepts timed trials only after external native verification. `integrity.py`
durably records raw process observations in a hash-chain ledger and requires a
separately timestamped phase root before audit or summary. `test_static.py`
checks inventory uniqueness, balanced order and mutation rejection.

Status: **no native paired result or speed claim**. The protocol file and
timestamp anchor have not been generated. This study is separate from V8 and
must not run during V8's exclusive measurement phases.
