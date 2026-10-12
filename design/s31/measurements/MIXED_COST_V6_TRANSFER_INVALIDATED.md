# V6 transfer attempt: unscored compiler-pin failure

The [v6 protocol](language/mixed-cost-v6-transfer-protocol.json) was
committed as `c1efdde` before the first native build. Its SHA-256 is
`265ecd7fc0297b1f52eda4e71ccc7627d2a0ce9b23d965a4c7da7ba4c67a1bc5`.
The one intended run emitted 164 proof files under the local
`zig-out/s31-mixed-cost-v6-transfer/` bundle. Before the runner could write
or score a result, its mandatory final `p.frozen()` check failed:

```text
ValueError: protocol or pinned stack differs from pre-native freeze
```

The exact mismatch was the compiler fingerprint: frozen
`6e37c595b79044ec588bec26f5325daf1173bf5b1c19d9fe10c61cb164c42ca1`,
observed after the run
`246bb1b688eefd02ab242526911a86f62e90d9bd6d91b944ce573b8f2f413f37`.
An uncommitted change to
`src/frontends/s31/language/bounded_call_admission.zig` was made during the
run to admit a new public-record bit/alias shape. The v6 simple-shape sources
may not be affected by that logic, but the protocol pinned the full compiler
fingerprint and did not permit a changed stack during timing.

**No v6 wall, PoW or proof-size score is reported.** There is no v6 result or
score JSON. The run is an integrity failure, not evidence that the frozen v4
cost predictor passed or failed on the v6 cohort. The raw bundle is retained
for forensic inspection, with no score-selected rerun. A new v7 protocol
will use entirely new sources and claims after the admission change is
committed and the stack has stabilized.
