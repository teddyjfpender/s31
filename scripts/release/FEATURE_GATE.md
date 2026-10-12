# Scoped S31 feature gate

[`s31_feature_gate.py`](s31_feature_gate.py) invokes existing acceptance and
security scripts for the newer language paths. It does not implement another
prover, verifier, source parser, or value oracle. Use it from the repository
root:

```sh
python3 -B scripts/release/s31_feature_gate.py --mode source --list
python3 -B scripts/release/s31_feature_gate.py --mode source \
  --out zig-out/s31/feature-gate-source.json
python3 -B scripts/release/s31_feature_gate.py --mode smoke \
  --case direct-mul-u8-native --out zig-out/s31/feature-gate-mul-u8.json
python3 -B scripts/release/s31_feature_gate.py --mode full \
  --out zig-out/s31/feature-gate-full.json
```

`source` runs the independent bounded v1 and v2 source-to-relation tests,
static-sum dead-code tests, the 112-program static-enum effect corpus, all ten signed/unsigned widths for checked addition,
subtraction, order, and checked/wrapping multiplication through source and
independent value-oracle checks, and public u8/u16/u32 record ABI static checks.
It builds no native proofs.

`smoke` includes those source checks and selected native proofs: static-sum DCE
on a dedicated chip, static enum effect staging with three direct-Gate proofs,
the bounded v2 record source fragment, u8 addition,
i8 subtraction/order, u8 checked/wrapping multiplication, and public u8/u32
record ABI. `full` expands the direct integer native runs to all ten widths and
adds the public u16 record ABI proof. The bounded v1 checker remains source-only;
its tests include re-sealed relation mutations but establish only the
`source-to-relation-only` capability. The v2 record source proof binds the
checked record fixture to a native generated verifier; it does not prove a
general compiler theorem.

Every selected command must exit successfully and report its expected set of
cases and positive controls. The runner records the exact argument vector,
working directory, script SHA-256, command SHA-256, subprocess exit status,
stdout/stderr SHA-256, and a result SHA-256 over those values. It checks the
compiler fingerprint before and after each command and at the start/end of the
run. Script or compiler drift, a failed command, a missing case, or a missing
negative control makes the run fail and exit nonzero. Later rows remain
`not-run`. `--list` executes no checks and cannot pass a gate. Repeated `--case`
arguments select a focused loop; `mode_complete` is true only when every row
for that mode passed in this invocation.

This report is finite executable evidence, with `release_claim` permanently
`not-established`. It does not certify AIR soundness, PCS/FRI security, the
full compiler correspondence theorem, or all programs. The separate
[`s31_v01_audit.py`](s31_v01_audit.py) covers CLI lowering inventory and its
own handwritten equivalence fixtures.
