# V24 conditional-repeat cost challenge

This is the **frozen protocol for the completed one-attempt V24 challenge**. The [independent result audit](../../../../../design/s31/measurements/INDEPENDENT_V24_CONDITIONAL_REPEAT_AUDIT_2026-10-12.md) reports a pass for every preregistered gate; the [canonical score](../../../../../design/s31/measurements/language/mixed-cost-v24-conditional-repeat-score.json) records the measurements. The protocol was prospective when frozen and must not be refit or rerun to change its score. Its new log-13 S31 source has four live arithmetic branches of 1,280 operations each, one multiplication every four operations, a balanced join, and eight ordered repeated-square calls of 2,048, 64, 4,096, 128, 512, 32, 1,024, and 256 rounds. Twenty-one distinct claims are pinned: claim 0 immediately after build, then 20 fresh claims in frozen random order. Each claim was proved and externally verified twice in adjacent processes, giving 42 honest proofs and 42 exact changed-result rejection controls. The same-claim pair has identical assignment, statement, and proof hashes.

The V18 warm cost model is reused without fitting to V23. The source-specific log-13, eight-call non-PoW center is the V17 four-call baseline plus four frozen average-call steps. For **each repeat**, the protocol freezes an online formula before the native run:

```text
predicted verified repeat wall time
    = frozen source-specific non-PoW center
    + measured FRI PoW time of the first proof of this same claim
    + measured interaction PoW time of the first proof of this same claim
```

The first proof's PoW durations are known before its repeat starts. No repeat measurement enters its own forecast. The repeat gates require median observed-relative error at most 20%, at least 18 of 21 paired errors within 35%, and repeat non-PoW median observed-relative error at most 20%. The 20 first proofs of nonzero claims retain V18's frozen warm wall, proof-size, RSS, and package-stage gates. Build and first-use forecasts remain V18–V20 five-record medians; the build-plus-42-process sum uses the frozen warm wall center for the 41 processes after first use and has a 25% gate. The sum excludes idle gaps. V17 and V23 remain failed holdouts regardless of V24's outcome.

The runner checks the exact source-derived manifest before proofs: 17 slots, 163 constraints, tree columns `[8, 148, 232, 8]`, and all ordered call and slot fields. Two quiet-host `ps` snapshots one second apart are required before the atomic attempt marker. Once the marker exists, any native failure is the one recorded attempt; no retry is permitted. First use is not a controlled operating-system cold-cache measurement. One host and source do not establish cross-host calibration or a Cairo speedup.

The following static preregistration checks ran before native observation:

```sh
python3 -m py_compile src/frontends/s31/benchmarks/mixed_cost_v24_conditional_repeat/*.py
python3 -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v24_conditional_repeat -p 'test_*.py'
python3 src/frontends/s31/benchmarks/mixed_cost_v24_conditional_repeat/freeze.py check
```

The single native attempt used the first command below. The second command
replays the independent audit against its retained artifacts; it does not
measure proof timing again.

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v24_conditional_repeat/study.py run \
  --out /private/tmp/s31-v24-conditional-repeat-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v24_conditional_repeat/audit.py \
  --out /private/tmp/s31-v24-conditional-repeat-artifacts --native
```

Canonical source, protocol, marker, result, score, and audit records live in `design/s31/measurements/language/`. Native replay requires retaining the raw artifact directory. A preflight rejection before the marker consumes no attempt; the reason and absence of native output must be documented.
