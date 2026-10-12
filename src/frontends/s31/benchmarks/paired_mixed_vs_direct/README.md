# Same-source direct circuit versus mixed circuit/chip proof

This study asks whether an authenticated square/add chip helps **actual native
proving** for one admitted S31 program. Both lowerings receive the exact same
normalized v2 source bytes, assignment bytes, and typed public statement.
For cases `(N, rounds) = (1, 16), (4, 16), (1, 1024)`, each of four
M31 lanes computes:

```text
v = x
for call i in 0..N:
    rounds times: v = v² + (13 + i) mod (2³¹ - 1)
    if another call follows: v = v + x mod (2³¹ - 1)
out = v + x mod (2³¹ - 1)
```

The source's public record contains `x.words[4]` and `result.words[4]`.
`direct-gate` expands the repeats into generic Gate AIR rows.
`direct-mixed-general` puts the repeats in separate tagged chip/bridge AIR
components while keeping the surrounding arithmetic in a Gate circuit.
The generated verifier for each lowering embeds the source and its own
component commitment. Different proof envelopes and FRI geometry are part of
the real whole-prover comparison, not normalized away.

The older v1 source is unsuitable for a fair first-verified process wall:
its direct-gate `prove` command internally verifies before returning, while
the mixed prover emits an unverified proof. The v2 record direct-gate command
`prove-for-external-verification` gives both paths the same measured boundary:
one fresh prover process, then one fresh external native verifier process.
The verifier also sees a valid typed statement with one changed result word
and must reject it. A successful source-level evaluation alone never counts
as proof verification.

## Prospective run

1. Run `python3 -B src/frontends/s31/benchmarks/paired_mixed_vs_direct/protocol.py`
   after both v2 proof paths pass a one-claim feasibility check.
2. Commit the protocol and these scripts **before** the scored run.
3. Ensure no concurrent compilation or native proving on the host.
4. Run `python3 -B src/frontends/s31/benchmarks/paired_mixed_vs_direct/study.py --out zig-out/s31-paired-mixed-vs-direct-v1`.
5. Replay every saved proof with `python3 -B src/frontends/s31/benchmarks/paired_mixed_vs_direct/audit.py --out zig-out/s31-paired-mixed-vs-direct-v1`.

The fixed roster has one warmup claim and 12 new scored claims per source,
with six direct-first and six mixed-first pairs in a deterministic shuffled
schedule. Each claim runs both paths. Results report process wall, proof
bytes, and OS peak RSS. Builds and warmup are recorded outside scored pairs.
The native logs also report interaction and FRI proof-of-work time. Subtracting
those timers from process wall is a **diagnostic arithmetic difference**, not
the measured wall time of a separate proof run. Mixed phase timing is enabled
for this study; direct phase timing is always printed by its prover.
Every native proof or verification process has a predeclared 120-second bound;
the build bound is 600 seconds. A timed-out case is reported as a failure and
is never silently omitted.
The script refuses an existing output directory or result file, source/claim
hash drift, changing compiler pins, changed binaries, failed honest verifier,
or an accepted changed claim.

This is a bounded one-host exploratory comparison. It does not establish a
general speedup, confidentiality, or a theorem connecting native accepted
proofs to all trace rows. Proof systems authenticate queried openings and
FRI claims probabilistically. The v2 record ABI and source family are narrow
admissions; other source shapes can have different circuit/chip economics.
