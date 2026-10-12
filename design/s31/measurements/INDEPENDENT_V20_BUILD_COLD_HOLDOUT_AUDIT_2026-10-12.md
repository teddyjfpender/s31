# Independent review of the V20 build and first-use holdout

**Finding: no discrepancy found in the frozen local pass.** This review
recomputed the admission, lifecycle, and warm gates from the committed protocol
and raw artifacts without importing the V20 or V18 scoring functions. It did
not rerun the timed build or proving workload.

## Preregistration and raw identities

- Commit `5d93582` contains the protocol bytes whose SHA-256 is
  `80c8661bfd0d9a09faf4904194318161018bfbe8a99ed098c73548fdf4650d63`.
  Its commit time is 2026-10-12 00:47:32 UTC. The sole attempt marker starts at
  00:49:28.850086 UTC and ends at 00:51:00.109504 UTC. The raw build log's
  filesystem modification time is 00:50:47.091886 UTC; subtracting the
  recorded 78.172015042-second build duration puts its approximate start
  69 ms after the marker. This is consistent with the prescribed order, though
  filesystem times alone cannot prove the benchmark process's clock behavior.
- All 31 frozen production-file SHA-256 values match their bytes at the
  protocol's pinned compiler revision `93114dfa53b9f8762d4da20a41b158992ce61de9`.
  The engine gitlink, three preregistered V20 tool hashes, V18 protocol hash,
  and both historical result hashes also match. The result, score, marker,
  and audit digest links match their committed canonical JSON bytes.
- The raw source and all three native binaries match the recorded hashes.
  The raw manifest matches its recorded digest and its frozen source, six
  ordered call identities, 13 complete slot layouts, 125 constraints, trace
  logs, `[8, 114, 176, 8]` tree columns, and PoW settings.
- All 22 trial rows have the frozen physical order, assignment and statement
  hashes, proof hashes and lengths, process endpoint arithmetic, honest
  `verified` logs, and exact first-result-word `+1` controls with
  `InvalidMixedInteractionNonce` logs. The 20 fresh claims occur in the
  preregistered shuffled order. Direct native replay of `a00r0` returned exit
  0 and `verified` on the honest statement, then exit 1 and
  `InvalidMixedInteractionNonce` on the changed result. The committed V20 audit
  additionally reports native replay of all 44 verifier calls; this review
  directly replayed one pair.

## Recomputed gates

The lifecycle forecast is exactly the componentwise median of the four
committed V18/V19 observations, plus the frozen V18 warm center for 20 fresh
claims. Recomputing from the 22 raw trial records gave:

| Metric | Frozen forecast | Observed | Observed-relative error | Gate |
| --- | ---: | ---: | ---: | ---: |
| Build | 78.164178 s | 78.172015 s | 0.010% | 25% |
| First post-build proof | 1.184328 s | 1.307724 s | 9.44% | 40% |
| Immediate repeat | 0.290695 s | 0.267163 s | 8.81% | 50% |
| Build plus 22 proof-process durations | 86.059710 s | 86.541344 s | 0.56% | 25% |

For the 20 fresh claims, the wall median is 336.155 ms against the 321.025 ms
frozen center; 19/20 wall observations lie in the frozen one-draw interval,
and the median lies inside the frozen sample-median band. All 20 proof sizes
lie in their frozen interval; their median is 254,442.5 bytes. The independently
computed non-PoW wall, prover RSS, verifier RSS, and all four package-stage
median errors each satisfy their frozen limits. The raw records therefore pass
every V20 lifecycle and inherited V18 warm gate.

The 86.541-second quantity sums one build and separately measured process
durations; it excludes idle gaps. The first post-build process was not an OS
cold-cache experiment. This is one host, one prospective run on a source
topology already observed in V18. The pass does not establish cross-host or
unseen-topology prediction, calibrated intervals, or a Cairo speedup. The raw
proofs and binaries currently reside outside Git at
`/private/tmp/s31-v20-build-cold-holdout-93114df-artifacts`; future native
replay depends on retaining them.
