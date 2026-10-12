# V23 immediate-repeat cost diagnosis

V23's frozen overall score remains **FAIL**: the single same-claim repeat took
187.442 ms against a preregistered 284.862 ms point forecast, an observed-relative
error of 51.97% against a 50% gate. This note analyzes the recorded result; it
does not change the protocol, score, gate, or number of native attempts.

## What the measured time contains

The reported verified-wall time is the sum of one prover process and one
external-verifier process. The table subtracts the two reported native proof of
work (PoW) durations from that sum; **non-PoW** still includes process startup,
native proof generation, packaging, and external verification. Each warm
non-PoW figure is the median of that record's 20 fresh-claim residuals. All
figures below are milliseconds, recalculated from the committed V18–V23 result
records in `design/s31/measurements/language/`.

| Run and source | Repeat wall | Repeat non-PoW | Repeat FRI PoW | Repeat interaction PoW | Warm non-PoW median |
| --- | ---: | ---: | ---: | ---: | ---: |
| V18, six calls, log 13, eight branches | 296.53 | 148.86 | 146.61 | 1.06 | 148.48 |
| V18, six calls, log 14, eight branches | 377.54 | 248.12 | 124.74 | 4.69 | 247.97 |
| V18, seven calls, log 14, 32 branches | 284.86 | 256.05 | 27.85 | 0.97 | 250.98 |
| V19, six calls, log 13, eight branches | 217.69 | 143.89 | 72.89 | 0.91 | 145.68 |
| V20, six calls, log 14, eight branches | 267.16 | 241.93 | 22.99 | 2.25 | 242.74 |
| V21, five calls, log 13, four branches | 280.64 | 161.11 | 118.53 | 0.99 | 150.58 |
| V22, six calls, log 13, three branches | 228.49 | 152.68 | 75.25 | 0.56 | 151.87 |
| **V23, eight calls, log 13, five branches** | **187.44** | **164.12** | **20.84** | **2.48** | **161.30** |

The V23 forecast is the median of the **five individual repeat wall times in
V18–V20**, namely 296.53, 377.54, 284.86, 217.69, and 267.16 ms. Its
selected median is the V18 seven-call **log 14** run. The selected run's
non-PoW residual exceeds V23's by 91.93 ms; its combined PoW exceeds V23's by
5.49 ms. Together these account for the 97.42 ms point-forecast overshoot.
The dominant mismatch is therefore the mixed-geometry repeat baseline, with
the one-draw PoW realization adding some error. In particular, two log 14
records contribute roughly 242–248 ms non-PoW residuals to a forecast for a
log 13 source. The code implements its documented five-record median rule;
there is no evidence here of a score extraction or arithmetic bug.

The V23 repeat's 164.12 ms non-PoW residual is only 2.82 ms above its own
fresh-claim median of 161.30 ms. Across the eight rows, the repeat residual
differs from its own warm median by at most 10.53 ms. Claim 0's first and
repeat assignment, statement, and proof SHA-256 values match in every record.
Their reported combined PoW durations are close within each pair; V23's were
25.06 and 23.32 ms. This is consistent with the same proof workload being
repeated while claim-to-claim PoW work differs. It does not establish that
host timing is otherwise controlled: V21 had known competing compiler work,
and V22/V23 only checked host quietness immediately before the attempt.

## A future, preregisterable repeat model

For a *new* holdout, freeze the source-specific non-PoW predictor and the
following online rule **before** any native observation:

```text
predicted_repeat_verified_wall
  = frozen_source_nonpow_center
  + first_same_claim_fri_pow_duration
  + first_same_claim_interaction_pow_duration
```

The first proof's reported PoW durations become conditioning inputs available
before its repeat starts; the repeat itself supplies no forecast input. Require
exact assignment, statement, proof, source, and binary identities for the
pair. Score the repeat's non-PoW residual separately from the conditioned
whole-process time. To judge reliability, preregister several fresh claims
with one immediate repeat each and score the *distribution of paired errors*,
rather than requiring a single stochastic draw to meet a point-estimate gate.
Freeze the claim roster, ordering, interval or error gates, timing extractor,
and one-attempt semantics before the next run. A simpler one-repeat protocol
could instead use the already frozen source-specific V18 one-draw wall interval,
while clearly reporting its nominal coverage.

For scale only, applying that proposed formula **retrospectively** to V23 gives
150.346 + 22.668 + 2.389 = 175.403 ms, versus the observed 187.442 ms
(6.42% observed-relative error). The unchanged V18 one-draw wall band was
156.761–518.003 ms and includes this repeat. These are post-result diagnostics,
not a prospective V23 pass or evidence that the next rule is calibrated.
