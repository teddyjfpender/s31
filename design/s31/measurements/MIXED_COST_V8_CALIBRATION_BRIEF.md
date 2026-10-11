# Why V8 changes the whole-prover predictor

V5 and V7 were prospective transfers of the frozen V4 cost model to fresh
one-call and eight-call sources. Both failed a preregistered gate. V6 is an
unscored integrity failure and contributes no performance data. The V8 model
is fit from the committed clean V4 calibration, V5, and V7 artifacts, and
will be scored only on two fresh V8 sources and their fresh claims.

| Clean source | Scored claims | V4 predicted wall p50 | Observed wall p50 | FRI PoW p50 | Non-PoW whole-wall p50 | V4 proof interval coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| V5 `scaled_seed_n1` | 20 | 84.21 ms | 60.85 ms | 31.64 ms | 28.15 ms | 17/20 |
| V5 `weighted_scan_n8` | 20 | 88.34 ms | 105.72 ms | 71.10 ms | 34.76 ms | 20/20 |
| V7 `affine_seed_n1` | 80 | 84.21 ms | 92.34 ms | 60.23 ms | 28.31 ms | 62/80 |
| V7 `switchback_n8` | 80 | 88.34 ms | 130.82 ms | 98.47 ms | 34.48 ms | 74/80 |

The non-PoW whole-process medians agree closely within each call-count
profile, while FRI PoW medians vary widely. A 26-bit geometric hash search
has a long tail; source/session rate variation and finite samples can move
its median substantially. The V7 N8 wall miss is therefore principally a
PoW clock miss: its observed non-PoW median was 34.48 ms versus V4's roughly
33.11 ms base-plus-calibration-residual median, while FRI PoW was 98.47 ms
versus V4's 53.13 ms median.
This is post-run attribution, not evidence that the source geometry changes
hash difficulty. The V5 N1 sample has only 20 draws, so its low median is
especially uncertain.

The V4 proof-size centers were accurate within 1% for all four sources, but
its single 3.397% relative half-width missed V7 N1's 80% minimum coverage.
V8 keeps those centers. It calibrates a 95th-percentile error separately for
small and large profiles, then takes the maximum across the four clean
source blocks in each profile. V8's frozen widths are 5.869% and 4.235%.
This makes the interval wider where the observed proof-size variation is
higher; it does not prove cross-source coverage.

All eight clean source manifests have `main_columns = 17c + 12`,
`interaction_columns = 28c + 8`, `constraints = 19c + 11`, and `slots = 2c + 1`
for call count `c`. Those features have no independent rank in this data.
V8 therefore retains the V4 call-count baseline, records exact expected
geometry as a profile guard, and does not claim to have learned a separate
column or constraint cost coefficient. Future profiles with geometry varying
independently require new measurements and a new prospective evaluation.

V8's 26-bit FRI PoW predictor is an equal-weight mixture of four exponential
clocks, each calibrated from one V5 or V7 source median. It retains the V4
interaction clock and non-PoW residuals. The mixture produces whole-wall
5th/50th/95th percentiles and an empirical median envelope from the smallest
and largest observed source rates. The envelope describes this limited fit;
it is not a formal confidence or coverage bound. A changed host rate can
still fail the fixed 30% wall-median gate.

The [V8 experiment](../../src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/README.md)
uses 80 scored claims per new source and retains V7's four per-source gates
without relaxation: at most 30% wall-median error, at least 80% coverage of
the nominal 90% wall interval, at most 10% proof-median error, and at least
80% coverage of the nominal 90% proof interval. The model, source identities,
numeric predictions, and limits are committed before native measurements;
any gate miss remains a failure. It is a one-host transfer check, not a
general-purpose proof-cost guarantee or a Cairo comparison.
