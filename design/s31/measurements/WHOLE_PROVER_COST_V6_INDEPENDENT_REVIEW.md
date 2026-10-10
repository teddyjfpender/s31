# Independent review of the V6 whole-prover cost publication

Reviewed the committed V6 publication at S31 `188e4068f2c312aab715c93697ee67e185c835d9` against the frozen study branch at `41b564bac42abfd71fdf27a9f1ecf77e75d16a2f` and the retained raw artifacts. This was a read-only replay: no native proof was regenerated and no model, protocol, gate, or measurement report was changed. **No blocking discrepancy was found.**

## Frozen identity and chronology

| Item | SHA-256 or commit |
| --- | --- |
| Protocol JSON | `c839427e3651a92f07710e5fc446cfa8fb022fbe4f70245d8fa22ec01c5c5b14` |
| Training corpus JSON | `bad7cbcd5d27f9546c2a2edad1ccdb28e8fec498f17df40e7637424b9a62a59d` |
| Frozen model JSON | `0f0d4356123fa6ee85e1653c4224a9abbfaf8ec011037a5aa1c47ec374876b7c` |
| Validation corpus JSON | `02bf8f9f47c8b2f548d47c0243dc7b5059c2ed5ec60a36bc3da2efe96e23e903` |
| Evaluation JSON | `e51e1d332282a6d2c9b492841f445814e8f8d1fde9dfcddda18af87122310909` |
| Published audit JSON | `05bac7095a4b1f82a20c52898410f7cd886020a8a4e78c26e1f768e37b2e5b01` |
| Protocol anchor commit | `b3191bd5d9c0b7a2afc71b440e9c2e636ef1d2af` |
| Model anchor commit | `22223af1ea5a0486ce7bcebfb66bc064cafab233` |

Both anchor commits are ancestors of the remote `feat/whole-prover-cost-v6-freeze` head `41b564bac42abfd71fdf27a9f1ecf77e75d16a2f`. The committed anchor bytes bind the stated hashes. The protocol and model anchor records carry UTC times `2026-10-10T21:37:42Z` and `2026-10-10T22:19:29Z`; their corresponding commits have later commit timestamps. The protocol, fitter, runner, and publisher source did not change between the model anchor and frozen publication. The retained validation build inventory binds both anchor commits and the frozen model hash. Repository evidence confirms reachability and binding; the separate external timestamp messages establish the claimed order relative to native phases.

## Raw evidence replay

The split contains 23 training programs with 100 trials each and 20 held-out programs with 100 trials each. All 4,300 assignments have distinct digests; training and held-out source and assignment digest sets have zero intersection. V6 source and assignment digests also have zero intersection with the published V4 and V5 inventories.

Running the frozen publisher in memory produced an object exactly equal to the committed V6 audit. Its artifact pass matched all 4,300 saved proof-file SHA-256 digests and sizes, all 4,300 full trial reports, all 4,300 saved assignment digests and public statements, and all 43 source/package bindings. It checked saved native-verifier acceptance, independent-oracle success, and changed-public-claim rejection flags for every trial. The publisher refit the model using the training corpus alone and replayed held-out evaluation without a mismatch. The V6 runner and publisher enforce the frozen tool, compiler, source, engine, protocol, model, and generated chip-manifest bindings; the model and audit leave automatic lowering disabled.

## Held-out metric and gate check

I separately recomputed each program's measured point and trial coverage from its raw trial values, then each family's interpolated p90 point error and total trial coverage. These agree with the saved evaluation and published report. Each cell below is **p90 relative point error / trial interval coverage**.

| Family | Prover plus verifier wall | Proof bytes | Prover peak RSS |
| --- | ---: | ---: | ---: |
| Arithmetic | 13.581% / 440 of 500 | 4.995% / 499 of 500 | 2.574% / 493 of 500 |
| Direct chip | 11.193% / 445 of 500 | 4.735% / 480 of 500 | 2.998% / 500 of 500 |
| Fixed width | 13.779% / 431 of 500 | 2.591% / 499 of 500 | 8.675% / 500 of 500 |
| Hash | 3.003% / 434 of 500 | 0.173% / 483 of 500 | 0.032% / 495 of 500 |

The frozen gate requires, per family, wall p90 error at most 25%, wall coverage at least 80%, and median wall interval upper bound at most 8 times measured mean. Proof bytes and RSS each require p90 error at most 10% and coverage at least 80%. Every held-out program requires RSS coverage at least 70% and an RSS upper bound at most 1.5 times its measured median. The lowest program RSS coverage was 93 of 100 (`arithmetic_1280`); the highest RSS upper-to-median ratio was 1.452605 (`signed_quotient_32`). All predeclared checks pass, including the saved success flags for 2,000 held-out native trials.

The nine integrated V6 Python tests pass. The invalid-anchor test intentionally asks Git to resolve a nonexistent all-`a` commit; Git emits a `fatal: Not a valid commit name` line on stderr while the expected rejection and test pass.

## Limits

This is a prospective check on one Apple M5 Max host and one compiler revision. The wall intervals reflect fresh-process PoW variation and remain empirical; they do not guarantee future tail coverage. Package-build time is outside the predicted wall target, and Zig cache state during builds was uncontrolled. Cross-host transfer, cached setup, and compile-to-proof latency were not established. The artifact replay verifies saved acceptance and oracle flags and proof bytes; it does not independently rerun native verification or the value oracles. Automatic lowering remains disabled.
