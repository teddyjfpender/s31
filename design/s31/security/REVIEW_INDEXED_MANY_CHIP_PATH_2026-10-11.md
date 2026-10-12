# Independent review: indexed one-to-eight-call chip path

Reviewed the 2026-10-11 workspace, S31 base `d373ebc`, and pinned native
`deps/stwo-zig` at `7d544c683`. This review follows the new
[`IndexedManyChipPath.lean`](../../../formal/s31/S31/Gadgets/Air/IndexedManyChipPath.lean)
statement through source admission, compiled endpoints, fixed Gate columns,
native chip and bridge AIRs, generated roster, lookup closure, and the
source-embedded verifier. I found **no concrete false-public-claim path** in
the inspected bounded profile. The Lean result is a conditional exact-event
theorem, not an end-to-end theorem about native proof acceptance.

## Exact theorem and native correspondence

The theorem's events are abstract `(Fin N, Nat, F)` values: a call tag, step
index, and state. For each call, the bridge yields `(call, 0, start)` and
consumes `(call, R, finish)`; each of its `R` chip rows consumes
`(call, index, input)` and yields `(call, (index + 1) mod p, output)`. Given an
**exact permutation** of the joint event lists, `0 < R < p`, and each row's
local step equation, `per_call_balance` filters by call tag and
`every_call_complete_path` derives `finish = step^R(start)` for every call.
The proof permits arbitrarily ordered witness rows and rules out a spare
unattached cycle because all `R` rows are used by canonical indices.
`nativeCallId_injective` establishes only that IDs `0..N-1` remain distinct
in M31 when `N <= 8`; the source-to-roster mapping is a separate obligation.

| Native layer | Checked source evidence | Link to the theorem |
| --- | --- | --- |
| Call selection | [`bounded_call_admission.zig`](../../../src/frontends/s31/language/bounded_call_admission.zig) admits one to eight live four-lane `square; add_const` calls, with consecutive IDs and bounded rounds. [`inspection.zig`](../../../src/frontends/s31/runtime/mixed_boundary/inspection.zig) rebuilds their compiled addresses and ordered circuit/chip/bridge slots. | Supplies candidate `Fin N`, `R`, constants and endpoints; not proved equal to Lean data here. |
| Gate wires | [`direct_arithmetic.zig`](../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig) starts from `CircuitView.computeUses` and adds one checked fixed-column multiplicity for **every** bridge endpoint occurrence, including forked/repeated inputs. Its fixed root is checked by the verifier. | Supports the claimed Gate-to-bridge value join, conditional on the native AIR and lookup argument. |
| Chip AIR | [`tagged_many_chip.zig`](../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_chip.zig) and the pair variant fix a call ID per component, constrain all four equations `out = in² + c`, and emit tagged seven-coordinate tuples `[relation, call, step, state₀..state₃]`. The AIR does not locally sort or range-check witness steps. | Local step matches the four-lane instance of `F`; native field-tuple extraction to `(Fin N, Nat, F)` remains to prove. |
| Bridge AIR | [`tagged_many_bridge.zig`](../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig) and the pair variant constrain eight endpoint columns constant across 16 rows, read eight Gate tuples, and contribute chip tuples at steps `0` and `R`. Gate and chip relation IDs differ. | Candidate authenticated `start`/`finish`; row constancy, Gate joins and tuple projection are additional premises. |
| Verifier | [`general_package.zig`](../../../src/frontends/s31/runtime/mixed_boundary/general_package.zig) rebuilds source/registry/circuit identities before bounded proof decoding; [`direct_mixed_general_arithmetic.zig`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig) checks root, public words, claimed-sum closure, live handles, transcript and STARK proof. | Native acceptance supplies a compressed lookup equation, not the theorem's exact event permutation without further cryptographic reductions. |

The statement parser is not a discovered ambiguity: Zig 0.15.2's
`std.json.ParseOptions` defaults `duplicate_field_behavior` to error, and the
V1 verifier also rejects unknown fields. V2 uses the separate canonical record
ABI parser. An earlier negative test that repeats `public_words` with a wrong
value is not, on its own, evidence for duplicate rejection; the parser default
and V2 explicit option supply that evidence.

## Lookup and multiplicity budget

The checked [`lookup_budget.zig`](../../../src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig)
requires circuit rows `16..2^16`, one to eight calls, each with power-of-two
rounds `16..32768`, total rounds at most `2^18`, and exactly nine public Gate
terms: eight statement words plus the reserved `u` wire. For `R` circuit
rows, `S` chip rounds, `N` calls, and `O=9`, it counts at most
`E = 3R + 2S + 160N + O <= 722185` lookup occurrences. Its conservative
integerized absolute-weight bound is
`B = 16(4R + 8N + 2O + 2S) + 160N <= 12585504 < p`.
This counts fixed Gate multiplicities and each bridge row separately, so a
nonzero integer tuple imbalance cannot disappear merely modulo M31.

The [lookup worksheet](LOOKUP_COMPRESSION_BUDGET_2026-10-11.md) derives the
conditional algebraic term `(7T - 6) / p^4`, with `T <= E`, for fixed,
injectively encoded tuple occurrences before independent uniform `alpha,z`
draws. The worst stated term is below `2^-101.73`. This is **not** the
soundness error of the whole proof. It assumes main-trace commitment before
the challenges, correct AIR enforcement, suitable Fiat–Shamir sampling, and
PCS/FRI soundness. Relation-domain admission checks Gate/chip tuple layouts,
but a formal native tuple-to-exact-event correspondence is still open.

## Focused hardening and evidence

The compiler allocates a fresh `guessM31` wire for each repeat output. A
source-produced output-to-output or output-to-earlier-input alias should
therefore never appear, although `validateUniqueProducers` alone does not
forbid using one valid producer as two calls' output. I extended
`requireFreshOutputPorts` in [`inspection.zig`](../../../src/frontends/s31/runtime/mixed_boundary/inspection.zig)
to reject both cross-call alias shapes. Its focused unit controls also retain
valid earlier-output-to-later-input chains, repeated input addresses, and
forked inputs. The helper is called during source inspection and again when
building the generated registry manifest; the source compiler remains the
authority for the actual endpoint map.

`zig build --build-file src/frontends/s31/build.zig
test-mixed-composition-admission -j1` passed after the change. Existing
[`source_pinned_general.py`](../../../src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py)
has accepted native proofs for counts 1–8 and rejects per-word changed claims
for counts 1, 3 and 8, compensating claimed sums, changed source identity,
truncated/trailing/oversized envelopes and malformed statements. I did not
rerun those full proof tests for this review; the targeted test exercises
source admission, not adversarial STARK witness synthesis.

## Open proof obligations

1. Establish a source-and-native correspondence for all admitted calls:
   source endpoints, unique fresh output wires, actual seven-coordinate
   chip/bridge tuples, six-coordinate Gate tuples, fixed multiplicities and
   verifier-selected roster must instantiate the abstract exact events.
   [`TaggedPairEventProjection.lean`](../../../formal/s31/S31/Gadgets/Air/TaggedPairEventProjection.lean)
   handles a source-shaped **two-call** ideal projection; the new theorem
   starts after projection for arbitrary `N`.
2. Derive exact joint tuple balance from accepted native LogUp and AIR/PCS
   checks with an explicit error bound, accounting for transcript challenge
   sampling and the bounded multiplicities. The budget worksheet proves only
   a conditional algebraic term.
3. Complete compiler-to-AIR semantic correspondence and whole-prover
   soundness. Native black-box mutation tests are useful regressions, not
   substitutes for these proofs. The mixed committed traces also do not
   establish witness confidentiality.
