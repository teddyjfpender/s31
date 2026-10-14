# Independent review: mixed N=3 lookup and boundary equations

**Date:** 2026-10-11. **Exact reviewed heads:** S31
`bd36d2f6316bf3cc4105117a541d058791117672`; engine
`807530990cdb9c8fc346801e6f1f44611e9f47dc`. I reviewed these in an
isolated clean worktree. This review does not cover later mixed-file moves or
changes in the integration worktree.

**Decision:** Go for the source-pinned, experimental N=3 verifier through
`mixed_boundary/package.zig:verifyEmbedded`. No concrete false-proof admission
was found in the reviewed lookup, boundary, or transcript path. This is not a
proof of cryptographic LogUp/PCS/FRI soundness or a general mixed-call release.

## Equation and binding review

The three-call roster is circuit, then chip/bridge for each call. Calls 0 and
1 use the pair AIRs and call 2 uses the many AIRs
(`direct_mixed_schedule.zig:160-203`, `direct_mixed_admission.zig:44-52`). The
pair and many chip equations have the same transition and running-sum forms;
the pair and many bridge equations likewise match, with different admitted
call-ID bounds (`tagged_pair_chip.zig:262-283`, `tagged_many_chip.zig:257-278`,
`tagged_pair_bridge.zig:278-295`, `tagged_many_bridge.zig:274-291`).

Each chip row proves four `output = input² + constant` equations and contributes
a tagged `(relation ID, call ID, step, state)` input term minus its
`step + 1` output term. The verifier supplies the call ID and constant from
the rebuilt source plan, not from a trace column. Each bridge constrains its
eight endpoint columns to be constant around the 16-row cycle. Its four
paired fractions consume the eight corresponding six-word circuit Gate
yields; its fifth fraction contributes the tagged last state minus first
state (`tagged_pair_bridge.zig:97-118,278-304`, with matching many bridge).
The direct circuit increments its committed multiplicity once per endpoint
occurrence, including repeated addresses
(`common/direct_arithmetic.zig:193-199`). The circuit public-output lookup
terms and all seven claimed sums are checked for zero closure before the
claims are mixed into the transcript (`direct_mixed_arithmetic.zig:399-409`,
`:523-532`).

Under **separate** authenticated all-row AIR and non-colliding lookup-tuple
premises, the tagged multiset equation forces the bridge's step-0 and
step-`rounds` states to be connected by chip transitions. There are exactly
`rounds` chip rows; since admitted `rounds` is below the M31 modulus, a path
from step 0 to step `rounds` using `step + 1` consumes all rows. This is a
review argument, not a machine-checked theorem. Zero denominators or
challenge-compression collisions require a separate quantitative bound.

The sealed verifier compiles the literal source and official AIR, rebuilds
the mixed geometry and manifest digest before bounded proof decoding, then
checks source/manifest/identity headers
(`mixed_boundary/package.zig:115-213`). The engine rechecks fixed root,
bundle/program binding, plan geometry, public words, seven claims and unused
claim slots, then gives the ordered handles to the core verifier
(`direct_mixed_arithmetic.zig:459-575`). Prover and verifier order the profile,
salt, FRI config, fixed commitment, circuit identity, public values, main
commitment, nonce, lookup draw, seven claims, interaction commitment and PCS
proof the same way (`:323-445`, `:495-575`). The in-process engine adapter
remains caller-authorized for S31 source semantics; the sealed entrypoint is
the proof-byte admission boundary.

## Focused controls run

I ran
`zig build --build-file src/frontends/s31/build.zig test-mixed-native -Doptimize=ReleaseFast -j1`
in the isolated exact-head worktree. It passed;
the sealed proof was 98,363 bytes, with local prove/verify times of 68/3 ms.
The test exercises honest verification; each of seven claimed-sum mutations;
a compensated two-sum mutation; wrong public words; source, manifest and
identity changes; resealed call-order and endpoint changes; trailing bytes;
and V4 cross-profile rejection (`mixed_boundary/package.zig:216-322`). The
source-roster control
`zig build --build-file src/frontends/s31/build.zig test-mixed-composition-admission -Doptimize=ReleaseFast -j1`
also passed on these exact heads. The
engine's separate in-memory test also has commitment-root and unused-sum
controls (`direct_mixed_arithmetic.zig:578-684`); I inspected but did not
independently run that separate engine test.

The remaining release work is a formal or independently analyzed reduction
from accepted native proofs to authenticated all-row mixed AIR constraints,
including random-composition, PCS/FRI, Fiat–Shamir and lookup collision
bounds. The tests above exercise one N=3 source program and do not establish
that reduction.
