# Independent static review: coupled mix4 AIR draft

Reviewed engine commit: `eb789bfefe5d395789422e372deb14132344f47f` in
`/private/tmp/stwo-s31-mix4-air-draft`, against
`design/s31/language/MIX4_COUPLED_CHIP_CONTRACT.md` and the V4 tagged-many
chip/bridge. This review inspected source only. The cost-study build slot was
reserved, so no Zig compilation, native proof, verifier, mutation, or Lean run
is evidence for this draft.

## Findings

1. **No concrete false-proof path found in the standalone mix4 equations.**
   `mix4_coupled_relation.zig:38-46` computes
   `q_j = s_j^2 + c`, `h = sum(q_j)`, `out_j = q_j + h`.
   `mix4_coupled_chip.zig:303-322` constrains the same four equations, plus
   the two LogUp inverse/recurrence equations. The point and domain evaluators
   both call this `rowConstraints` function, so their algebraic residuals are
   identical. The chip's degree-two bound `log_size + 1` covers the four
   transitions and its inverse/recurrence products. This is an equation
   inspection, not a native proof soundness result.

2. **The bridge event signs and multiplicities match the contract.**
   `mix4_coupled_bridge.zig:93-113` combines each pair of Gate denominators
   as `(d0+d1)/(16*d0*d1)` on each of 16 rows. Its eight constant endpoint
   columns are constrained row-to-row at lines 274-290. Thus a sound bridge
   yields one positive copy of each of its eight Gate events. Its last
   fraction is `(-1/T_0 + 1/T_R)/16` per row and cancels the chip's
   `+1/T_0 - 1/T_R`. The bridge's cubic products fit `log_size + 2`.
   Repeated Gate addresses remain separate occurrences and require the
   circuit's source-derived multiplicity count. No mix4-specific sign or
   omission was found.

3. **Release blocker: the draft is not source-authenticated or proof-admitted.**
   `mod.zig:32-35` exports the three primitives, but no mixed-v2 registry,
   canonical-body admission, constrained scalarization/repacking, source and
   witness address-map comparison, source-derived roster/manifest, new
   transcript domain, sealed bounded proof decoder, or native verifier
   installs them. Directly constructing the public `Component` structs with
   unrelated `call_id`, `constant`, `boundary.rounds`, or Gate addresses would
   not prove a source program. These fields must come from one verified plan,
   and every claimed sum must enter the corresponding live AIR handle. This
   is a known incomplete boundary, not a demonstrated bypass in a released
   proof profile.

4. **Release blocker: the conditional lookup bound is not yet recomputed for
   a mixed roster.** The new seven-coordinate key begins with
   `0x53333104`, distinct from Gate (`378353459`, or `0x168d3733`, in the pinned circuit),
   the old untagged chip (`0x53333102`) and pair/many (`0x53333103`).
   The first-coordinate separation and shared seven-power compressor are
   correct for the audited primitives. A new profile still needs a checked
   source-derived count of every emitted tuple and integerized weight bound
   below `p`, including circuit multiplicities, all old and new chips,
   bridges and outputs. The earlier `B <= 12585504` worksheet is conditional
   on emitter counts and cannot simply be inherited. Nonzero denominators,
   challenge sampling after main commitments and the PCS/FRI/Fiat-Shamir
   terms remain separate obligations.

5. **Adjacent global relation-ID collision, relevant to future composition.**
   The S31 SHA direct word bus defines `0x53333103` in
   `src/frontends/s31/sha/air/sha_direct_word_bus.zig:17`, the same ID as
   the engine's pair/many tagged relation in
   `src/integrations/circuit_cpu/private_pair_boundary.zig:23`. The SHA
   encoder at `sha_direct_word_bus.zig:80-82` emits six coordinates
   `(03, call, address, lo, hi, 0)`; the pair encoder at
   `private_pair_boundary.zig:246-247` emits seven coordinates
   `(03, call, step, s0, s1, s2, s3)`. The SHA tuple zero-padded to seven
   equals the old-chip tuple when
   `(step,s0,s1,s2,s3)=(address,lo,hi,0,0)`. Current source-pinned
   mixed-arithmetic proof profiles do not include SHA, so this is not a
   mix4-draft exploit. Add an admission guard that rejects any roster placing
   the current SHA-word and pair/many constructors in one LogUp challenge
   domain. For a future composition, define a central versioned relation-ID
   registry with compile-time uniqueness over its admitted constructors;
   allocate a fresh SHA-word-v2 ID (candidate `0x53333105`, after a full
   registry audit), bump that component's source identity and the composite
   profile/transcript tag, and add cross-kind collision tests. Keep every
   existing admitted ID and profile unchanged so old proof bytes remain
   valid. The new mix4 ID `0x53333104` did not collide with any relation ID
   found in the searched engine/S31 source.

6. **Validation gap and build risk.** The new tests cover two hand-calculated
   rounds, a 16-round modular oracle at constants `0`, `7`, and `p-1`, one
   in-memory closure, canonical endpoint extraction, and one mutated
   transition residual. They do not run an installed prover/verifier AIR or
   mutate every lane, bridge word, step index, claimed sum or source-bound
   profile field. Since `mod.zig` imports these new modules in its test
   block, a Zig compile failure would also block the engine module test.
   Compile the targeted engine tests after the reserved cost run, then build
   one real source-pinned mixed-v2 proof and independently verify the listed
   mutation matrix before changing the draft status.

## Conditional reduction checked on paper

If each transition row satisfies `out = F_c(in)` and the shared lookup
compressor is collision-free on the source-derived event set, chip rows emit
`+T(i,in) - T(i+1,out)`, the bridge emits `-T(0,initial) + T(R,final)`, and
the circuit's negative Gate obligations cancel the bridge's eight positive
Gate events. Exactly `R < p` chip rows are committed. A path from step zero
to step `R` consumes at least `R` edges; with only `R` rows no disjoint
cycle or extra edge remains. Duplicate event multiplicities must be counted
as signed integers before reduction modulo `p`. This argument assumes the
new profile authenticates the endpoints, roster, source body, parameters,
main commitments and all component claimed sums; the draft has not yet done
so.
