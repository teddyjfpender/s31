# Coupled four-lane chip for the authenticated mixed boundary

Status: **design only**. This specifies a second *semantic* native chip kind.
It does not extend native proof admission, install an AIR, or establish a
speedup. The existing pair and many constructors both prove the independent
lane recurrence `x -> x² + c`; their different names and call limits do not
constitute two kinds of computation.

This contract builds on the [general boundary contract](GENERAL_AUTHENTICATED_BOUNDARY.md).
The current mixed N=3/N=4 verifiers and registry revision 1 remain fixed.
A new profile and registry revision are required.

## Source meaning and one worked round

Use the **already admitted source-language** `iterate` step operations. A
candidate native kind, `square_add_mix4_v1`, admits exactly this normalized
body on `[m31; 4]`, with one canonical `0 <= c < p` and power-of-two
`16 <= R <= 32768`:

```s31
fn coupled(v: [m31; 4]) -> [m31; 4] {
    std::math::mix4((v .* v) + splat<4>(7_m31))
}

circuit two_kinds(private x: [m31; 4]) -> public [m31; 4] {
    let a = iterate<16>(
        fun(v: [m31; 4]) -> [m31; 4] => (v .* v) + splat<4>(13_m31), x);
    let middle = a + x;
    let b = iterate<16>(coupled, middle);
    b + x
}
```

The `middle` addition is deliberately in the *circuit* between the two
different chips. The current bounded native admission rejects an arithmetic
node as a chip input because it has packed lanes without four scalar Gate
addresses. Constrained scalarization and matching topology/witness address
maps are prerequisites for proving this example with a native mixed profile.
In particular, the four scalar ports for `middle` must be circuit wires
whose base-field values are constrained equal to the four packed coordinates
of `a + x`; copying host-evaluated words into a bridge would leave a gap.
The text frontend and generic circuit already represent its normalized
`repeat` body `square; add_const(7); mix4`.

For state `s=(s0,s1,s2,s3)`, define `qj=sj²+c`, `h=q0+q1+q2+q3`, and
`F_c(s)j=qj+h`, all in M31 with `p=2³¹-1`. `mix4` is the existing S31 operation
that adds the four-lane sum to **each** lane; it is not a bit shuffle.

| Round | Input | After square and `+7` | Sum | Output |
| --- | --- | --- | ---: | --- |
| 0 | `[0,1,2,3]` | `[7,8,11,16]` | 42 | `[49,50,53,58]` |
| 1 | `[49,50,53,58]` | `[2408,2507,2816,3371]` | 11102 | `[13510,13609,13918,14473]` |

This is not four copies of the current recurrence: changing any input lane
changes every output lane. No per-lane affine conjugation from the existing
one-call square chip implements that cross-lane dependency.

## AIR and endpoint contract

One chip row has `i`, four `in` words and four `out` words. The proposed
base trace retains the existing nine-column layout and the same bit-reversed
circle-domain storage. For each row and each lane `j`, constrain

```text
q_j = in_j² + c                 (an expression, not an extra trace column)
out_j - q_j - (q_0+q_1+q_2+q_3) = 0.
```

The four transition polynomials have degree two. There are no selector or
padding rows: exactly `R` rows are committed. The source-derived `R` and `c`
are immutable verifier AIR parameters, and the witness writer independently
checks the exact source operation. The AIR must install the *same* four
constraints in prover domain evaluation and verifier point evaluation.

Use a new relation ID `R_MIX4` (candidate `0x53333104`, subject to a global
registry collision audit), distinct from Gate and the existing tagged
square/add relation. The canonical seven-coordinate event is

```text
T_mix(call_id, step, state) =
    (R_MIX4, call_id, step, state_0, state_1, state_2, state_3).
```

Chip row `i` emits `+1/T_mix(call_id,i,in) - 1/T_mix(call_id,i+1,out)` in
the LogUp rational sum. Its interaction trace has the existing two fractions,
eight M31 columns, and a constrained claimed sum. The component's remaining
two constraints establish the fraction inverse and running-sum recurrence,
for six constraints total. The verifier additionally checks the source-bound
endpoint relation through the installed chip and bridge AIRs and the global
lookup closure. Algebraically, an honest chip satisfies

```text
chip_claimed_sum - 1/T_mix(call_id,0,initial)
                 + 1/T_mix(call_id,R,final) = 0.
```

Here `1/T` abbreviates `1/(f_alpha(T)-z)`. The verifier does **not** know
the private `initial` and `final` words and cannot evaluate this displayed
equation directly. It checks the ordered claimed sums and closure while the
installed bridge AIR commits and constrains those endpoint words. Together,
the row-event multiset and bridge endpoints force a length-`R` path from
index 0 to R when lookup compression is collision-free: each edge increments
the index, and there are only R committed edges, with R less than the M31
characteristic. It is not enough to check the transition rows alone or to
trust the prover's final state. The exact reduction, including duplicate
event multiplicities and nonzero denominators, needs independent review.

Each call also gets a bridge with eight constant endpoint columns (four in,
four out) at the current bridge log size 4. The bridge constrains those
columns constant across its rows, emits the eight Gate events with the
opposite sign to the circuit's Gate obligations, and emits
`-1/T_mix(call_id,0,initial) + 1/T_mix(call_id,R,final)` to cancel the
chip's endpoints. The bridge copies **compiler-owned scalar Gate addresses**,
not addresses supplied by proof bytes. Its anticipated shape is eight main
columns, twenty interaction columns and thirteen constraints, as in the
existing tagged bridge, but its source hash and relation ID must be new.
The four lane values must be canonical M31 words; the base-field endpoint
extraction rejects nonzero extension limbs.

The Gate tuple stays `(R_GATE,address,value,0,0,0)`; its six coordinates are
not a new event kind just because the consuming chip differs. Zero-padding
both tuple forms to seven coordinates is safe **only** after checking the
first-coordinate relation IDs differ. Producer and consumer copies of an
intended event have exactly the same tuple, with opposite signs. The event
cannot be distinguished only by a role or a manifest string because those
do not enter the algebraic lookup key.

## Source-derived registry and proof package

Registry revision 2 adds immutable constructors `mix4_chip_v1` and
`mix4_bridge_v1`, each with separate AIR source digest, version, role,
relation IDs, parameters, witness writer, live AIR constructor, claimed-sum
extractor, and exact geometry. An admission pass selects the chip kind from
the **canonical normalized body**, never from a package field, proof header,
filename, or manually supplied manifest. Reject a body with another order,
an extra operation, a noncanonical constant, a dead or merged call, or a
repeated call with inconsistent source-to-canonical mapping. Existing
`square; add_const` calls keep their existing registered constructors.

Compile the source once into a witness-free plan with each call's ID,
normalized body digest, `R`, `c`, input/output scalar Gate addresses, and
public-output liveness. Independently compile the witness and compare every
address, fixed-column root and roster field before writing a trace. The
verifier recreates the plan from its embedded authenticated source and
official AIR bundle **before proof decoding**. It instantiates live verifier
AIR handles from the closed registry, compares their actual spans,
constraints, lookup relations and source hashes with the source-derived
typed manifest, then checks a bounded envelope. The manifest JSON is only an
inspection view; a rehashed sidecar cannot authorize a changed constructor.

The roster is `circuit, chip(0), bridge(0), ..., chip(n-1), bridge(n-1)` for
`1 <= n <= 8`. Claim slots and sum indices follow that order exactly. Bind
registry version, constructor IDs, call/body parameters, endpoint addresses,
all component source/program hashes, preprocessed root, public ABI, profile
tag, PCS geometry and roster digest to a new transcript domain before the
first witness commitment. The verifier installs every claimed sum in its
corresponding live AIR; checking only a claimed-sum total would let an
unconstrained component float. Use one fixed, main, and interaction
commitment and one native PCS/FRI proof for the whole roster.

The v1 pair/many registry currently chooses kind by **call position** and
the source admission accepts only `square; add_const`, so this is a new
admission rule, not an extension implied by the present inspector. The first
native milestone should retain source-pinned fixed N=3/N=4 behavior under
their old tags, then add a separate mixed-v2 tag with body-derived kinds.

## Bounds, cost and verification work

Keep the current caps of eight calls, total `2¹⁸` chip rounds, `16..32768`
rounds per chip, and checked trace-cell/proof-byte arithmetic. If the same
bridge and chip widths hold, each new call contributes `17` main and `28`
interaction columns, `19` constraints, and `17R + 28*16` committed M31 cells
before any extra circuit scalarization cost. Its chip quotient evaluation
log bound should be `log2(R)+1`; bridge bound remains its existing higher
degree. These are **geometry predictions**, not benchmark results. The
cross-lane sum makes the row arithmetic cost higher than square/add even
with the same column count. Compare against the exact same source compiled
as generic circuit, including setup, peak RSS, wall time, proof bytes and
native verifier time; choose native lowering only where measured total cost
wins or where an explicit user choice requests it. The V7r1 cost model is
trained on an earlier stack and cannot validate this new kind without a new
prospective study.

For the shared QM31 challenges, a conditional bound is available only after
counting **all** emitted Gate, old-chip, mix4-chip and bridge tuples. If `T`
is the number of distinct, injectively encoded seven-coordinate coefficient
vectors and all signed imbalances are nonzero mod M31, the algebraic
collision/false-closure term is at most
`[6*binom(T,2)+2*T-1]/|QM31|` under ideal independent uniform challenges.
This is separate from AIR, PCS/FRI and Fiat-Shamir soundness. An actual v2
release must derive T and total occurrence bounds from its checked plan;
the transcript must draw challenges only after main commitments are fixed.
The current unblinded traces also make `private` an ABI visibility rule,
**not witness confidentiality**.

Required acceptance evidence:

1. An independent integer/M31 oracle for two worked rounds, the full 16-round
   example, boundary field values `0`, `p-1`, and varied constants including
   `0`; compare text, normalized JSON, generic circuit and native chip.
2. One native proof with old square/add chip, a constrained circuit addition,
   then mix4 chip; dependent and independent calls; every count 1..8 where
   admitted; repeated Gate addresses with multiplicity; public-output
   liveness and rejection of an unused call.
3. Mutate one lane in each transition, mix4 sum, input/output bridge word,
   Gate address, step index, constant, rounds, kind, AIR source hash,
   component role/order/span, claimed sum, public word, fixed root, and
   transcript tag. Include independently resealed wrong manifests and
   cross-version/cross-kind replay, rather than only checksum corruption.
4. Check soundness of the new AIR constraints and endpoint reduction in both
   prover and verifier evaluation paths, source/canonical/witness address
   correspondence, lookup collision budget, preflight limits and native
   proof decoding. Run a separate reviewer before removing `experimental`.

No proof is produced by this document. In particular, neither the current
fixed-roster proof nor the existing abstract Lean `mix4` row theorem proves
this proposed native AIR or the complete compiler-to-PCS correspondence.
