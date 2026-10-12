# From raw AIR rows to the mixed lookup claim

The mixed proof has one 512-row circuit Gate component, one chip component per
call, and one bridge component per call. A lookup term for a tuple `t` has a
denominator `z - compress(alpha, t)`. Away from zero denominators, its AIR
residual forces the interaction column to contain the intended reciprocal.

For example, a Gate row may produce a value that no later row reads. Its fixed
output multiplicity is zero, so the *ideal* lookup event list omits the output.
The physical Gate AIR still checks the singleton equation

```text
(interaction difference) × (z - compress(alpha, output tuple)) = 0.
```

At `z = compress(alpha, output tuple)`, both sides are zero whatever the
interaction difference is. The equation loses its power at that challenge.
The native prover refuses to divide by zero, but the soundness argument must
also account for a malicious committed trace. The independent
[pole review](../../../../../design/s31/security/INDEPENDENT_REVIEW_MIXED_POLE_CLOSURE_2026-10-11.md)
and native regression isolate this case.

`SourceMixedPoleClosure.lean` puts three sorts of challenge pair into one
exceptional set:

1. compression collisions that can conceal an imbalanced ideal event list;
2. poles of every emitted ideal tuple, even when the two lists balance;
3. poles of all 512 physical Gate output denominators, including outputs with
   zero multiplicity.

Outside that set, `RawGateRows.toChecked` derives all three nonzero conditions
for every Gate row from the source row identity and converts the raw AIR
residuals to the checked reciprocal-sum contract.

`SourceMixedBridgePoleClosure.lean` treats a bridge similarly. Each bridge
has eight Gate endpoint tuple factors and two chip endpoint tuple factors at
its anchor row. The local event-list inclusion plus the same challenge
exclusion supplies their nonzero conditions. The bridge main AIR makes its
eight words constant over sixteen rows, so the anchor factors govern the
remaining rows in the existing bridge claim theorem. Chip paired interaction
residuals already derive their input/output denominator conditions.

`SourceMixedRawTraceClosure.lean` composes these steps. Its
`RawAuthenticatedMixedTrace` carries every raw Gate/bridge row equation, the
checked chip rows, fixed Gate row identity, public words, event-list
permutations, and the total claimed-sum fold. Its `toChecked` theorem
constructs the checked all-row trace outside the exceptional set. The
`raw_scheduled_false_word_is_exceptional` theorem then combines a source row
schedule and explicit chip/bridge event projection with that trace: if one
public word is false, the challenge pair lies in the exceptional set.

`SourceMixedRawEventAlignment.lean` derives the two global event-list
permutations from five local, per-call equalities: the bridge's eight Gate
reads, the chip input and output tuples, and the bridge start and finish
tuples. The fixed Gate row roster and public output words then determine the
circuit side of those lists. Its checked-projection theorem reuses those same
five equalities after the raw pole conversion. The local-certificate theorem
takes raw component rows, those five equalities, fixed source mappings, and
the claimed-sum fold; it derives the global permutations and checked trace
internally.

For the pinned one-to-eight-call source shape, the set has at most
`36,494,846 × |QM31|` pairs. This is a finite **fixed-witness algebraic**
bound. It becomes a probability bound only with a suitable independent
challenge draw after the relevant trace is committed.

The theorem does not derive the five local tuple equalities, source row
identity, public word mapping, or claim fold from native proof acceptance.
Those are the next compiler and committed-trace correspondence obligations.
It also does not
prove Fiat–Shamir independence, Merkle/PCS extraction, FRI soundness, or
witness confidentiality. In particular, the raw false-word theorem without
the scheduled variant takes `LocalPublicPath` as a premise; its Gate
arithmetic residuals do not establish that local path by themselves.

Run the focused Lean check from `formal/s31`:

```sh
lake build S31.Gadgets.Air.SourceMixedRawTraceClosure
```
