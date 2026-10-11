# Independent review: record layout, mixed fixed rows, and cost v2

Reviewed on 2026-10-11 against `042b20c` (record layout), `fff3ded`
(fixed-row fixture), `ae61bec` (frozen cost model), and `1b212bd`
(held-out evaluation). This is a source and tracked-evidence review, with
lightweight static checks. I did not rerun Lean, Zig compilation, native
proving, or the timed measurements. **No critical defect was found in this
scope.** The following boundaries remain material before claiming full
compiler correspondence or a reliable general cost predictor.

## Checks performed

- `check_record_layout_corpus_v2.py` passed: 13 compiled programs, 28 roots,
  eight rejected raw layouts, and four rejected descriptor mutations. Its
  independent tree walk checks emitted leaf path, kind, width, and order.
- `render_lean_mixed_fixed_fixture.py --native-json
  /tmp/s31-mixed-fixed-native.json` matched the checked-in fixture. Its seven
  static mutation tests passed. The generator checks 512 eight-cell fixed
  rows per N1/N8 case, whole-array digests, opcode partitions, and 44/114
  independently calculated selected rows.
- The cost v2 static tests passed. The tracked model SHA-256 equals the
  evaluation's model hash; the model and training corpus match ancestor
  `ae61bec` via `require_model_anchor`. Independent reading of the committed
  corpora confirms four programs and 80 trials in each split. The recorded
  held-out errors and coverage agree with the preregistered formulas.

## Findings and follow-up

1. **Fixed-row proof has a trace-authentication premise.**
   `GeneratedMixedFixedRows.selected_fixed_matches` assumes every fixed cell
   of the decoded trace equals the pinned export. The source hash, exported
   root, and complete row digest are checked by the Python fixture; the Lean
   theorem does not derive the export from compiler semantics or derive that
   equality from verifier acceptance. It also supplies neither main trace
   values nor local `AcceptedRow` facts. Next: bind the verifier's
   authenticated preprocessed root to these columns, then connect the
   accepted main columns and exact event roster to the selected source rows.
   This is a remaining theorem obligation, not a counterexample to the
   conditional result.

2. **Record layout proof covers local shape, not the complete ABI.**
   `checkRoot` validates depth, arity, sibling uniqueness, leaf width, and a
   *per-root* 1,024-leaf limit. The checked-boundary theorem still assumes
   word-block widths match the descriptor and public words are canonical.
   Native aggregate leaf budget, identifier syntax, nominal record-name
   consistency, private-bit prohibition, relation-wire binding, bit value
   range, JSON parsing, and proof authentication are outside it. The generated
   corpus links 28 compiler-emitted roots to the Lean shape walk, but does
   not prove the native parser produces those Lean trees. Next: define and
   prove a full descriptor-to-`RawLayout` refinement, then compose it with
   the word and relation-wire checks. The Python/native root predicate does
   accept a public bit leaf at a root; a direct `_root` probe confirmed that
   the Lean root checker does not have a bit-root parity bug.

3. **Cost v2 is a successful local baseline, with a narrow target.**
   All four preregistered gates passed on four held-out programs: wall
   program-median p90 relative error **26.03%**, proof-size p90 **1.03%**,
   wall-trial band coverage **72/80**, and proof-size coverage **65/80**.
   The predicted target is one fresh prover process plus one fresh native
   verifier process *after package build*. Held-out builds took **52.66–53.76
   seconds per program** and are measured but unpredicted. The wall empirical
   band is **0.443–6.906 times** its center; first-trial cold-start outliers
   exceeded it. With four held-out program medians, the interpolated p90 is
   a small-sample diagnostic, not a tail-latency or cross-host guarantee.
   Next: model build separately, distinguish cold and warm proof latency,
   randomize program order, and replicate on another host before describing
   this as a reliable whole-workflow predictor. No speedup or automatic
   lowering claim follows from this study.

4. **Native replay depends on local raw artifacts.** The tracked cost
   corpora contain hashes, timings, and audit counts; the proofs, exact
   package binaries, and stderr are retained only in the local 72 MiB
   `zig-out/s31-mixed-cost-v2` directory. The audit code did replay all 160
   original and 160 changed claims against those artifacts, but a fresh
   checkout cannot independently repeat that audit without the raw directory
   or rebuilding and rerunning. Next: publish a content-addressed raw
   artifact with its SHA-256 manifest if external replay is required.

The study pins all `src/**/*.zig` bytes. Later edits to those files make
`frozen()` correctly refuse the newer checkout, even if they only change
tests. Replay against the original compiler requires the frozen source
revision; the committed model-anchor check succeeded. A later-checkout
fingerprint mismatch does not imply that measurement used changed bytes.
