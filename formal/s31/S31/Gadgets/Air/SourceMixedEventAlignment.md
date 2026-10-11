# Mixed event order and correspondence

The circuit Gate claim sees all bridge Gate reads together. The component
claim fold sees each call's bridge reads beside its chip inputs and endpoint.
Within a call, the chip's terminal endpoint also precedes its input rows in
the ideal source list, while the bridge claim expression places it after
them. These sequences have equal **occurrences**, including multiplicity,
but generally do not have equal order.

`SourceMixedAuthenticatedTrace` therefore requires `List.Perm` for the two
global event alignments. A proved permutation leaves the reciprocal sum
unchanged for every challenge pair. `SourceMixedEventAlignment.lean` derives
both global permutations from a smaller source/component contract:

- The circuit lists identify Gate row uses/yields, public words, and all
  bridge Gate reads.
- Each call identifies its chip input/output events and bridge start/finish
  events with the source-shaped native row tuples.

`EventProjection.ofSourceRows` derives both circuit list equations from the
source row roster, empty baseline lists, public words, and each bridge's
eight Gate events. `EventProjection.assemble` then constructs the full trace
contract from that projection, source row identity, public word identity, and
claim fold. The five per-call projections remain compiler/committed-trace
obligations. The native optional full-trace audit
checks a value-bearing Gate event bag and the complete chip and bridge rows;
ordinary succinct verification still needs a PCS/FRI soundness argument to
authenticate those rows.

The public result also needs the separate `LocalPublicSchedule` premises:
address selection, unique producers, packed input/final state memberships,
and output unpack/copy paths. Its chip transition equation follows from the
projected row tuples, chip AIR arithmetic, and a fixed-constant binding in
`SourceMixedChipRowProjection.lean`. Merely comparing a sidecar assignment with
`relation.evaluate` does not prove those circuit paths.
