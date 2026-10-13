# Record v2 scalar values and the typed evaluator

`GeneralRecordV2ValueCorrespondence.lean` closes a value-level gap in the
bounded record-v2 model. The exact-source checker had already reconstructed
the typed program, but its independent scalar evaluator and the actual
`S31.Program.environment` were previously run separately. Equality of two
program structures cannot establish equality of those two evaluator
implementations.

The new proof has three steps:

1. `node_value` proves that source integer arithmetic modulo `2147483647`
   agrees with the actual `S31.evaluateNode` on one-word M31 add/mul nodes.
2. `nodes_related` inducts over **any** finite source node list with unique,
   fresh names. It relates every wire lookup after every instruction. Source
   evaluation prepends results; normalized evaluation appends them, so the
   freshness condition is necessary.
3. `checked_source_result_fields` starts from a successful exact-source
   `Static` package and source evaluation, then relates **all** ordered record
   result selectors to the actual typed `Program.environment`. Duplicate
   selectors remain duplicate record fields even though the normalized public
   output list deduplicates their wire names.

Here is the worked example in the Lean file, written as S31 source:

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit combine(public visible: Pair, private secret: Pair) -> public Pair {
    let sum = visible.left + secret.left;
    let product = sum .* visible.right;
    Pair { left: product, right: sum }
}
```

For `visible = {left: 2, right: 3}` and `secret = {left: 4, right: 5}`,
the source values are `sum = (2 + 4) mod p = 6` and
`product = (6 × 3) mod p = 18`. The ordered result record is `(18, 6)`.
The public claim vector is `(2, 3, 18, 6, 0, 0, 0, 0)`; neither private word
appears in that vector. `worked_environment_bridge` applies the general fold
theorem, and `worked_result_bridge` derives the typed result values from it.
The file also checks that changing the private `secret.left` while preserving
the public claim, or changing the public result, yields `publicMismatch`.

The theorem's `InputAlignment` premise explicitly states how canonical source
input words were partitioned into public and private typed assignments, and
that the resulting initial environments agree. The exact-source checker does
not yet derive this premise for every admitted record shape. The theorem also
stops at `Program.environment` and typed record result values; a general
`Program.evaluate`/claimed-word theorem, with output deduplication and every
public statement layout discharged, remains open. Native AIR, PCS, and FRI
correspondence remain separate obligations.
