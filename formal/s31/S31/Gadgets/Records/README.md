# Named record claim codec (public ABI v2)

`SourceValueV2.lean` models the bounded width-one M31 record source fragment's
execution. It checks each result field against a shared SSA program, proves
every checked field equals its source expression for arbitrary inputs, and
rejects swapped-field and split-alias certificates. The independent Python
source/value checker and native Zig differential corpus are described in
[`RECORD_SOURCE_RELATION_FRAGMENT_V2.md`](../../../../../design/s31/language/RECORD_SOURCE_RELATION_FRAGMENT_V2.md).
This theorem models the admitted fragment and does not parse production source
bytes or authenticate proof openings.

[`NamedCodecV2.lean`](NamedCodecV2.lean) joins the checked type-tree walk and
the public statement word decoder for one already parsed root. The native
implementation is `src/frontends/s31/language/record_abi.zig`, whose current
schema is `s31-public-record-boundary-v2`.

For a root named `request` with the declared type

```text
record Pair {
  left:  m31[1],
  right: m31[1]
}
```

and leaf values `left = [1]`, `right = [2]`, `encode` emits claims in this
order:

```text
path [root "request", field "left"]   words [1]
path [root "request", field "right"]  words [2]
```

`decode` checks the type tree, each ordered path, exact declared width, and
the kind-specific range. It then splits the flat words `[1, 2]` back into
`[[1], [2]]`. Swapping the two claims is rejected even though the flat words
would still have the same length. A public `bit[1]` claim accepts `0` or `1`
and rejects `2`; duplicate sibling field names are rejected before decoding.

The main theorem, `decode_encode`, applies to any bounded `RawLayout` accepted
by `checkRoot` (1–64 children per record/tuple node, at most 32 edges of
nesting, at most 1,024 leaves per root), with a block of the declared width
and correctly ranged words at every leaf. It proves that checked decoding
recovers every block in declaration order. `decode_sound` proves the converse
data-loss property for an accepted arbitrary claim list: decoded blocks have
exactly the declared widths and concatenate to the entire claimed word
stream. `encode_paths_nodup` proves distinct complete paths after sibling-name
validation. The visibility lemmas show that a private root contributes no
public named claims and that public roots on either side of it retain their
declaration order.

This codec models semantic claim lists after parsing. It does not prove Zig
JSON parser correspondence, canonical JSON serialization, nominal consistency
between multiple roots, first-order relation wire references or aliases,
public statement padding, ABI digest authentication, or STARK verification.
Those are handled by adjacent formal modules and native tests, with full
compiler correspondence still open. `checkRoot` permits a public bit leaf;
the whole-descriptor validator separately rejects private input bit leaves.

The [public u32 boundary example](../Functional/RecordU32BoundaryV2.md)
walks through a two-u16-limb record value, repeated result aliases, its
eight-word proof projection, and the exact Lean packing theorems. Its model
starts after validated descriptors and does not claim native parser or AIR
refinement.

Focused check:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake env lean S31/Gadgets/Records/NamedCodecV2.lean
```

[`GeneratedMixedEightV2.lean`](GeneratedMixedEightV2.lean) is a separate,
source-pinned finite certificate for the record ABI v2 eight-public-word
example in
[`mixed_eight_alias_bit.s31`](../../../../../src/frontends/s31/tests/acceptance/record_abi/mixed_eight_alias_bit.s31).
It checks concrete named paths, field order, `bit` bounds, private-root
erasure, the two shared result references, and rejection when either shared
reference is given inconsistent claimed words. The small structured Lean
terms are generated from the actual text compiler output and exact typed
statement; the adjacent Python runner pins the full JSON bytes and passes
them to Zig. Lean does not check the JSON parser or hash function, so the
finite byte-level differential and the kernel theorem have distinct scopes.
See the [record ABI acceptance guide](../../../../../src/frontends/s31/tests/acceptance/record_abi/README.md)
for commands and all adversarial cases.

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake env lean S31/Gadgets/Records/GeneratedMixedEightV2.lean
```
