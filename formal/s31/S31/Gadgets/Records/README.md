# Named record claim codec (public ABI v2)

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

Focused check:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake env lean S31/Gadgets/Records/NamedCodecV2.lean
```
