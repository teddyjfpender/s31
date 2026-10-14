# From a public statement to the control circuit's pins

The [conversion AIR proof](ControlGadgetConversionAir.md) establishes what
each of the five installed `m_31_to_u_32` rows means, conditional on its
range and Gate lookup tuples. This continuation identifies which **claim**
the native verifier puts into those Gate lookup events. It covers the one
sealed control source shown in the [public pin example](ControlGadgetPublicPins.md).

## The eight words

The source declares one public scalar `x`, two private four-lane inputs, and
one public four-lane `result`. For `x=0` and private selected input
`b=[1,2,4,8]`, the expected inverse is:

| Statement slot | Meaning | Claimed M31 word | `low` | `high` | Gate address |
|---|---|---:|---:|---:|---:|
| 0 | `x[0]` | 0 | 0 | 0 | 3 |
| 1 | `result[0]` | 1 | 1 | 0 | 4 |
| 2 | `result[1]` | 1073741824 | 0 | 16384 | 5 |
| 3 | `result[2]` | 536870912 | 0 | 8192 | 6 |
| 4 | `result[3]` | 268435456 | 0 | 4096 | 7 |
| 5–7 | ABI padding | 0 | 0 | 0 | 8–10 |

The statement JSON contains only `public_inputs.x` and
`public_outputs.result`; it contains no private inputs. The package's sealed
`public-abi.json` fixes their names, shapes, order, and M31 encoding.
`relation.claimedWords` checks the canonical M31 values, places the public
input first, then the four public outputs, and initializes the remaining
three slots to zero.

```text
source.s31 ──parse/lower──> sealed relation and public ABI
                              │
public-only JSON ─claimedWords─┴─> eight u32 words
                                   │
                                   ├─> (low16, high16, 0, 0) × 8
                                   ├─> transcript mix
                                   └─> eight Gate output lookup terms
                                            at addresses 3 ... 10
```

The native verifier compares the supplied key bytes with the compiled key,
checks the embedded source binding, parses the public statement, reconstructs
these eight words, mixes their QM31 encodings into the transcript, and
requires the global lookup sum to vanish. The first Gate output term uses
address 3; each subsequent term increments that address. The package audit
checks the exact native Gate topology: address 3 has the conversion of `x`,
addresses 4–7 have the four ordered result conversions, and 8–10 are pinned
zero rows. It also checks the source, canonical optimizer identity, key,
preprocessed root, fixed-column roster, and exact Lean-parsed source bytes.

## What the Lean theorem says

`ControlGadgetStatementPins.lean` models the verifier encoding of a canonical
word as `(word mod 65536, floor(word/65536), 0, 0)` and proves that decoding
it recovers the original word. It proves the input conversion plus its Gate
add-zero row exposes exactly `x`. It combines the four output conversion and
pin equations with the earlier zero-test, select, and inverse AIR theorem.

For **any** satisfying rows and any eight canonical public words, if each
verifier-supplied output lookup event equals its addressed Gate cell, the
theorem concludes:

```text
claim[0] = x
claim[1+i] = result[i] = inverse(selected[i])   for i = 0,1,2,3
selected = if x == 0 then b else a
selected[i] * claim[1+i] = 1  in M31
```

The event-to-cell equality is an explicit premise. The Python audit checks
the exact source call path and one real native accepted proof. It cannot turn
native acceptance into authenticated, committed Gate cells. That step needs
global LogUp soundness and PCS/FRI authentication, which remain open for an
arbitrary accepted proof. The Python source guard recognizes exact call-site
fragments and reports SHA-256 hashes of those files; it is an executable
source identity check, not a formal semantics proof of the Zig verifier.

## Reproduce the focused audit

Given an already built sealed package, a proof, and its public-only JSON:

```sh
python3 scripts/compiler/control_public_statement_audit.py \
  "$PACKAGE" "$PROOF" "$STATEMENT" \
  --lean-checker formal/s31/.lake/build/bin/s31-pure-field-derivation-bytes-check
python3 -m unittest scripts.tests.test_control_public_statement_audit
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.ControlGadgetStatementPins)
```

For the example above, the native verifier accepted the original proof and
statement. Changing `result[0]` from `1` to `2`, or swapping the first two
result words, made it reject with `InvalidInteractionNonce`. A test also
swaps the captured output pin addresses and checks that topology admission
rejects the changed order. These are concrete controls, not a universal
cryptographic soundness result.
