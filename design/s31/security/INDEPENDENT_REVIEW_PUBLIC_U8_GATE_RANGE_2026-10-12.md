# Independent review: public `u8` record input in direct Gate

**Reviewed implementation:** `6feb92b04301cf35e612911e482db11acc0994f9`.
I found no concrete soundness defect in the scoped public `u8` input and
input-alias result path. The conclusion is conditional on the Gate lookup and
polynomial-commitment assumptions below; it does not extend to arbitrary
derived bytes or other proof profiles.

## Byte-level scope

| Inspected file | SHA-256 |
| --- | --- |
| `src/frontends/s31/language/record_abi.zig` | `b07d0680d96baeaf6c024be204cc58977eabbf8106b069eac1c3945c19bd2d19` |
| `src/frontends/s31/language/relation_compiler.zig` | `2b46f1f4f3631a455095260827e416456871c030a783ed1f6df2ee2835b78d54` |
| `src/frontends/s31/language/gadgets/integer_bits.zig` | `18e880ba7a96f958810d041939e35ba9fa2fc2d0226f98e5a574158e696e853d` |
| `src/frontends/s31/python/abi/binding_v2.py` | `e144a495a54abf2fbbbd5727c696efa2ee97d1670b10960d5bb27a73dbc5d618` |
| `src/frontends/s31/python/package/context.py` | `558a2a17a94963b2643bcc5764875d3698cb76920df9d11571dffef9f308d992` |
| `src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py` | `d89505fdb044bf120eda013934b6d5a6353886b581ccd5643f43282a2a6a9c54` |
| `formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean` | `6c687f78cf601f759bf61461ca42e5d04b2f933481fcc06786b820e02f46caeb` |

The pinned `deps/stwo-zig` Gate AIR, fixed-column, and witness files match the
SHA-256 pins in the earlier [independent `u16` review](INDEPENDENT_REVIEW_PUBLIC_U16_GATE_RANGE_2026-10-12.md).
The edits to `records.md` and the `RecordAbiV2.lean` introductory comment in
this review only update wording for `u8`; they change no theorem or code
semantics.

## Constraint and binding argument

The text frontend lowers `record_public_u8.s31` to a version-2 relation with
one public `u16[1]` input wire for `req.byte`; its ABI descriptor tags that
same wire `u8`. Both Python `validate_binding` and native `record_abi.validate`
bind each descriptor leaf's wire, raw kind, length, visibility, and named path
to the relation. Native `parseProgram` validates the descriptor before proof
or verification. The canonical descriptor digest is in the sealed key and
the native verifier rebuilds the compiled circuit from its embedded source.
Changing only the descriptor from `u8` to `u16` therefore changes key identity
and does not retag an existing byte proof.

For each such input word `w`, direct compilation chooses width eight, guesses
Boolean witnesses `b_0,...,b_7`, and emits `mulInto(b_i,b_i,b_i)` for every
bit. It reconstructs `r = Σ 2^i b_i` and emits a self-loop addition forcing
`r-w=0`. Under the fixed Gate opcodes and sound address/value lookup, these
rows impose `b_i²=b_i` and `w=r` in M31. Each bit is 0 or 1, so
`0 ≤ r ≤ 255 < 2³¹−1`; modular wrap cannot provide another canonical value.
This uses eight arithmetic Boolean gates and reconstruction arithmetic per
word, without the fixed 16-bit lookup table. The public input is also included
in the circuit's eight-word output binding, and a `u8` result must alias a
public input leaf with the same `u8` tag and raw wire.

Python and native typed-statement decoders reject a `u8` claim outside
`[0,255]`. The native flat-assignment evaluator checks tagged public inputs
and aliased outputs before proving; the ordinary raw `u16` range alone would
be insufficient. The source-only mixed admission requires a public *bit*
alias, and direct-chip packaging requires a single M31 four-lane repeat, so
neither admits this public byte source. Private `u8` record inputs and derived
`u8` record outputs fail descriptor validation.

## Evidence and remaining obligations

I independently ran the static and native acceptance controls and the
record-binding unit tests at the inspected bytes:

```text
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py
  accepted 0 and 255; rejected 256 and 2147483646 in the typed path
python3 -B -m unittest src/frontends/s31/tests/python/test_record_binding_v2.py -q
  19 tests passed
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py --native
  exit 0; honest boundary values [0,255], rejected byte values [256,2147483646]
```

The static control also checks source lowering, descriptor alias rejection,
direct-chip package rejection, public-word order, and independent M31
arithmetic for both boundary values. The native control built a fresh
descriptor-parser corpus and direct-Gate package, proved and verified both
boundary values, rejected a changed but in-range public claim at the proof
layer, rejected two out-of-range typed statements at the native parser, and
rejected a flat witness of 256 before proof generation. It also checked five
native descriptor cases, including derived-result and mismatched-tag
rejection. These are finite executable controls, not a general accepted-proof
soundness theorem.

The Lean `RecordAbiV2` theorem proves an eight-Boolean-bit reconstruction is
less than 256, and the descriptor modules model leaf width and private-leaf
exclusion. Those theorems do not establish production compiler-to-Gate AIR
correspondence, accepted-proof-to-decoded-trace extraction, or cryptographic
soundness. The argument assumes the fixed Gate columns and public output
addresses bind the compiled topology, Gate LogUp soundness for reused wire
addresses, and PCS/FRI commitment, low-degree, and transcript soundness. It
also assumes that externally accepted proofs always use the generated native
verifier and its sealed key.
