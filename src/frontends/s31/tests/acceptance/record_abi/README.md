# Nested public record ABI acceptance

## Public byte input range under direct-gate

[`record_public_u8.s31`](../../../examples/arithmetic/record_public_u8.s31)
tags one raw u16 relation word as a public `u8` in ABI v2. Direct Gate
reconstructs it from eight Boolean bits using arithmetic operation gates.
Only a public input alias can appear as a `u8` result. The native statement
and flat witness paths reject words above 255; chip and mixed admission reject
the public byte source shape.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py --native
zig build --build-file src/frontends/s31/build.zig test-bounded-call-source -Doptimize=ReleaseFast -j1
```

The native control proves 0 and 255, rejects changed in-range and out-of-range
statements, rejects a flat witness of 256 against a valid claim, and checks a
derived output and wrong narrow result tag in the production descriptor parser.
The Lean `RecordAbiV2`, `RecordLayoutValidationV2`, and
`RecordDescriptorValidationV2` modules model the eight-bit reconstruction
bound and private-leaf exclusion; they do not establish a full physical AIR
correspondence theorem for this compiler path.

## Public u16 input range under direct-gate

[`record_public_u16.s31`](../../../examples/arithmetic/record_public_u16.s31)
has a public `u16[1]` field, computes its M31 square plus a public salt, and
returns the original u16 input wire as a named result field. The direct-gate
compiler constrains the input with 16 Boolean producer gates and arithmetic
reconstruction; it does not use the fixed u16 lookup table. The v2 descriptor
admits only public u16 input leaves and u16 result leaves that alias one of
those input wires. Private u16 leaves and derived u16 result wires are
rejected. The direct-chip package gate and the source-only
direct-mixed-general admission both reject the u16 source shape.

Run the fast text/descriptor/oracle controls, then the focused native proof
control when compiler and prover CPU is available:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u16_direct_gate_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u16_direct_gate_v2.py --native
zig build --build-file src/frontends/s31/build.zig test-bounded-call-source -Doptimize=ReleaseFast -j1
```

The native gate verifies honest claims at `0` and `65535`, rejects a
well-formed changed claim against the old proof, rejects `65536` and
`p−1` in both statement decoders, rejects an out-of-range flat witness,
and tests a derived u16 result mutation through the production Zig
descriptor parser. The mixed admission fixture includes a valid cast from
four public u16 limbs to M31 before one chip call; the source-only admission
still rejects it. The Lean
[`RecordAbiV2.lean`](../../../../../../formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean)
model proves the 16-bit reconstruction bound and public tag bound, while
[`RecordDescriptorValidationV2.lean`](../../../../../../formal/s31/S31/Gadgets/Functional/RecordDescriptorValidationV2.lean)
excludes private u16 leaves. These are model-level statements; the native
proof acceptance gate supplies executable coverage for this fixture.

## Public u32 record under direct-gate

[`record_public_u32.s31`](../../../examples/arithmetic/record_public_u32.s31)
uses one scalar `u32` record input and an alias-only `u32` result. Its two
little-endian `u16` limbs each get a 16-bit arithmetic range proof. The
verifier sees four ordered words because both named paths refer to the same
two-limb wire. The ABI digest distinguishes this `u32` from `[u16; 2]`.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u32_direct_gate_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u32_direct_gate_v2.py --native
python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u32_adversarial_v2.py --native
```

The native check accepts zero, maximum, and mixed-limb proofs, rejects a
changed proof claim, overlarge low/high limbs at statement and flat-witness
admission, alias mismatch, derived/private/malformed descriptor shapes, and
the wrong nominal ABI digest. A coherently retyped `[u16; 2]` record has the
same AIR/preprocessing geometry for this fixture but a distinct key digest.
The capability is public, direct-gate, and alias-only; it does not admit
private `u32` leaves or arbitrary derived `u32` result wires.

## Eight-word text, statement, native, and Lean correspondence

[`mixed_eight_alias_bit.s31`](mixed_eight_alias_bit.s31) is a small, actual
source program with a public `bit`, a two-word public salt, a four-word
private input, and two result fields that refer to the same four-word wire.
Its result `flag` also refers to the public input bit. The text compiler
therefore emits three relation inputs, two distinct public result wires, and
exactly eight projected public words: one bit, two salt words, the repeated
bit, and four result words. The ABI describes nine logical result leaf words;
the last four repeat an existing result wire and do not add public proof words.

[`mixed_eight_lean_correspondence_v2.py`](mixed_eight_lean_correspondence_v2.py)
pins the exact compiled relation, descriptor, and typed-statement JSON bytes
beside the source. It compares the production Python statement codec with the
independent public-word projection, then sends the **same unmodified source
and statement bytes** through the native Zig statement parser. Its eight-case
corpus accepts the honest evaluated assignment and a consistently changed bit;
it rejects a split input/result bit alias, a split result alias at the third
lane, an out-of-range bit, a swapped equal-width result field, a leaked private
root claim, and a descriptor reorder with a stale statement digest. The split
bit alias is a distinct adversarial case from the older native record corpus.

The generated
[`GeneratedMixedEightV2.lean`](../../../../../../formal/s31/S31/Gadgets/Records/GeneratedMixedEightV2.lean)
kernel-checks the small named layouts, paths, widths, private erasure,
declaration-order wire lists, accepted eight-word projection, and the bit and
result alias rejection examples. Full JSON is kept in byte-pinned artifacts;
Lean does **not** parse those JSON bytes or kernel-check the SHA-256 comments.
The generator and native parser provide a finite byte-level differential,
not a general compiler refinement theorem. The separate
[`mixed_eight_proof_v2.py`](mixed_eight_proof_v2.py) sends these **same pinned
source and statement bytes** through the `direct-mixed-general` native prover
and verifier. It checks the exact eight public words, a changed but ABI-valid
public bit and its result alias, a changed unused public salt, and a changed
chip result with its repeated alias. The original proof must fail for each
changed claim after ABI parsing. Split aliases, a non-bit claim, and a renamed
record field must fail in the ABI parser; a changed private input with the
old output must fail before proving. The generated full-trace auditor must
accept the honest proof, typed statement, and private assignment, reporting
512 circuit rows and 16 rows each for the chip and bridge, and must reject
the changed private assignment and changed v2 statement. A separate negative
source gate changes both flag aliases to `m31` and uses a self-consistent value
`2`: the generic ABI accepts its typed statement, while this mixed proof
profile rejects the source because the alias must be a `bit`. This is a one-call
proof admission for this shape, not a general compiler refinement theorem.
The existing admitted
N=1/N=8 record proof smoke is documented in the
[mixed boundary acceptance README](../mixed_boundary/README.md).

Run from the repository root, or pass the same absolute paths from elsewhere:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/mixed_eight_lean_correspondence_v2.py --native
python3 -B src/frontends/s31/tests/acceptance/record_abi/mixed_eight_proof_v2.py
cd formal/s31 && LEAN_NUM_THREADS=1 lake env lean S31/Gadgets/Records/GeneratedMixedEightV2.lean
```

At the current fixture, the native corpus reports **2 accepted / 6 rejected**.
The source, descriptor, and statement SHA-256 values are printed by the
Python command and recorded in the generated Lean file. Pass `--write` only
when intentionally updating the pinned source and its derived artifacts.

[`mixed_eight_statement_edges_v2.py`](mixed_eight_statement_edges_v2.py)
uses that same byte-pinned source and statement for a focused public-claim
parser matrix. It accepts the honest claim and a consistent boundary claim
with bit `0` and M31 words `0` and `p−1`. Its 21 rejected cases cover both
bit positions, the M31 range on the salt and result, word-vector length,
both alias groups, named paths, private-leaf insertion, digest/version, and
canonical JSON bytes (including the required single final newline). The
accepted boundary claim tests statement parsing only; it is not asserted to
satisfy the circuit or to verify against the honest proof.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/mixed_eight_statement_edges_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/mixed_eight_statement_edges_v2.py --native
```

## Whole-descriptor shape differential

[`whole_descriptor_shape_v2.py`](whole_descriptor_shape_v2.py) compares an
independent implementation of the whole-descriptor *shape* check in
[`RecordDescriptorValidationV2.lean`](../../../../../../formal/s31/S31/Gadgets/Functional/RecordDescriptorValidationV2.lean)
with the Python ABI validator and production Zig `relation.parseProgram` →
`record_abi.validate` path. It compiles 13 varied record programs and the
hand-written nested-alias program. Every one of those 14 source descriptors
must pass all three checks. It then mutates the nested descriptor to cover
nominal-name disagreement, a private bit leaf, duplicate or colliding root
names, a wrong result name, a tuple root, depth 33, empty record/tuple,
duplicate sibling fields, and invalid leaf widths. Zig must reject each
specifically as `InvalidRecordAbi`; a JSON or relation-layer rejection cannot
pass the harness.

One synthetic relation exercises the **global** leaf bound that the compiler's
small public-word examples do not reach: 1,023 private one-leaf inputs plus a
one-leaf result total exactly 1,024 and pass; adding one private input totals
1,025 and is rejected. The synthetic relation is constructed from a compiled
single-input source, then extends both its relation input list and record
descriptor consistently. It is an ABI-validator test, not a source-compiler
acceptance claim. All corpus bytes are pinned by SHA-256
`a1f2fef313d2e3f81f69a854b0978a07065f098c71ba0adc4e711e1c637c827c`.

The optional `--lean` mode generates concrete `checkDescriptor` propositions
for the 30 small cases and checks each with `by decide` in Lean. The two
synthetic 1,024/1,025-leaf cases stay in the Python/Zig differential; Lean's
general `overBudget_rejected` theorem covers every descriptor above 1,024,
while this fixture does not create a giant Lean term for the exact-boundary
case.

Three explicit gap controls keep the claim precise. A malformed nominal
identifier (`Bad!`), a wrong declared leaf path, and a wrong wire reference
retain valid *type-tree shape* and are admitted by the independent shape
model. The Python and Zig full validators reject them. Lean's descriptor
checker starts from an already parsed named tree; this differential is a
finite agreement check, not a proof that Zig parsing refines Lean for all
inputs. It does not compare ABI digests, statements, proofs, or authenticated
AIR openings.

Run the fast source/model/Python check or include the native parser:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/whole_descriptor_shape_v2.py --static
python3 -B src/frontends/s31/tests/acceptance/record_abi/whole_descriptor_shape_v2.py --lean
```

The current corpus has **15 native accepted / 17 `InvalidRecordAbi` rejected**
cases: 14 compiled positives, one synthetic bound positive, 14 shape
negatives, and three intentional refinement gaps. The Zig executable is
[`native_descriptor_corpus.zig`](native_descriptor_corpus.zig), wired to
`zig build record-descriptor-parser-corpus` in the frontend build.

## Identifier bytes: native and Lean differential

[`lexical_name_differential_v2.py`](lexical_name_differential_v2.py) compiles a
small record circuit, then changes one input-root, nominal-record, or field
name in its public descriptor. It updates the corresponding leaf path, so a
valid renamed root or field remains a valid descriptor. Each position gets
the same eight byte cases: empty, one ASCII letter, exactly 128 bytes, 129
bytes, a leading digit, a hyphen, non-ASCII UTF-8, and an underscore with
letters and digits. The unmodified compiled descriptor is a ninth control.

The script generates 25 concrete Lean descriptors and kernel-checks both
`checkDescriptor = true` and the expected `checkLexicalDescriptor` result for
each. Thus every negative retains a valid *shape* and fails the lexical rule.
The same 25 source/descriptor bytes go through the production Zig
`relation.parseProgram` → `record_abi.validate` path using the existing
[`native_descriptor_corpus.zig`](native_descriptor_corpus.zig) runner. It
requires exactly **10 accepted** and **15 rejected specifically as
`InvalidRecordAbi`**; an unrelated parse or relation error fails the run.
Corpus SHA-256:
`04281617e87db8ea06476f831688c869de2904724c9df9bd43d78e8db32a7ecf`.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/lexical_name_differential_v2.py
```

This is a finite parser differential. The Lean checker starts from an already
parsed named tree; the fixture does not prove a general JSON-to-Lean
refinement or validate an authenticated proof.

## Canonical descriptor digest and final public words

[`descriptor_digest_correspondence_v2.py`](descriptor_digest_correspondence_v2.py)
checks the complete executable ABI chain up to proof verification. It uses the
production Zig relation parser, `record_abi.digest` (native canonical JSON and
SHA-256), and `record_abi.claimedWords` (ordered named claims and the final
eight-word projection). The Python side computes the digest from the specified
domain prefix and canonical descriptor bytes, checks the independent
declaration-order/alias projection, and pins every native input in corpus
SHA-256
`cb863031d541c594a24feb41aab146344759b3239049e475dce4bcf0be256af9`.

The **23 accepted** cases include 14 compiled programs, the same nested
program serialized with reversed JSON key order and with pretty spacing, and
seven explicitly marked *synthetic* descriptor mutations. The latter change
root, nominal, or field names; result field order; result wire references; and
an M31 leaf's ABI type to `bit`. All seven change the native/Python descriptor
digest. Type-code changes are checked separately from root/path/wire changes.
Five malformed descriptors must fail at native `InvalidRecordAbi`. Two negative
controls corrupt the corpus's expected digest or expected public words and
require the native oracle to detect each corruption.

For example, renaming the private `mask` root changes the descriptor digest
from `15ca13f4…` to `cc0c730a…`, even though the public projection remains
`[494, 507, 520, 533, 494, 0, 0, 0]`. Rebinding the result's second leaf
from the first to the second public input changes the projected fifth word
from `494` to `507`; the matching relation output reference is changed in
that synthetic case. Recoding the first public M31 leaf as `bit` changes the
digest and constrains its accepted claim to `0` or `1`.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/descriptor_digest_correspondence_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/descriptor_digest_correspondence_v2.py --native
```

The seven descriptor mutations are valid parser states, not claims that the
text compiler emits those exact programs. This finite correspondence does not
prove a general JSON parser or canonical serializer refinement, relation-wire
mapping for every source program, or that native proof acceptance implies the
Lean descriptor and claim premises. The native proof corpus below checks
representative verified proofs separately.

[`text_lowering_correspondence_v2.py`](text_lowering_correspondence_v2.py)
starts one step earlier, at actual `.s31` text. Its handwritten baseline is:

```s31
struct Inner { a: [m31; 1], b: [m31; 1] }
struct Request { inner: Inner, flag: bit }
struct Secret { delta: [m31; 1] }
struct Result { first: [m31; 1], second: [m31; 1] }
circuit map(public req: Request, private secret: Secret) -> public Result {
    let x = req.inner.a + secret.delta;
    Result { first: x, second: req.inner.b }
}
```

The test compiles **12 text variants** and compares each normalized relation
with handwritten ordered path, kind, width, visibility, and relation-wire
expectations. The variants rename or reorder fields, add tuple nesting, widen
an M31 leaf to two words, change the output alias, reorder or nest result
fields, expose the formerly private root, rename either root, and change a
`bit` to an M31 leaf. Each compiled descriptor then reaches the native digest
and eight-word statement projection. Six corruptions of *each* normalized
descriptor—leaf order, width, visibility, path, result wire, and result kind—
must fail specifically at `InvalidRecordAbi`: **12 accepted / 72 rejected**.
The text frontend must also reject a private record containing the `bit` leaf.

With one fixed value seed, the baseline projects to
`[494, 507, 1, 533, 507, 0, 0, 0]`. Reordering the result fields projects to
`[494, 507, 1, 507, 533, 0, 0, 0]`, because output slots follow declaration
order. Making `secret` public adds its input before the outputs:
`[494, 507, 1, 533, 546, 507, 0, 0]`. Widening the first input and first
result leaves to two words produces seven occupied slots:
`[494, 495, 507, 1, 533, 534, 507, 0]`. Source text SHA-256 is
`c43501bb95e8892d23aa17a428fd4b8e8744b9608e59cc31388f9f966a530218`;
the native input corpus SHA-256 is
`b43e2f3003d77fbfe90c220d0de63270952e43e4f276e25ab9da072d551bc04e`.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/text_lowering_correspondence_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/text_lowering_correspondence_v2.py --native
```

This is a finite text compiler/native parser differential. The statement
values are ABI fixtures; the audit does not prove that those values satisfy
each circuit, nor does it produce or verify STARK proofs. General source
lowering correspondence and authenticated proof-to-Lean premises remain open.

[`nested_alias_v2.py`](nested_alias_v2.py) covers a versioned public record
whose input contains a tuple and a nested record, whose result contains a
tuple and nested records, and whose private input is another record. The
source computes three M31 additions:

```s31
let y = req.pair.0 + req.pair.1 + req.extra.seed + mask.delta;
Result { nested: (Inner { seed: y }, req.pair.0),
         copy: Inner { seed: y } }
```

At `req.pair=([2],[3])`, `req.extra.seed=[5]`, and private
`mask.delta=[7]`, `y=17`. The canonical public statement has **six named
leaves**: three input leaves and three result leaves. The result's last leaf
aliases `y`; its middle leaf aliases the first public input. The native
proof word vector is `[2, 3, 5, 17, 2, 0, 0, 0]`: three public input slots,
two output slots (one reuses an input wire), and three zero pads. The private mask is
absent from the public statement.

Run the fast source, Python codec, and malformed-input checks without Zig:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_alias_v2.py --static
```

Run the native acceptance from the repository root:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_alias_v2.py
```

The native run builds one direct-gate package and verifies two genuine proofs,
including a modular-wraparound assignment. It requires the statement built
from flat prover wires to equal the statement built from a typed named claim,
byte for byte, and requires Zig to accept those bytes against the sealed key.
It also changes each bound public word in four **well-formed**, alias-consistent
statements. Python accepts their ABI shape, while Zig must reject the original
proof. This checks proof binding separately from parser rejection.
It then requires clean native rejection of 16 changed statements: both alias
directions, tuple index, field name and order, private or missing leaves,
range/type errors, wrong ABI digest, deep path, duplicate object keys,
noncanonical JSON, missing newline, and oversized input. The source-side
typed adapter must reject nine malformed assignments, including nested
duplicates, deep values, wrong tuple arity, private visibility changes, and
both alias conflicts. These controls test this bounded source and verifier
path; they do not prove all record layouts or underlying STARK soundness.

## Deterministic Python/native differential corpus

[`differential_mutations_v2.py`](differential_mutations_v2.py) starts with the
same nested source and a single genuine native proof. It generates a fixed
corpus of **152 malformed statements** and **16 well-formed changed public
claims**. The corpus SHA-256 is
`0c2d0382b990b2caaba2c2995c112f8bddfaaf4f6a2cf5887d87a6d441d29933`.
Each of the six public leaves is mutated independently for integer range,
JSON type and word-vector shape. Every root, field and tuple-index path
coordinate is changed. The corpus also covers split aliases, envelope keys,
duplicate JSON keys, noncanonical bytes, truncated JSON, and the statement
size limit. For valid changed claims, all occurrences of an aliased wire
change together. The Python ABI parser must accept those claims and return
different public proof words; the native verifier must reject the original
proof against them after parsing. The native test records named error classes
and requires malformed cases to fail in the JSON/ABI parser layer and changed
claims to fail in the proof layer.

With the current verifier, all 16 valid changed claims fail at the proof
transcript's interaction-nonce check (`InvalidInteractionNonce`). This is
evidence that these changed statements reach proof verification after ABI
parsing and that the held proof is bound to its original public words. It does
not by itself exercise every later FRI or quotient check.

Run the fast source and Python parser checks:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/differential_mutations_v2.py --static
```

Run the Python/native differential acceptance:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/differential_mutations_v2.py
```

The native run builds one direct-gate package, produces one proof, then invokes
the generated verifier on all 168 mutations. It tests parser agreement and
public-claim proof binding for this one sealed record layout. It is a finite
adversarial corpus, not a proof that the Python and Zig parsers agree on every
JSON input or every valid record type.

## Source to Lean/native statement fixture

[`lean_native_bridge_v2.py`](lean_native_bridge_v2.py) checks the same nested
program against a concrete contract in
[`RecordAbiV2.lean`](../../../../../../formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean).
It independently walks the compiled type trees in declaration order, checks
every six public claim paths and alias, then projects relation public inputs
and distinct result wires to `[2, 3, 5, 17, 2, 0, 0, 0]`. The script requires
the exact generated Lean path and word declarations to match the compiled
source and canonical statement. Lean then proves its own nominal tree walk,
six claimed words, deduplicated proof words, and an inconsistent result alias
rejection for this fixture. A valid, consistently changed input/output alias
is accepted as a *different* five-word public claim.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/lean_native_bridge_v2.py
cd formal/s31 && lake env lean S31/Gadgets/Functional/RecordAbiV2.lean
```

The Python check has eight targeted negative controls for path order, tuple
index type, split aliases, private leaf leakage, field range and result wire
order. `--emit` prints the exact source-derived Lean contract when updating the
fixture. This check ties one admitted source program to the Lean model and to
the statement words already exercised by the native acceptance. It does not
prove a general Python/Zig parser refinement, native proof soundness, or
confidentiality of private inputs.

## General statement checker and generated source corpus

[`RecordStatementV2.lean`](../../../../../../formal/s31/S31/Gadgets/Functional/RecordStatementV2.lean)
proves an exact admission equivalence for arbitrary validated leaf descriptors:
the claim list must match path, width, and M31/bit range in order, repeated
wire references must agree, and the public input/result wire projection must
fit the eight-word native slot budget. It also proves that first-wire lookup
returns every aliased claim's payload after the consistency check.

[`general_statement_refinement_v2.py`](general_statement_refinement_v2.py)
compiles 13 different source programs: wide leaves, nested tuples, public
bits, private roots, and repeated input/result or result/result wires. Its
independent projection agrees with the Python ABI decoder. The generated
[`Lean corpus`](../../../../../../formal/s31/S31/Gadgets/Functional/GeneratedRecordStatementCorpusV2.lean)
checks 13 accepted claims, 13 consistent changed claims with changed public
words, and 65 malformed rejections. The source corpus SHA-256 is
`a5e2883c146957858828404f47afec1251a4c8b99929c0ed310bb56a04a2305c`.

With `--native`, the script sends those same 91 source-derived cases to the
production Zig `relation.parseProgram` and `record_abi.claimedWords` paths in
one small executable. Zig must return the independently projected eight words
for all 26 well-formed statements, including each consistently changed claim,
and must reject all 65 malformed claims specifically as
`InvalidRecordStatement`. The executable is reusable for other JSON case
corpora using its documented schema in
[`native_parser_corpus.zig`](native_parser_corpus.zig). This parser check does
not generate or verify a proof; an ABI-valid changed claim is expected to be
admitted by this parser. The exact 91-case native input SHA-256 is
`1c653b515475bc8e90a4ccff13faf2fe6373d74d31f2a0b9ab6679c0eab270c8`.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py --native
cd formal/s31
lake build S31.Gadgets.Functional.RecordStatementV2
lake env lean S31/Gadgets/Functional/GeneratedRecordStatementCorpusV2.lean
```

The [hand-written bit and alias example](../../../../../../formal/s31/S31/Gadgets/Functional/RecordStatementV2.md)
shows the exact named claims and padded proof words. The theorem starts after
descriptor validation and JSON/digest checks. This corpus compares the source
compiler, Python decoder, independent projection, Lean model, and, with
`--native`, Zig statement parser. It does not prove native STARK verification
for all 13 shapes.

## Text, record claims, and relation values on the same assignment

[`nested_relation_word_correspondence_v2.py`](nested_relation_word_correspondence_v2.py)
uses the 12 source-text record variants above with concrete assignments. Its
small value oracle computes `x = a + delta` by hand, then writes each named
input and result wire in declaration order. The fixtures exercise nested
records and tuples, width-two leaves, reordered fields, public and private
inputs, result aliases, and a public bit. Their exact corpus bytes are pinned
by SHA-256
`37ca9286ff4e6fb5b43bc3ee6fe8f3512bea594ed9e90ae239e00f97716afdde`.

With `--native`, the reusable Zig statement runner parses each compiled
relation and its canonical named claim, then requires three production paths
to equal the handwritten eight-word vector: `record_abi.claimedWords`,
`relation.claimedWords` on the flat assignment, and `relation.evaluate` on
that assignment. All **12 cases pass**. Two controls corrupt the expected
public word or a private arithmetic operand while leaving the original
statement fixed; the native runner must reject both. This closes a bounded
text-to-evaluated-word gap left by the synthetic descriptor corpus. It does
not establish a universal compiler theorem or authenticate any proof row.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_relation_word_correspondence_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_relation_word_correspondence_v2.py --native
```

## Representative proof binding across record layouts

[`native_proof_corpus_v2.py`](native_proof_corpus_v2.py) takes four programs
directly from the 13-layout source corpus and runs their generated native
provers and verifiers. It first checks that the source corpus still renders
the exact checked-in Lean fixture:

| Layout | Eight public proof words | Feature exercised |
| --- | --- | --- |
| `pair_4` | `[2, 3, 5, 7, 2, 3, 5, 7]` | Four-lane input repeated in two named result fields |
| `tuple_2_2` | `[11, 13, 17, 19, 11, 13, 17, 19]` | Nested tuple paths and two result aliases |
| `bit_3` | `[1, 23, 29, 31, 23, 29, 31, 0]` | Public Boolean input alongside three M31 lanes |
| `private_2` | `[2147483646, 5, 37, 41, 1, 12, 0, 0]` | Two private lanes, modular wraparound, repeated result alias |

Each package must seal the exact compiled source and record ABI digest. For
each proof, its canonical statement bytes must agree with the assignment
encoder, the Python decoder, and the independent source-derived projection.
The separate value oracle checks the outputs, and the generated verifier
accepts the proof. The harness then changes a public claim consistently at
every aliased leaf. Both statement decoders must accept that new claim and
project it to different proof words; the verifier must reject the *original*
proof after parsing, at proof binding. This avoids counting a malformed alias
as evidence of proof binding. In the current verifier, all four changed claims
fail at `InvalidInteractionNonce`; that is transcript binding evidence, not a
check of every later PCS or FRI stage.

The flat proof word vector keeps the declared public input slots followed by
the distinct result-wire slots. An output that aliases an input still occupies
its own result slot; only repeated named result leaves share an output slot.

Run one layout for a short edit loop, or all four:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/native_proof_corpus_v2.py --case pair_4
python3 -B src/frontends/s31/tests/acceptance/record_abi/native_proof_corpus_v2.py
```

The four cases test a bounded subset of the 13 source layouts. They do not
establish full compiler correspondence or the soundness of the underlying
STARK verifier.

## Nested public u8/u16 source and proof seal

[`nested_narrow_seal_v2.py`](nested_narrow_seal_v2.py) compiles two valid
source programs whose only semantic layout change is the named nested input
field `digit` versus `value`. Both lower to the same three-input, four-node
flat arithmetic relation and the same six live public proof words followed
by two padding zeros. The source
includes a public `u8`, public `u16`, M31 salt, and a repeated `u16` result
alias inside records and a tuple. It pins the source and ABI digests and
checks the paths, tags, word projection, and modular arithmetic by hand.

With `--native`, both generated packages prove and verify the honest boundary
values. Each proof is then presented to the *other* generated verifier using
that verifier's own valid key and statement. Both cross-replays must fail
inside proof verification, after named-statement validation. A forged ABI
digest in the original key must fail key validation. Separate native parser
controls reject wrong version, path, leaf order, and out-of-range `u8`/`u16`
claims. See the [short design note](../../../../../../design/s31/language/RECORD_NESTED_NARROW_SEAL_V2.md)
for the exact source and eight-word vector.

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_narrow_seal_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_narrow_seal_v2.py --native
```

The valid field rename also changes exact source bytes; this proves the
combined source/ABI seal on these two packages, not an isolated ABI-only
transcript field or universal compiler correspondence.

## Independent bounded record source check

[`record_source_fragment_v2.py`](record_source_fragment_v2.py) checks one
hand-written program with a public and a private `Pair` input, two arithmetic
lets, a declaration-ordered result whose constructor lists fields in reverse
order, and a result alias of a public input wire. The independent parser
reconstructs the complete version-2 relation and ABI digest from the text.
The script builds an actual direct-gate package, checks its emitted source,
relation, ABI artifact, and manifest, and verifies a native proof for public
words `[2, 3, 17, 3, 0, 0, 0, 0]`. A different but ABI-valid `result.left`
claim must fail inside proof verification. Focused unit tests re-seal changed
relation and ABI artifacts and require the independent checker to reject them.

```sh
python3 -B -m unittest src/frontends/s31/tests/python/security/test_record_source_fragment.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/record_source_fragment_v2.py
```

The checker reports only `source-to-relation-only`. It does not certify native
gate extraction, AIR, or the proof system. Its accepted grammar and exact
checks are in the [design note](../../../../../../design/s31/language/RECORD_SOURCE_RELATION_FRAGMENT_V2.md).

## Independent bounded source-to-statement projection

[`independent_statement_fragment_v2.py`](independent_statement_fragment_v2.py)
extends that exact M31 record grammar from source bytes through canonical v2
statement bytes to the eight proof words. It derives the ABI digest, required
public leaf paths, alias identities, and final distinct-wire order from the
independent source parser. It does not import the production ABI codec or
compiler. For the `Pair` program above, the named claim has `x.left=2`,
`x.right=3`, `result.left=17`, and `result.right=3`. The last leaf aliases
`x.right`; the projected proof words are `[2, 3, 17, 3, 0, 0, 0, 0]`.

The fast unit gate compares 30 bounded source/layout/alias programs with the
production Python statement decoder. It also rejects changed paths, split
aliases, M31 overflow, wrong scalar types, missing leaves, duplicate keys,
and noncanonical bytes. The optional native gate sends the same handwritten
three accepted and six rejected claims through Zig's statement parser, without
creating proofs:

```sh
python3 -B -m unittest src/frontends/s31/tests/python/security/test_record_statement_fragment.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/record_source_statement_fragment_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/record_source_statement_fragment_v2.py --native
```

This adds the `source-to-statement-projection-only` audit capability. It checks
the public claim that a verifier would receive; it does not establish that a
proof is valid, that the source computation produced those values, or that all
record types are supported. See the [exact contract](../../../../../../design/s31/language/RECORD_SOURCE_STATEMENT_FRAGMENT_V2.md).
