# Nested public record ABI acceptance

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
