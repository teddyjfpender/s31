# Nested public record ABI acceptance

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
