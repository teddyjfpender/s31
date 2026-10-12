# Bounded source-to-statement projection check

The independent v2 record source check already reconstructs a relation and
ABI descriptor from source bytes. This audit step independently checks the
next boundary: the named public statement that becomes the verifier's eight
public words. Its implementation is
[`independent_statement_fragment_v2.py`](../../../src/frontends/s31/tests/acceptance/record_abi/independent_statement_fragment_v2.py),
outside the production compiler fingerprint.

## A complete small claim by hand

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
```

Take `x.left=2`, `x.right=3`, `y.right=7`. The arithmetic gives `p=14` and
`q=17`. The public statement contains four named leaves, in declaration
order: `x.left=2`, `x.right=3`, `result.left=17`, `result.right=3`. It does not
contain private `y`. The final result leaf and `x.right` refer to the same
relation wire, so they must agree. The relation's public input order is
`x.left, x.right`; the distinct public result wires are `q, x.right`. Thus
the eight-word verifier vector is:

```text
[2, 3, 17, 3, 0, 0, 0, 0]
```

The repeated `3` is intentional: a result alias occupies a public output
position even though the statement must give the alias the same value. A
malformed claim that gives `result.right=4` is rejected during statement
parsing. A well-formed changed claim such as `result.left=18` projects to a
different vector; the parser accepts its *shape*, and proof verification must
reject it against the old proof.

## Exact scope

The checker calls only the separate bounded source parser, then derives the
v2 boundary digest from its descriptor. It requires a canonical compact JSON
statement with one terminal newline, exact v2 envelope and digest, every
public path in declaration order, single canonical M31 words, consistent
aliases, and no more than eight projected public words. It rejects duplicate
JSON keys and non-JSON constants before interpreting the claim.

This accepts only the source parser's one-record, one-word-M31-per-field
grammar with up to four fields, two inputs, and eight arithmetic lets. It is
an independently implemented projection check, not an end-to-end compiler
correspondence proof or a native verifier proof. It neither evaluates the
source program nor authenticates a proof. The existing native proof acceptance
for this particular `Pair` program checks honest proof acceptance and an
ABI-valid changed claim's rejection separately.

## Reproduce

```sh
python3 -B -m unittest src/frontends/s31/tests/python/security/test_record_statement_fragment.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/record_source_statement_fragment_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/record_source_statement_fragment_v2.py --native
```

The first command compares 30 bounded source variants and their statements
with the production Python ABI decoder, then checks malformed byte and value
mutations. The second checks a byte-pinned three-accepted/six-rejected corpus.
The last command compares that same corpus with the production Zig statement
parser without running the prover.
