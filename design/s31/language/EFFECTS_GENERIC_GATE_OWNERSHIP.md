# Bounded effectful source to generic Gate ownership

This opt-in admission closes one compiler correspondence step for generic
Gate packages. `verify-effects-gate-lean` combines the existing Lean check of
the exact source, normalized relation, assignment, statement and source
semantics with an independent Python check of the **actual value-free native
Gate rows** exported by the externally pinned prover. The native verifier
reconstructs the verifier key before it checks the proof.

## Reviewed source shape

The admitted program has exactly four M31 lanes, one public input, zero to
three private inputs, one four-lane public result, 1–16 SSA arithmetic nodes,
and at most 16 `assert_eq` checks. Nodes use `+`, `-`, `.*`, `+ splat<4>(c)`
or `.* splat<4>(c)`. Constants 0 and 1 are excluded because current builder
peepholes can remove the corresponding Gate row. All node names are fresh,
commutative operands are in canonical order, and repeated expressions are
excluded. The result must select an arithmetic node. Unsupported programs
fail closed; ordinary S31 package build and native verification still work.

For example:

```s31
use std@1;
circuit affine_guard(public x: [m31; 4], private y: [m31; 4]) -> public [m31; 4] {
    let shifted = x + splat<4>(7_m31);
    let scaled = shifted .* splat<4>(9_m31);
    assert_eq(y, scaled);
    let out = y - x;
    out
}
```

For each of the four coordinates, the source requires `shifted = x + 7`,
`scaled = shifted · 9`, `y = scaled`, and `out = y - x` in M31. The compiler
packs each four-coordinate vector into one QM31 wire. The inspector exports
the packed address for each source node. The checker finds exactly one Gate
producer for each arithmetic node, checks its operation kind and ordered
operands, independently evaluates every interned constant through its Gate
derivation from the reserved `0`, `1` and `u` roots, and matches the one Eq
row's addresses to `y` and `scaled`. The
selected `out` wire is unpacked through four basis projections, converted to
four public M31 words, then copied to four fixed public output pins. The
public `x` pins are traced backwards through the packing tree to its four
scalar input wires. In total the ordered ABI is four `x` words followed by
four `out` words.

The generic Gate AIR groups binary rows by operation kind. Its dynamic fixed
columns contain operation flags, input/output addresses and multiplicities;
Eq and M31-to-u32 columns hold assertion and conversion addresses. The
checker compares all exported row addresses and flags to these columns,
hashes each of the 13 dynamic columns as little-endian u32 words, and
compares them with the source-bound 45-column component roster sealed by the
verifier key. It checks exact source spans, assertion spans, public binding
spans, ABI order, circuit identity and fixed root identity. The remaining
large fixed lookup tables are held by the native verifier's own `check-key`
reconstruction and its fixed PCS commitment; they are not copied into this
small diagnostic export. The `qm31_ops_mults` and
`m31_to_u32_multiplicity` columns are checked against the native roster hashes;
their multiplicities are **not** independently derived from the source. The
checker rules out extra producer rows for source nodes, scalar inputs, pack
and extraction intermediates, conversions and public pins. Producer ownership
of unrelated finalization wires is
left to the pinned native compiler and Gate AIR verifier.

## Trust and limits

The inspector and verifier executable hashes and source/key hashes must come
from outside the package. The command copies and pins the package and proof
inputs before running either executable. Its topology output is diagnostic,
not itself a proof opening. The check establishes source-to-emitted-row
**ownership conditional on the pinned native compiler, Gate AIR semantics,
fixed-root and PCS/FRI soundness**. It is not a Lean theorem connecting the
native builder to the full Gate AIR, and does not prove witness values from
fixed addresses alone. The native proof binds a public statement, but it
does not identify the supplied private assignment as the proof's hidden
witness. Verifier-side Lean sees that full private assignment; this audit
path does not preserve its privacy.

The current `linear-ssa-m31-effects-v1` source parser also has its own
bounded grammar and rejects records, arrays, control flow, loops, chips,
hashes and wider integers. General compiler correspondence still needs those
features, a formal generic Gate row relation, and a proved native PCS/FRI
link. This admission does not claim them.
