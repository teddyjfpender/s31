# Bounded direct-gate correspondence certificate

`correspondence-certificate.json` is a package-admission check for a narrow
source language. It does not certify arbitrary S31 or change the installed
native verifier's accepted proof language.

## Accepted source

The checker independently tokenizes the exact UTF-8 `.s31` bytes. It accepts
one public `[m31; 4]` input and one public `[m31; 4]` output, 1–16 fresh
`let` bindings of `earlier + earlier` or `earlier .* earlier`, then a returned
`let` wire. Comments and whitespace are allowed. Imports, functions, constants,
private inputs, assertions, casts, and nested expressions are outside this
version. Each use must reference the input or a previous binding.
The exact source is limited to 16,384 UTF-8 bytes and 256 tokens.
Commutative operands must appear in increasing positional-wire order, and
no two bindings may repeat the same operation on the same operand pair. The
production canonicalizer would reorder or merge those cases, so this
certificate profile explicitly excludes them.

For example:

```s31
circuit fourth(public x: [m31; 4]) -> public [m31; 4] {
    let square = x .* x;
    let result = square .* square;
    result
}
```

The independent parse yields positional wires `0=x`, `1=square`,
`2=result`. Its expected normalized relation has two ordered `mul` nodes,
both four lanes wide, and a public `result` output. The static sharing is
preserved: wire 1 is used twice by the second operation. For each lane, the
local arithmetic obligations are `square - x*x = 0` and
`result - square*square = 0` over M31.

## What the checker compares

The checker compares the full normalized relation to its independent parse,
not merely hashes. It independently derives the positional SSA and public
ABI. It requires one six-row direct input packing span followed by exactly
one QM31 row per arithmetic node, in the same source-map order. It checks
the value-free native `gate-topology.json` artifact: the first three ordinary
multiply and add gates pack the four input lanes, each source add or
pointwise multiply gate consumes the previously checked wire addresses,
and four masks plus three inverse-basis gates unpack the returned wire into
the four public result addresses. The native builder reserves address 2 for
its fixed extension constant, addresses 3–6 for input words, and addresses
7–10 for result words. Each scalar input must also have a self-product
producer, the direct profile's M31 lane constraint. The independent schedule
fixes the allocation addresses of input lanes, pack terms, source results,
result masks, inverse products, and the eight ABI copies. It compares every
gate triple in native kind order and independently replays
every emitted selector, address, and use-count column row from the native
gate lists, requires every circuit variable to have exactly one producer,
then hashes each column as little-endian M31
words and compares it with the component manifest. For a source operation
`let square = x .* x`, the relevant preprocessed row has pointwise selector
`[0,0,0,1]` and addresses `[x_wire,x_wire,square_wire]`; substituting an add
selector or an operand changes the checked row plan. The remaining constant
gates must derive their QM31 values from fixed
`0`, `1`, and `u`, with `i²=-1` and `u²=2+i`; the pack basis must be the four
unit vectors and each unpack inverse must multiply its basis vector to one.
Extra gates that read public or source data are rejected. The checker requires
an exact, independently computed base-256 constant derivation and `1+1`
padding schedule for this fragment. This fixes the number and addresses of
constant-only gates as well, including the final 512-row/512-variable circuit.
It also requires the direct-gate profile, single QM31 component, package/key/report/manifest
agreement, and SHA-256 of the actual pinned projection and AIR bundle files.
The certificate records the key core, including circuit hash and
preprocessed root, but the key does not hash the certificate; the package
manifest hashes it as an artifact, avoiding a key/certificate hash cycle.

The machine-readable status is:

```json
{
  "source_to_normalized": "source-to-normalized-checked",
  "native_gate_emission": "native-gate-topology-and-selectors-checked",
  "native_root_binding": "preprocessed-root-binding-assumed",
  "gate_lookup_air_pcs": "AIR/PCS-assumed",
  "admission": "python-package-only"
}
```

The parser and checker are independent of the production Python text
compiler. They remain Python code and are not Lean-verified. The existing
Lean SSA certificate and local packed arithmetic-row theorems explain the
intended semantics of this fragment; this checker has not been proved to
implement those Lean definitions.

## Proof boundary and invocation

Call S31 package verification before using the package's prover or native
verifier. Package verification requires this certificate for every text
source in the accepted grammar and rejects an unsupported source carrying
one. The standalone installed native verifier checks a proof against its
sealed normalized relation and key; it does **not** read `.s31` bytes or this
certificate. A native verifier invoked directly cannot claim source
correspondence from the certificate.

The exported topology is produced by the native inspector and checked by a
separate Python replay. Its per-column hashes bind it to the generated
component manifest, but this checker does not independently derive the PCS
preprocessed root or prove the native verifier reconstructs exactly those
columns. It also does not prove the Gate input/output lookup join,
AIR-to-rational implication, PCS opening checks, or verifier statement/key
binding. These remain explicit native assumptions. Artifact hashes are
identity checks, not semantic theorems.

The acceptance control builds a genuine direct-gate package and proof for
the square example. Its negative control builds a second, natively sealed
package in which the first relation node is changed from `mul` to `add`,
while retaining the original `.s31` bytes. It rehashes and reseals the
untrusted package metadata and simulates a compromised production text
lowerer that endorses that altered relation. The independent parser still
rejects the package before package-level proof admission.

Four further controls mutate the native value-free topology: they change a
source pointwise gate into an add gate, replace an extension-field basis
constant, make an otherwise unused gate read the computed result, or replace
a `1+1` padding gate with a zero-only gate. Each
control recomputes all eight columns, their manifest hashes, the package
key/report, and the certificate/artifact hashes. Package admission rejects
all four on semantic grounds. These controls exercise topology replay
separately from the normalized-relation checker.
