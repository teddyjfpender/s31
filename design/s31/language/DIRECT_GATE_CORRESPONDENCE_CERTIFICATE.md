# Bounded direct-gate correspondence certificate

`correspondence-certificate.json` is a package-admission check for a narrow
source language. It does not certify arbitrary S31 or change the installed
native verifier's accepted proof language.

## Accepted source

The checker independently tokenizes the exact UTF-8 `.s31` bytes. It accepts
one public `[m31; 4]` input and one public `[m31; 4]` output, 1–16 fresh
`let` bindings of `earlier + earlier` or `earlier .* earlier`, then a returned
wire. Comments and whitespace are allowed. Imports, functions, constants,
private inputs, assertions, casts, and nested expressions are outside this
version. Each use must reference the input or a previous binding.

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
the direct-gate profile, single QM31 component, package/key/report/manifest
agreement, and SHA-256 of the actual pinned projection and AIR bundle files.
The certificate records the key core, including circuit hash and
preprocessed root, but the key does not hash the certificate; the package
manifest hashes it as an artifact, avoiding a key/certificate hash cycle.

The machine-readable status is:

```json
{
  "source_to_normalized": "source-to-normalized-checked",
  "native_gate_emission": "native-gate-emission-assumed",
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

The source-map gate spans and circuit hash bind native metadata but do not
independently reconstruct Zig's exact gates or their preprocessed selector
values. A future theorem or trusted gate-plan checker must prove the native
Gate input/output lookup join, row emission, AIR-to-rational implication,
PCS opening checks, and verifier statement/key binding. Hashes are identity
checks, not proofs of these implications.

The acceptance control builds a genuine direct-gate package and proof for
the square example. Its negative control builds a second, natively sealed
package in which the first relation node is changed from `mul` to `add`,
while retaining the original `.s31` bytes. It rehashes and reseals the
untrusted package metadata and simulates a compromised production text
lowerer that endorses that altered relation. The independent parser still
rejects the package before package-level proof admission.
