# Arithmetic-produced chip input ports

Status: **experimental implementation; native acceptance and independent review pending**.

The source-bound `direct-mixed-general` profile previously admitted a chip call
only when its four-lane input was a private input or an earlier chip result.
This extension admits one of `add`, `mul`, `add_const`, or `mul_const` as the
immediate input node of an existing `square; add_const(c)` chip call. It does
not introduce a chip kind, change the recurrence, or enable the source-only
Mix4 draft. The existing bounds remain one to eight live calls, 16–32768
power-of-two rounds per call, at most 2¹⁸ rounds total, and exactly eight
public M31 words in the mixed general proof. The native lookup budget still
checks the actual compiled circuit row count and total weighted events.

The normalized [two-call source](../../../src/frontends/s31/examples/boundary/private_arithmetic_chip_input.s31.json)
uses the following computation, with all operations in M31:

```text
a      = repeat_16(y ↦ y² + 13, x)
middle = a + x                  // ordinary circuit arithmetic
b      = repeat_16(y ↦ y² + 17, middle)
public = (b + x, b · middle)
```

For `x = [0, 1, p−1, 7]` and `p = 2³¹−1`, the first chip returns
`[296612488, 2076908689, 2076908689, 2108197386]`. The circuit's
`middle` is `[296612488, 2076908690, 2076908688, 2108197393]`. The second
chip receives those four words at four scalar Gate addresses. Its output is
`[1617586023, 1913274192, 578207781, 796105780]`, and the two public
arrays are recorded in the adjacent fixture.

## Why the extraction is constrained

The SIMD circuit represents `middle` as one packed QM31 wire. The boundary
cannot trust four values copied from the host evaluator. At the arithmetic
node, the bounded compiler applies `simd.unpack` to that packed wire. Each
`unpackIdx` extracts one coordinate by a pointwise multiplication with a
fixed basis vector and, for coordinates 1–3, multiplication by its inverse.
These are recorded circuit gates. The four resulting base-field wires have
unique producer addresses and are used as the second chip's input ports.
Both witness-free and value compilers perform the same extraction, and the
runtime compares the full call map, circuit shape, and preprocessed root
before proving. The verifier independently recompiles the embedded source
and reconstructs the same root, component roster and PCS geometry before
decoding proof bytes.

The [fork source](../../../src/frontends/s31/examples/boundary/private_arithmetic_chip_fork.s31.json)
feeds `middle` to two different chips. Extraction happens once at the source
node, so the calls refer to the same four addresses. The preprocessed Gate
multiplicity increases once **per endpoint occurrence**, yielding two extra
uses at each of those addresses. An omitted use would leave a lookup
imbalance; disallowing repeated addresses would reject valid fan-out.

This is a source-grammar extension of experimental `S31MIX07`. It retains
registry v1 and the existing transcript because the chip AIR, tuple schema,
component order and proof envelope do not change. Literal source bytes,
compiled addresses, fixed root, and the generated registry manifest are
bound into the existing source-derived identity. Previously admitted source
programs compile through the same path and should retain their proof bytes;
that regression remains a required native gate. Adding a different transition
such as Mix4 requires a new constructor, lookup relation, registry and
transcript version.

## Required acceptance and remaining assumptions

Run the focused compiler tests and
[`arithmetic_chip_input.py`](../../../src/frontends/s31/tests/acceptance/mixed_boundary/arithmetic_chip_input.py)
after the paired timing study releases CPU capacity. The native script checks
both source fixtures and all four admitted arithmetic feeder operators, an
independent M31 integer oracle, source-derived manifest hashes and address
fan-out, honest proofs, changed public words and assignments, every claimed-sum
slot, a compensated sum pair, proof corruption, a semantics-preserving source
change with resealed statement and proof-envelope identities, and a dead-call
build rejection. Unit tests compare witness values at the four constrained ports,
the witness and topology maps, one producer per port, and exact multiplicity
two for the shared fork ports. The
[old-family proof-byte gate](../../../src/frontends/s31/tests/acceptance/mixed_boundary/PROOF_BYTE_COMPATIBILITY.md)
must additionally confirm unchanged proof bytes for the prior one-to-eight
source family; no frozen baseline exists yet.

These tests do not discharge the proof-system assumptions: the selected AIR
must constrain every Gate and chip row and its claimed LogUp fractions; the
lookup-compression calculation assumes base trace tuples are fixed before
uniform challenges; and the exact PCS/FRI/Fiat–Shamir configuration needs
its own soundness argument. This profile is transparent. A committed bridge
can reveal a private endpoint, so language `private` does not promise witness
confidentiality.
