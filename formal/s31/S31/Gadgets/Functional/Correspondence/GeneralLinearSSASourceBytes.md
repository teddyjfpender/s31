# Pure S31 source bytes to modeled AIR

The Lean checker in `GeneralLinearSSASourceBytes.lean` consumes two supplied
files: ASCII `.s31` source and a canonical JSON source-relation certificate.
It parses the source independently, derives a positional SSA graph, decodes
the certificate independently, and requires the two graphs to be equal. The
source term used by the theorem is *derived by the parser*, so the caller does
not get to choose a convenient Lean term after seeing the certificate.

Here is the checked three-lane fixture:

```s31
circuit three(public x: [m31; 3]) -> public [m31; 3] {
  let a = x + x;
  let b = a - x;
  let c = a .* b;
  c
}
```

The parser assigns `x=0`, `a=1`, `b=2`, and `c=3`. It checks that every
operand ID existed before its `let`, every name is distinct, every array
has three lanes, and the selected public output is ID 3. The certificate
must say exactly:

| New ID | Operation | Left ID | Right ID |
| --- | --- | --- | --- |
| 1 | add | 0 (`x`) | 0 (`x`) |
| 2 | sub | 1 (`a`) | 0 (`x`) |
| 3 | mul | 1 (`a`) | 2 (`b`) |

For each active lane `i ∈ {0,1,2}`, the modeled arithmetic rows constrain
`aᵢ - xᵢ - xᵢ = 0`, `bᵢ - aᵢ + xᵢ = 0`, and `cᵢ - aᵢbᵢ = 0` in M31. For
example, `xᵢ=2` forces `aᵢ=4`, `bᵢ=2`, and `cᵢ=8`. A packed row may have a
fourth inactive position; its value does not affect the three active lanes.

The theorem `checked_source_air_sound` says: if the joint source/certificate
checker accepts and a complete modeled packed-row trace satisfies all three
instructions, its selected output equals the source parser's denotation for
*every* input assignment. The proof covers any number of nodes and lanes
within this parser's bounded grammar; it does not enumerate inputs.

This parser deliberately covers plain binary add/sub/mul `let` statements,
one circuit, 1–4 named inputs, 1–8 equal-length M31 lanes, 1–16 nodes, and
no helpers, aliases, constants, or assertions. Its source/certificate gate
also caps certificate bytes at 65 KiB. The circuit name is validated as an
identifier but is absent from the certificate's SSA field set, so it is not
identity-bound by this Lean checker. The package verifier separately checks
source and relation digests, public ABI, native rows, and proof artifacts.
The theorem's `AcceptsTrace` premise is a mathematical row-satisfaction
premise; the native PCS/FRI verifier-to-that-premise bridge remains open.

Run the concrete controls from `formal/s31` after building the Lean module:

```sh
python3 tests/audit/general_linear_source_check.py
```

They admit four real bounded sources and reject seven changed sources or
certificates, including altered subtraction order, visibility, source names,
an extra input, trailing syntax, and an oversized certificate.
