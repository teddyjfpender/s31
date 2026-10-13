# Multi-field record source to native fixed rows

This opt-in certificate joins four existing checks on **one pinned package
snapshot**: exact `.s31` bytes to typed `Program` in Lean, the independent
record source relation and ABI, source arithmetic cells in the native
512-row Gate fixed columns, and native proof verification under the pinned
key. The caller supplies SHA-256 pins for source text, relation, key, prover,
verifier, and Lean checker from outside the package.

## A calculation by hand

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let Pair { right: saved, left } = x;
    let Pair { right: secret } = y;
    let p = left .* secret;
    let q = p + saved;
    Pair { right: saved, left: q }
}
```

Take public `x=(2,3)` and private `y=(5,7)`. The three pattern bindings
`saved`, `left`, and `secret` are aliases of existing input fields; no new
arithmetic wire or Gate row is allocated for them. The source calculations
are `p=2×7=14` and `q=14+3=17`. The public record result is `(17,3)`; the
typed public statement carries `[2,3,17,3]` in declared leaf order and
omits both private fields.

| Source wire | Gate address | Meaning |
| --- | ---: | --- |
| `x.left` | 11 | public input 2 |
| `x.right` | 14 | public input 3 and `saved` |
| `y.left` | 15 | private input 5, unused in this calculation |
| `y.right` | 16 | private input 7 and `secret` |
| `p` | 17 | `2 × 7 = 14` |
| `q` | 18 | `14 + 3 = 17` |

The native pointwise-multiply row is physical row 508 with selector
`(0,0,0,1)` and addresses `(11,16,17)`. The add row is physical row 0 with
selector `(1,0,0,0)` and addresses `(14,17,18)`. Native lowering swapped
the two add operands compared with written `p + saved`; M31 addition is
commutative, and the Lean `FixedSourceCell` and scalar-row theorem accept
exactly these two orientations. Each source row has lookup multiplicity 1:
`p` is read once by `q`, and `q` is read once by the public-output copy.
The checker reconstructs each multiplicity from **all** fixed operand uses
and public output slots, then compares the full eight-column export to the
component manifest and the native recommitted root to the pinned key.

Run the certificate on a built package and proof with externally obtained
digests:

```sh
python3 scripts/release/record_v2_multifield_row_certificate.py PACKAGE PROOF \
  --statement STATEMENT --lean-checker CHECKER \
  --lean-checker-sha256 CHECKER_DIGEST \
  --source-sha256 RELATION_DIGEST --text-sha256 SOURCE_DIGEST \
  --key-sha256 KEY_DIGEST --prover-sha256 PROVER_DIGEST \
  --verifier-sha256 VERIFIER_DIGEST
```

`formal/s31/scripts/check_record_v2_multifield_row_certificate.py` runs a
real two-field/private proof through this path. It rejects changed public
output or alias words, corrupted proof bytes, incorrect external source/key
pins, changed exact source or structural projection, changed source row
address or multiplicity, and a changed fixed root.
The source-to-row checker also rejects dead source nodes with zero use
multiplicity; the Lean private-existence theorem requires live source cells.

## Precise proof boundary

Lean `checkStatic` checks exact bytes against the complete relation, ABI,
typed structural derivation, and actual typed `Program`; its topology pass
checks every source operand and result name. The physical-row and private
existence theorems then apply to a decoded trace **if** its fixed columns,
scalar input cells, arithmetic residuals, Gate lookup balance, unique
production, and public pins satisfy their stated premises. The certificate
checks fixed-column identity and native verifier acceptance; it does not
establish from that acceptance that the main trace satisfies those Lean
premises. The private assignment is existential in the Lean theorem. This
certificate does not expose or bind a particular private witness from the
native proof to a separately supplied Lean assignment. Native PCS/FRI,
Fiat–Shamir, fixed-root commitment security, and the verifier implementation
remain separate obligations.
