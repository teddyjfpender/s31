# P02: gate interaction boundary and lookup-use cap

For the sealed `gate` profile, this diagnostic checks a narrow bridge between
the package roster and the native verifier. It is deliberately conditional:
the full AIR/interaction correspondence and native PCS/FRI soundness are open.

```sh
python3 -B scripts/release/pcs_fri_gate_interaction.py /path/to/sealed-gate-package \
  --proof /path/to/proof --statement /path/to/public-statement.json
python3 -B scripts/release/pcs_fri_gate_interaction.py /path/to/sealed-gate-package --require-p02
```

The package diagnostic executes its installed `check-key` verifier. With a
proof and statement, it also requires native proof acceptance and changes
each of the eleven encoded component claims, one at a time, by one canonical
M31 unit. The same native verifier must reject every altered proof with
`InvalidLookupSum`.
The diagnostic only runs binaries that the caller already trusts locally;
artifact hashes and checked source files do not establish executable
provenance. `--require-p02` exits 2 while the full obligation remains open.

## What the gate verifier checks

The legacy native gate proof header contains exactly eleven canonical QM31
claimed sums. The verifier mixes the preprocessed and base trace roots and the
eight public words, checks the interaction PoW, draws one lookup challenge
pair `(z, α)`, and then evaluates the following equation before it mixes the
claimed sums and commits the interaction root:

```text
Σ_{component=0}^{10} claimed_sum[component]
  + Σ_{j=0}^{7} 1 / (GateTuple(3+j, public_word[j])(α) - z)
  + 1 / (GateTuple(2, u)(α) - z)
  = 0

GateTuple(address, value) = [378353459, address,
                             value.limb0, value.limb1,
                             value.limb2, value.limb3]
u = (0, 0, 1, 0) in the QM31 basis
```

For the native host verifier, each public `u32` is embedded as QM31 limbs
`(word & 0xffff, word >> 16, 0, 0)` before this equation is evaluated.

`GatePublicInteraction.lean` proves that the source-order claim loop equals
the sum of all eleven claims and the nine public Gate fractions. It also
proves the public event count for exactly eight output words. The existing
`TaggedPairSourceCorrespondence` model supplies the exact output addresses,
`u` tuple, and Horner compression; this P02 theorem reuses that model for the
legacy gate verifier's eleven-claim path. Source hashes pin the native host
verifier, witness lookup sum, component facts and in-circuit verifier version
reviewed here. A changed source needs a renewed review.

## Lookup-use arithmetic

The component roster now rejects coherent resealing of the static native AIR
facts: base and interaction widths, log-size sources, fixed table heights,
and every relation-use count and ID. Dynamic trace heights remain derived
from the package. The diagnostic separately replays the native
`checkRelationUses` upper bound for each relation:

```text
rows_i                 = 2^(component_trace_log_i)
shifted_bound[relation] = Σ_i (floor(rows_i / 2^16) + 1) × uses_per_row_i
exact_uses[relation]    = Σ_i rows_i × uses_per_row_i
require shifted_bound < 2^15 and exact_uses < p = 2^31−1
```

The first inequality is the in-circuit 15-bit bound. It implies
`exact_uses < 2^31`; the diagnostic also checks the exact integer sum and
that it lies under the shifted upper envelope. For a local sealed
`affine_guard` package, the Gate relation has 1,216 exact uses and shifted
bound 14. `VerifyBitwiseXor_8` has 224 uses and shifted bound 14; the other
six relations have smaller counts. These are **lookup-use counts**, not a
bound on all signed multiplicity values or on the probability of a false
LogUp closure.

## Remaining proof obligations

The local checks do not prove that accepted PCS/FRI openings authenticate
every component's base and interaction rows, that all denominator poles are
handled, or that the eleven claimed sums equal the row sums of the compiled
AIR. They do not cover all S31 lowerings or give a security-bit estimate.
P02 and the v0.1 proven release gate stay open.

Focused checks:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_gate_interaction \
  src.frontends.s31.tests.python.test_gate_component_roster -v
cd formal/s31 && lake env lean S31/Gadgets/Air/GatePublicInteraction.lean
```
