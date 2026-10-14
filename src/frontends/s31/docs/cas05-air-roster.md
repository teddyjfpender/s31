# Candidate CAS05 source-to-AIR roster

**Status:** geometry and metadata gate only. Production dispatch remains
closed. This gate does not construct XDM04 source columns, assert the S31 AIR
against them, or prove PCS/FRI soundness.

S31 already generates a Gate component roster from the embedded program,
selected AIR bundle, and preprocessed circuit. The roster lists every
preprocessed column, each AIR component's base and interaction column counts,
its trace log size, and the component's proof and claimed-sum position. A
verifier must regenerate this roster from the installed source and AIR; JSON
supplied alongside a proof is not a trust root.

`runtime/pcs/cas05_air_roster.zig` assigns a **candidate** XDM04 source slot
to each of those compiler-owned columns. Within each height, the order is:

1. preprocessed columns in their existing commitment order;
2. components in proof order, with each component's base columns followed by
   its interaction columns in local order.

Each source slot gets an OOD claim slot at the same height and column index.
For example, suppose a generated roster has one component at log size 6 with
one base and one interaction column, and another at log size 5 with the same
two columns. There are no fixed columns. The candidate mapping is:

| XDM04 height | Domain rows | Source column | S31 AIR column | OOD claim |
| --- | ---: | ---: | --- | ---: |
| 0 | 64 | 0 | component 0, base 0 | claim 0 at height 0 |
| 0 | 64 | 1 | component 0, interaction 0 | claim 1 at height 0 |
| 1 | 32 | 0 | component 1, base 0 | claim 0 at height 1 |
| 1 | 32 | 1 | component 1, interaction 0 | claim 1 at height 1 |

The typed SHA-256 digest includes a domain tag, the complete regenerated Gate
manifest digest, the largest log size, height and column counts, and every
ordered source/AIR/claim entry. The audit-only
`inspectGeneratedGateCandidate` entry point derives this digest, compares
the candidate key's profile with the generated geometry, and then checks the
key's roster field. It does not accept a caller-supplied roster digest.
The experimental stwo-zig S31 transcript prelude has a slot for this same
digest. Equal digests only establish that both sides named the same proposed
slots. The actual prover must commit those exact column values to XDM04 and the
verifier must bind all of their OOD claims into the corresponding S31 AIR
checks before this becomes a sound proof path.

The present CAS05 v6 source profile admits 2–8 **adjacent** log sizes and at
most 64 columns per height. The checked-in generated Gate fixture has
component log sizes 20, 18, 16, 14, 9, 8, and 4. It spans 17 heights with
gaps, so the candidate gate rejects it as `UnsupportedCas05HeightRange`.
The direct Gate profile has one height and also fails this profile. This is
a protocol-level mismatch, not a missing hash. The minimal design choice is:

1. Generalize XDM04/CAS05 to sparse arbitrary heights, including `H=1`,
   with new authenticated-opening and fold checks and a new paper-to-native
   bound for that geometry. One exploratory encoding would permit explicit
   zero-column insertion levels and at least 17 heights for today's Gate
   roster. That would change the commitment and fold schedule and needs a
   fresh theorem and host-memory analysis; it is not an established transform.
2. prove a compiler AIR repacking/padding transform that preserves every
   constraint, source commitment, degree bound, and OOD claim while fitting
   the current adjacent-height profile.

Neither route is implemented or proved. The selected release **measure** is
the paper work-factor target `ε(T)/T ≤ 2⁻⁹⁶`. The existing paper fixture
uses `T=2³²` as a **provisional illustration**, not a selected deployment
threat budget; the native budget must be fixed and justified before admission.
This is not an achieved native security claim: native proven bits remain
`null`, and CAS05 release admission remains closed. The fixture's
illustrative 232-query calculation is for a one-table single-point model,
not for this S31 AIR mapping or native CAS05's conjugate two-point quotient.

Run the focused geometry and hostile-shape tests with:

```sh
zig build --build-file src/frontends/s31/build.zig \
  test-cas05-air-roster -j2 -Doptimize=ReleaseSafe
```
