# Bounded source to raw Gate AIR

[The pure source-byte bridge](GeneralLinearSSASourceBytes.md) gives a
handwritten `.s31` example, its positional SSA IDs, active packed-row
equations, and a theorem binding supplied source bytes to modeled AIR
acceptance.

[The effectful source-byte bridge](GeneralLinearSSAEffectsSourceBytes.md)
independently parses source with constants and `assert_eq`, checks its exact
indexed graph against canonical compiler certificate bytes, and proves that
any modeled AIR trace satisfying those rows and assertions has the parsed
source's result.

## General linear M31 SSA kernel

[The general linear SSA correspondence](GeneralLinearSSA.md) proves, for any
M31 array length and finite number of inputs and `add`/`sub`/`mul` nodes,
that a checked positional graph's complete packed AIR row relation and its
executable normalized-node relation accept exactly the selected source-term
value. It covers reused operands, unused nodes, short final rows, arbitrary
inactive padding, and arbitrary satisfying witnesses. Its separately stated
boundary is the binding from real `.s31` and JSON bytes to this graph and
from native committed rows to the modeled AIR equations.

[The effects profile](GeneralLinearSSAEffects.md) extends that graph kernel
with canonical constant arithmetic and live equality assertions. It proves
soundness and conditional completeness for arbitrary finite graphs, and a
strict byte gate checks a production affine/assertion fixture; the effectful
source-byte bridge also derives its meaning directly from bounded `.s31`
syntax. Native rows, public ABI, and proof authentication remain separate
obligations.

[The public ABI byte gate](GeneralLinearSSAPublicABI.md) derives the ordered
M31 input/output layout from either checked certificate profile, checks exact
canonical ABI and named assignment JSON, and matches all eight little-endian
public words byte for byte. The theorem joins this gate to modeled AIR
soundness; native public-pin ownership remains open.

## Optimized source row capacity

[The optimized decoded-trace theorem](OptimizedDecodedTrace.md) connects an
arbitrary physical 512-row trace to exact optimized source semantics, including
the installed arithmetic roots, Gate event balance, and public pins. It proves
the compact input-pack producer is live from source admission and CSE, so the
caller cannot assume this separately. The theorem's trace premises are
explicit and do not follow from a native verifier result.

[The optimized physical roster proof](OptimizedPhysicalRoster.md) derives the
compact program's 16-producer budget from the accepted optimizer, then fixes
its 512-row direct-Gate partition and proves 28 distinct source/public
positions for a four-let program with one CSE hit. This removes a free row
budget assumption for the modeled optimized source path. Native emission and
proof authentication remain separate checks.

## Optimized source to projected AIR cells

[The optimized source AIR bridge](OptimizedSourceAirRows.md) composes exact
source/normalized/canonical byte admission, commutative operand sorting and
common subexpression elimination, the compact direct-Gate projected cell
schedule, local operation polynomials, and the packed public input boundary.
For the handwritten reversed/CSE program, Lean checks that four source lets
use three compact operation rows at physical positions 3, 503, and 4. An
arbitrary coherent wire satisfying those modeled cells has the source result
at the selected output address. Native emitter and proof authentication remain
explicitly outside this theorem.

[The live optimized release fixture](LiveOptimizedRelease.md) checks the exact
source, normalized JSON and canonical IR bytes used by the native release
acceptance. Both repeated additions feed the output: five source lets share
four arithmetic producers at rows 3, 503, 4 and 5. The conditional modeled
AIR theorem binds any locally accepted public claim to that exact source.

## Latest derived-roster join

[The arbitrary-trace theorem](DerivedRosterArbitraryTrace.md) joins exact
source-byte admission, a 512-row source-derived fixed roster, and the
conditional raw Gate soundness theorem. The [derived multiplicity checker](AliasDerivedGateMultiplicities.lean)
computes each output use count from scheduled reads and the nine public
feeders. This closes the caller-supplied multiplicity gap in the modeled
roster. The theorem assumes decoded fixed cells agree with the roster,
installed arithmetic and Gate runtime facts, and ideal exact balance.
Authentication of committed cells and native verifier refinement remain
separate obligations. See the [independent theorem review](../../../../../../design/s31/security/INDEPENDENT_REVIEW_DERIVED_ROSTER_ARBITRARY_TRACE_2026-10-12.md)
and [formal live evidence](../../../../../../design/s31/security/FORMAL_LIVE_EVIDENCE_2026-10-12.md).

## Canonical add/mul DAG optimization

`CanonicalDagOptimization.lean` models the add/mul branch of Zig
`language/canonical.zig` for one public four-lane M31 input and at most sixteen
fresh, backward-referencing SSA instructions. It maps each source wire to a
compact node ID, orders the two commutative operands by compact ID, and reuses
the first node with the same operation and operands. This models the two
optimizer steps that the existing `SSATextBytes` grammar deliberately excludes.

For example, source operations `a = x + x`, `b = x .* x`, `c = a + b`, and
`d = b + a` become the three compact nodes `a`, `b`, `c`; the output mapping
for `d` points to `c`. The last operation's operands are reversed before the
duplicate lookup. The Lean example checks the exact four-to-three result.

The optimizer is followed by an independent symbolic audit: it reconstructs
the full source and compact expressions from their positional SSA, then checks
equality up to recursively swapping add/mul children. The theorem
`optimizeChecked_semantics` proves that **every accepted** compact result has
the same output as the source for every four-lane M31 input. Its proof derives
commutativity from the implemented M31 modular arithmetic, and runs both
programs through the existing normalized relation evaluator. Kernel-checked
mutations reject a changed operation and a wrong output mapping.
The structural theorem `optimize_exists_of_valid` separately proves that the
optimizer itself emits a compact certificate for **every** bounded positional
SSA whose instruction IDs are fresh, operands read earlier wires, and output
is in range. `findKey_sound`, `found_existing_instruction`, and
`fold_keys_match` prove that a CSE hit selects the first instruction with the
same canonical operation and ordered operands. `CanonicalDagCompleteness.lean`
adds the missing invariant relating all source wires, compact terms, and
canonical cache keys. Its `audit_complete_of_valid` theorem proves that
**every** compact DAG actually produced from this valid bounded fragment
passes the independent symbolic audit, including repeated and reversed
operands. Consequently `optimizeChecked_exists_of_valid` proves the checked
optimizer succeeds on every valid source in this fragment.

These theorems cover the modeled positional SSA fragment. They do not cover
constants, casts, other operation tags, or native AIR emission. Those edges
remain separate correspondence obligations. The focused checks are:

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.CanonicalDagOptimization)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.CanonicalDagOptimization)
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.CanonicalDagCompleteness)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.CanonicalDagCompleteness)
```

### Reversed operands and CSE from source bytes

`OptimizedTextBytes.lean` adds a **separate, bounded byte grammar** for the
direct four-lane add/mul fragment. It admits reversed operands and repeated
expressions, which the older `SSATextBytes.parseLet` rejects. For example:

```s31
circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {
  let a = x + x;
  let b = x .* x;
  let c = a + b;
  let d = b + a;
  d
}
```

The parser retains four source instructions. The checked optimizer emits
three arithmetic nodes and maps source names `x,a,b,c,d` to canonical IDs
`0,1,2,3,3`. The final add's compact operands are `(1,2)`, so the reversed
source form shares `c`'s node. `parsed_bytes_sound` proves that any accepted
source has the same four-lane M31 output as its compact certificate for all
inputs. `checked_bytes_sound` adds exact normalized JSON and canonical IR
byte comparisons as premises of that semantic result. A kernel-checked
example proves this source compacts to the three-node certificate and the
older byte parser rejects it.

The native `language/canonical.zig` fixture runs the production canonical
builder on this source's normalized relation. It checks the complete
source-name-to-ID map, the exact compact legacy IR serialization, and the
SHA-256 digest of those bytes. The Python differential fixture checks that
the production text frontend emits the normalized JSON pinned in Lean and
that the Zig fixture's expected canonical bytes equal the Lean literal. The
canonical digest for this fixture is
`2088c1bad15f2ba5b52f0214e9d3d66744b9c84aa6218aa336d8b337157e7132`.
These are focused executable checks across implementations, not a universal
Lean theorem about the Zig serializer. The older large pinned byte literals
are not kernel-proved to satisfy `checkBytes`; the new live release fixture
does kernel-check its exact production byte triple. The universal theorem
applies whenever that checker accepts its three byte inputs.

The **production canonical builder** accepts this reversed/CSE form. The
Python checker now has a separate `parse_source_optimized` and v3 certificate
API. It derives a source-to-canonical ID map, checks reused native source-map
spans and compact topology, and rejects altered maps even if a report digest
is recomputed. The default v2 package build and verification path still
rejects reversed/CSE; explicit `build --correspondence optimized` now attaches
the v3 certificate and strict `verify-release` recomputes it. The new Lean
grammar is an extension model.
The structural optimizer's audit-completeness theorem is now proved in
`CanonicalDagCompleteness.lean`. Authentication of the resulting AIR and proof
remains open.

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.OptimizedTextBytes)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.OptimizedTextBytes)
(cd src/frontends/s31 && zig build test-canonical-cse -Doptimize=ReleaseFast)
PYTHONPATH=src/frontends/s31/python python3 -m unittest src/frontends/s31/tests/python/test_canonical_optimizer_fixture.py
PYTHONPATH=src/frontends/s31/python python3 -m unittest src/frontends/s31/tests/python/test_optimized_correspondence.py
# Builds a real temporary native package; run on a clean pinned Stwo dependency.
PYTHONPATH=src/frontends/s31/python python3 src/frontends/s31/tests/python/check_optimized_native_package.py
```

`RawGateSoundness.lean` composes the executable source-byte/normalized-byte
relation check, source-derived fixed cell schedule, installed arithmetic roots,
physical public input/output rows, ideal Gate event semantics, and the
source-extracted raw Gate interaction equations. Its main theorem covers an
**arbitrary fixed 512-row witness trace** for every source accepted by the
bounded direct-gate byte grammar. It also handles a returned value followed
by unused arithmetic instructions.

The context names each assumption. `relation` checks exact source and
normalized bytes. `partition` fixes the 512-row gate layout. `fixed` matches
every source and public boundary cell to the decoded fixed columns.
`arithmetic` requires all installed nine-root local arithmetic equations to
vanish on the trace values. `unique` and the public/constant events state the
ideal Gate and ABI obligations. These conditions apply to arbitrary witness
values; no honest witness generator is assumed.

Theorem `balanced_implies_source_claim` proves that ideal exact Gate balance
forces the public claim to equal source evaluation. Theorem
`forged_claim_unbalanced` takes its contrapositive. Theorem
`forged_claim_accepting_pairs_card_le` then uses the production-extracted raw
LogUp equations to bound false acceptance for a fixed forged trace by

```text
(5s² + 2s + 1536) × |QM31| challenge pairs
```

among `|QM31|²` ideal independent pairs, where `s` is the number of distinct
Gate use/yield tuples. The 1536 term includes all three denominators in each
of 512 rows, including a zero-multiplicity output row. Theorem
`installed_bytecode_pair_accepts` connects all-row zero outputs of the
installed extension bytecode to this raw accepting set.

`AliasRawGateSoundness.lean` reuses the same physical trace context for the
zero-cost source alias and redundant-parentheses grammar. Its exact byte
checker proves that the final packed public input has a positive Gate use
count and enforces at most sixteen arithmetic instructions, so the alias
theorem takes no extra input-use or capacity assumption. It also proves all
projected source and public rows are distinct and inside the 512-row trace.
`AliasCanonicalIrBytes.lean` binds the same parsed producers to compact
canonical IR bytes. `AliasCanonicalAirBridge.lean` composes that byte check
with the conditional physical Gate theorem; keeping the modules separate
lets the executable byte audit compile without linking the AIR evaluator.
`GeneratedMutationRows.lean` adds seventeen kernel-checked source-byte samples,
one for each admitted arithmetic length from 1 through 16 plus a second
sixteen-operation spelling with comments. An independent
positional DAG generator supplies the expected certificates, grouped physical
source-row positions, and output-use multiplicities. The even-sized samples
return an earlier producer, so their final eager arithmetic row has zero
output multiplicity. Each sample changes the return or an operation and proves
the altered bytes do not parse to the original certificate. The source-byte
corpus digest and selected-source digest are pinned in the generated file.
For the four native proof samples, Lean also checks every byte of the canonical
normalized JSON and compact canonical IR against its source parser. It rejects
a changed normalized opcode or changed canonical IR bytes. The native package
checker separately compares those bytes and IR digests with the files and
manifest actually used to construct the proofs. SHA-256 is computed outside
Lean, so that digest comparison remains an implementation test.
The two distinct sixteen-operation spellings, one using aliases and one using
comments, are also checked to produce identical normalized and canonical IR
bytes. This states the zero-cost syntax property for those exact source files.
Regenerate and verify it with:

```sh
python3 src/frontends/s31/tests/python/generated/render_lean_source_row_fixture.py --check
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.GeneratedMutationRows)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneratedMutationRows)
```

The rows checked by Lean are source-derived expected rows. Native exporter
equality for a packaged program must still be established by the separate
package topology check; this fixture does not authenticate the committed AIR
columns, witness values, or proof verifier.
`GeneratedNativeClaims.lean` then instantiates the general raw Gate theorem for
the four native samples. For each exact source file, any physical trace meeting
the fixed-cell, arithmetic, public-pin and ideal exact-balance premises yields
the source-computed public result. The source/normalized-byte premise is
discharged by the generated Lean checks; the physical and proof-system
premises remain explicit.
For example,
the following source has one arithmetic producer and therefore one source
arithmetic row; the alias bindings and parentheses add none:

```s31
circuit alias_square(public x: [m31; 4]) -> public [m31; 4] {
  let named = (x);
  let square = ((named) .* (named));
  let result = (square);
  result
}
```

The original source and normalized bytes must match the alias checker. Given
the physical row context and ideal Gate balance, the public result equals
`x .* x` for every four-lane input and arbitrary fixed witness trace. A false
claim receives the same raw challenge bound as the direct spelling.

## Handwritten row example

`AcceptedAliasPublicPhysicalTrace.lean` now constructs one coherent modeled
source and public-boundary wire assignment for **every** source accepted by the
exact alias source/normalized/IR byte checker, at every public input. It
eliminates a caller-supplied honest projected arithmetic witness, including
for aliases that return an earlier producer while later arithmetic rows are
still evaluated. Its stronger projected physical theorem proves distinct
in-range rows and matching fixed tuples for each selected source or public
cell in the same 512-row trace. The installed *local* arithmetic roots vanish;
the unselected rows use synthetic zero-add padding.
See [the hand-worked alias example](AcceptedAliasPublicPhysicalTrace.md) for
the selected circuit addresses and grouped AIR rows. Full native fixed-column
equality, exact Gate balance, and proof authentication remain separate joins.

The checked source fragment can return an earlier result:

```s31
circuit early_output(public x: [m31; 4]) -> public [m31; 4] {
  let a = x .* x;
  let b = x + a;
  let c = a .* b;
  a
}
```

For `x = [1, 2, 3, 4]`, the source computes `a = [1, 4, 9, 16]`,
`b = [2, 6, 12, 20]`, and `c = [2, 24, 108, 320]`. The public result is `a`.
The compiler retains all three arithmetic rows. Under the 512-row direct
profile, 474 rows are in the add partition. The two source products occupy
trace rows 502 and 503, while the source add occupies trace row 3. Source
instruction order and physical trace row order differ because native rows are
grouped by operation.

| Source step | Circuit address | Physical AIR row | Output Gate uses |
| --- | ---: | ---: | ---: |
| `a = x .* x` | 23 | 502 | 6: two later reads and four public masks |
| `b = x + a` | 24 | 3 | 1: read by `c` |
| `c = a .* b` | 25 | 503 | 0: unused result |

Each row's local polynomial constraints still apply. The final row does not
yield a Gate output event because its multiplicity is zero. Its output
denominator nonetheless appears in the raw singleton equation; the challenge
bound includes zero-denominator exceptions for that row. A false claim such as
`[1, 4, 9, 17]` cannot have ideal exact Gate balance with these physical rows
and public pins. The theorem bounds the ideal challenge pairs for which its
raw interaction equations could still close.

This is a local and algebraic correspondence theorem. It does **not** prove
that native verifier acceptance authenticates the trace and fixed columns,
that the installed bytecode is executed by the verifier exactly as modeled,
that PCS/FRI is sound, or that Fiat--Shamir challenges are independent. Those
links remain separate release obligations.

## What the concrete 512-row witness establishes

`ZeroPhysicalTraceWitness.lean` constructs a 512-row decoded trace for the
two-product alias square with zero public input and output. It proves every
field of `AliasFixedTraceContext`: exact alias-byte/normalized-byte admission,
the 512-row partition, all 27 projected fixed cells, all-row local arithmetic
roots, producer-value uniqueness, basis and inverse events, and four input
and output pins. The pins are external Gate **uses**, matching the native
public feeder; exact balance forces matching producer values. This shows
those **stated premises** can hold together.

The fixture deliberately assigns synthetic zero-multiplicity add rows outside
the 27 projected cells and supplies separate synthetic external yields. It is
**not** the production trace. The module proves
both distinctions: Gate balance fails because a basis row reads zero where
the basis producer yields a nonzero unit, and fixed row 11 differs from the
native direct-gate export (`mults = 0` versus `11`). This prevents the context witness
from being misread as proof of honest native witness completeness.

`AliasProjectedExportBridge.lean` separately proves that the alias source's
positional certificate yields exactly the same 27 projected fixed cells as
the pinned `functional_square4` native export. Their program names differ;
the theorem is about certificate and cell equality. The full fixed rows are
checked below; a full honest-trace theorem still needs main-column
assignments, native feeder events, and committed-row authentication.

`PinnedFullOutputRoster.lean` goes one step further with the pinned native
export's **512 output-address and multiplicity pairs**. It proves every row
has those two exact fixed values, all 27 selected cells still match all eight
fixed columns, and the complete active-producer roster gives unique Gate
producer values for arbitrary main columns. For a general decoded trace, this
last theorem needs the complete output/multiplicity equality and coverage of
any separately listed external yield by an existing arithmetic producer.
The module constructs two traces that agree on every exported pair and all
selected cells but disagree on the add selector at row 11. This is an
underdetermination result for the older **two-column projection**; it does
not apply after checking the full fixed roster below.

`PinnedFullFixedRoster.lean` checks all eight fixed columns across all 512
direct-gate AIR rows. Its `fixedAt_exact` theorem quantifies over every one
of the 4096 canonical cells, and `selected_cells_fixed_of_fixed_roster`
derives every selected source and public-boundary cell for any decoded trace
that carries the pinned fixed columns. The generated Lean roster is emitted
from the direct compiler and its direct arithmetic preprocessor. A separate
native `inspect-topology` fixture is checked byte for byte against the Lean
roster by `benchmarks/direct_gate_release_cost/test_fixed_columns.py`.
Both exports have column-major little-endian SHA-256
`cb0e835c505fe2c672cfb79db9a60cc63fc6dea0013b101d6512eac0a23343b0`.
For example, physical row 11 is
`[1, 0, 0, 0, 0, 0, 0, 11]`.

The complete fixed roster is source-derived data. The theorem does not
establish that a verifier commitment opens to those 4096 values, nor does it
constrain the 6144 main cells or the interaction trace. An honest balanced
physical witness and the verifier's PCS/FRI authentication remain separate
obligations. The alias fixture and the native fixture also have different
program names, so their positional certificate equality does not establish
cross-parser equivalence or name-insensitive compilation.

## One concrete native square4 base trace

`PinnedNativeSquare4Witness.lean` composes the full fixed roster with the
checked-in main-column literals captured from one direct prover `writeBase`
diagnostic run for public input
`[0, 1, 2, 7]` and output `[0, 1, 16, 2401]`. The checked-in diagnostic
report is `formal/s31/fixtures/square4-native-physical.json`; its generator
is `formal/s31/scripts/check_square4_native_witness.py`. The native source
digest is `b7d744dd89f487742f2b72cf71fa76c6c37c2f5b01b74b58befa24e8c749979c`,
the key's preprocessed root is
`c0ea49c8f9027d5bdf9ce7a59ded3fb3a1f6b541a0ed1bb6c65b3c7d1175570a`,
and the 12 column-major main evaluations hash to
`3181458839c78d755d55bf7e80e9e43eed0d1f6354258ac18f82e5b92fcf42c3`.

The Lean kernel checks all 4096 fixed and 6144 checked-in main literals as
canonical field values, the selected fixed-cell premise, the complete 512-row
output address/multiplicity projection and producer uniqueness. It proves
local AIR arithmetic for source rows 502 and 503, eight native public copy
producers at addresses 3–10, all nine public feeder uses are native row
yields, and rejection of a mutation to the second square's output. A finite
kernel checked theorem verifies **all 4608 installed arithmetic roots**
across all 512 rows. The independent Python checker repeats that all-row
arithmetic check from the JSON report. Lean also proves **exact ideal Gate
multiset balance** for all
1033 concrete uses and yields via `List.isPerm_iff` and a kernel evaluated
Boolean permutation check. The 512 rows contribute 1024 uses; the nine
external uses are the unit at address 2 and the eight public scalar words
at addresses 3–10. There are no external yields in this native witness.
Lean also proves that changing just the feeder's final public output word
from `2401` to `2400` makes exact Gate balance impossible while all 512 native
rows remain unchanged. The independent checker also checks unique active
producer values and rejects five
fixed, main, pin, claim, and lookup-only mutations.
The formal CI job rechecks the report and compares its generated Lean literal
byte for byte with the committed module. A separate native CI job builds a
fresh `direct-gate` package from the checked-in `.s31` source, exports its
complete 8 × 512 fixed and 12 × 512 main cells through
`inspect-physical-rows`, checks all arithmetic roots and five mutations,
compares the entire JSON report with the committed report, and compares the
rendered Lean fixture byte for byte. Run the same gate locally with
`python3 formal/s31/scripts/check_fresh_square4_native_witness.py`.

`PinnedNativeSquare4Context.lean` uses these kernel checked native facts to
instantiate every field of `PhysicalTraceContext` for the concrete input
`[0, 1, 2, 7]` and claim `[0, 1, 16, 2401]`. It checks the zero, four basis,
and three inverse producers, plus all eight public words in the external
**use** list. This establishes that the arbitrary-trace algebraic soundness
context is satisfiable by one native base assignment. A corollary applies
`physical_balanced_certificate_claim` to this context: any result of the
positional square4 certificate on this input equals the feeder's public
claim. The module also checks that the certificate interpreter actually
returns the claimed four words. The full source-to-native name/IR link and
verifier authentication still require separate work.

The report records uncommitted prover evaluations from one inspected run.
The fresh native CI job re-extracts those evaluations on each run. All-row
arithmetic and exact ideal Gate balance are Lean theorems for this one pinned
base trace. The local
arithmetic equations alone do not determine the main trace: arithmetic
padding row 11 has fixed tuple
`[1, 0, 0, 0, 0, 0, 0, 11]` and a checked-in all-zero main tuple. Replacing
its first input with `1`, second input with `2`, and output with `3` satisfies
the same local add equation, but the enhanced report checker rejects it for
failing exact ideal Gate balance. Its output has Gate multiplicity 11.
Interaction columns, the native feeder's authenticated sign/contribution
semantics, the cryptographic binding from a proof's commitments to these
rows, and PCS/FRI soundness are not established by this fixture. The Lean metadata strings
alone do not prove a hash or key-root relation; the independent package
checker performs the native key/source comparison when regenerating the
report.

Run the fast check from `formal/s31`:

```sh
lake build S31.Gadgets.Functional.Correspondence.RawGateSoundness
lake build S31.Gadgets.Functional.Correspondence.AliasRawGateSoundness
lake build S31.Gadgets.Functional.Correspondence.AliasCanonicalAirBridge
lake build S31.Gadgets.Functional.Correspondence.ZeroPhysicalTraceWitness
lake build S31.Gadgets.Functional.Correspondence.AliasProjectedExportBridge
lake build S31.Gadgets.Functional.Correspondence.PinnedFullOutputRoster
lake build S31.Gadgets.Functional.Correspondence.PinnedFullFixedRoster
lake build S31.Gadgets.Functional.Correspondence.PinnedNativeSquare4Witness
lake env leanchecker S31.Gadgets.Functional.Correspondence.PinnedNativeSquare4Witness
lake build S31.Gadgets.Functional.Correspondence.PinnedNativeSquare4Context
lake env leanchecker S31.Gadgets.Functional.Correspondence.PinnedNativeSquare4Context
```
