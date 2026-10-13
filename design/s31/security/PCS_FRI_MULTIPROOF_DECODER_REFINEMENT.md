# Lifted Merkle compressed decoder refinement check

The S31 verifier calls the pinned `stwo-zig` lifted Merkle verifier. Its proof
contains a **compressed** list of sibling hashes, while the FRI capture
records one **full** authentication path per requested leaf. The deterministic
decoder is the bridge between those representations.
The reviewed `deps/stwo-zig` gitlink is `59e1f115250b8af01712b9bf3d71616e53094964`;
its `verifyImpl` rejects positions outside `2^height` when the height is below
the machine word width. The native runner checks that the submodule checkout
matches the gitlink before exercising this guard.

[`pcs_fri_decoder_refinement_native.zig`](../../../formal/s31/tests/pcs_fri_decoder_refinement_native.zig)
builds a complete eight-leaf tree independently of the decoder. For every one
of the 255 nonempty query subsets it creates a compressed witness from that
tree, asks the native `verifyWithPathCapture` to verify it, and compares **every
captured sibling at every level** with the original tree. The queries are fed
in reverse order with one duplicate, so the check covers native sorting,
deduplication, witness cursor order, paired nodes, ancestor lookup, and copying
paths back to the caller's order. A separate two-column case verifies native
log-size column ordering before leaf hashing. This finite check runs the
actual pinned Zig decoder and S31's `Blake2sPlainMerkleHasher`, whose leaf and
parent hashing have no type prefixes.

For example, query leaves `1`, `3`, and `7` in an eight-leaf tree. `Lᵢ` is a
leaf hash and `Pᵢⱼ` is the parent of the indexed leaf pair:

```text
layer 0: queried L1,L3,L7 consume witnesses L0,L2,L6
         frontier becomes P01,P23,P67
layer 1: P01,P23 pair without witness; P67 consumes P45
         frontier becomes P0123,P4567
layer 2: P0123,P4567 pair without witness; frontier becomes root

compressed witness: [L0,L2,L6,P45]
captured path for 1: [L0,P23,P4567]
captured path for 3: [L2,P01,P4567]
captured path for 7: [L6,P45,P0123]
```

The same exhaustive check now runs an **independent post-verification trace
checker** for each accepted subset. Starting from the supplied leaf values,
the compressed witness, and the published capture, it sorts and deduplicates
the query nodes, emits one `pair` or `witness` event per frontier chunk,
records each witness offset, hashes the parent, and checks every copied path
entry against its corresponding ancestor. It requires witness offsets to be
exactly `0, 1, …, n−1`, no unused witness, and the final hash to equal the
root. Changed captured siblings, reordered witnesses, short witnesses, and
surplus witnesses have explicit rejection tests. The check is single-column
and uses finite eight-leaf examples; the existing two-column test separately
checks the log-size ordering used for leaf hashing.

The test also requires a short witness, surplus witness, changed hash,
inconsistent duplicate row, and out-of-domain index to fail without publishing
a capture. The companion [source guard](../../../scripts/s31_formal_lib/pcs_fri_capture.py)
pins the reviewed `verifyImpl` stages and has hostile mutation tests. Run both
with:

```sh
formal/s31/tests/run_pcs_fri_decoder_refinement_native.sh
```

The [general-height native suite](../../../formal/s31/tests/pcs_fri_decoder_general_native.zig)
extends the independent complete-tree oracle to heights `0`, `1`, `2`, `4`,
and `6`, using singleton, alternating, full, and irregular sparse query sets.
Every case submits reversed queries and two duplicates, then checks every
captured sibling against the full tree. It also checks that inconsistent
duplicates, a query outside the declared tree, a short column, a short or
surplus witness, and a changed witness fail without publishing a capture.
A separate single-query case constructs an authentication path at height
`@bitSizeOf(usize)` for `maxInt(usize)` and checks the full copy. This covers
the native verifier's finite-width range-guard boundary without allocating an
enormous tree; S31's higher-level capture admission currently restricts
heights to less than the word width. An empty-tree case checks its special
no-query, no-witness contract.
These examples sample arbitrary-height behavior; they do not exhaust it.

The general-height suite also builds a 16-leaf commitment from **three**
columns with log sizes `[4,2,4]`. At leaf `i`, the short column is projected
to `2·⌊i/8⌋ + (i mod 2)`, and the native leaf row must be ordered as
`[column 1, column 0, column 2]`. The test checks all full paths for queries
`[15,9,4,1,9]`. Changing the repeated row in **any** of the three columns
must return `DuplicateQueryMismatch`; changing one nonduplicate projected
value must fail at the root without publishing a capture. This is a finite
check of row assembly and tie order against an independently built tree.

## Executable raw-query model

[`MultiproofRawQueries.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofRawQueries.lean)
adds an executable front end to the existing all-height decoder. It checks
`position < 2^height` and equality of **rows** for repeated positions before
hashing. It removes identical rows, sorts by position, decodes the compressed
witness, checks the root and unused-witness suffix, and maps full paths back to
the original caller slots. It proves that successful parsing supplies a
strictly sorted initial frontier and contains every caller leaf, so the prior
all-height and caller-order theorems apply without those model premises.
The model checks final index `0`; `parsedDecode_root_index_zero` proves that
this index follows from the bounded position and complete path for every
nonempty accepted query set. Native Zig checks the final hash and singleton
frontier directly.

For a small hand calculation, take height `1`, leaf hash equal to the sum of
the row, and parent hash `100·left + right`. Caller queries are
`[(1,[11]), (0,[10]), (1,[11])]`, and the compressed witness is empty. The
parser produces frontier `[(0,10),(1,11)]`; the paired chunk yields root
`1011`. Captured paths return in caller order as `[[10],[11],[10]]`.
Changing the final row to `[12]`, using position `3`, or omitting the one
witness needed for a lone query all make the executable model return `none`.
The native verifier is also run with this exact toy hash and these exact
vectors, so the source-bound test compares the two executable semantics at
the parser, root, and caller-copy boundary. The toy hash is intentionally
insecure; the vector checks control flow, not cryptographic binding.

The theorem `verifyRaw_each_opening` proves that every slot returned by this
model is a full opening at the declared height and root. The theorem
`verifyRaw_refines_committed_row` then identifies that row with the projected
committed columns **if** an opening from the actual committed tree is supplied
and the two concrete openings do not witness a hash collision. The model does
not establish that Zig executes this function, that native leaf bytes encode
the same rows, or that the actual prover committed the projected columns.
The source guard pins the row comparison, row assembly cursor, leaf hashing,
frontier loop, and caller-order copy; the native tests give differential
evidence for those stages.

The separate [committed-column origin note](PCS_FRI_COMMITTED_COLUMN_ORIGIN.md)
constructs an ideal complete Merkle tree from the projected columns, proves
that each projected row has an opening to its computed root, and checks the
pinned prover's leaves, parents, decommit rows, and verifier paths against an
independent native tree. Zig-to-Lean equivalence and quantitative binding
remain open.

This is a **finite executable refinement check**, not a proof of arbitrary
height Zig semantics. The existing
[`MultiproofDecoder.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofDecoder.lean)
proves one-layer model properties and
[`MultiproofCapture.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofCapture.lean)
proves that modeled full paths replay to the checked root. The native
[`MultiproofAllHeights.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofAllHeights.lean)
now composes the executable layer decoder for any height. If its full decode
ends in one checked root with no surplus witness, every initial query has a
path of exactly that height to the root, and the original compressed witness
is consumed exactly once in frontier order. The
[`MultiproofSortedFrontier.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofSortedFrontier.lean)
theorem proves that a strictly sorted input frontier emits strictly sorted
parents, including the nonpaired even-index case. It then proves the native
one-sort loop equivalent to the guarded all-height model from a sorted initial
frontier. The new `decodeNativeShape_witness_accounting` and
`decodeNativeShape_follows` theorems give exact model witness order and a
path for every initial query through that one-sort shape. The native Zig
[`MultiproofCallerOrder.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofCallerOrder.lean)
model now maps those unique paths back to each original request slot. Its
theorems prove a checked full path for every slot at arbitrary depth and equal
paths for equal duplicate requests. The native source guard pins the
`unique_index` increment, source and destination offsets, original position
copy, and publication after the root check. The native Zig sort/dedup,
finite-width index arithmetic, and path-copy loops still need a semantic
proof. The trace checker and general-height suite supply differential
evidence, not that proof. The tests do not establish that
the native committed tree was built from the intended oracle columns, nor a
quantitative BLAKE2s collision reduction. The Merkle binding theorem compares
openings at the **same root, height, and index** and extracts a concrete leaf
or parent collision; it makes no global injectivity assumption. P06 stays open
until those native origin and cryptographic obligations are discharged.
Empty-tree placeholders and cross-height reuse of a plain-hash root are outside
this finite check and need explicit protocol-level shape handling.

The follow-up [native collision reduction](PCS_FRI_NATIVE_MERKLE_COLLISION_REDUCTION.md)
works at arbitrary representable path depth: for two accepted full paths with
different canonical rows at the same root, height and index, it constructs a
checkable leaf or parent collision certificate. It also adds an exact
duplicate-query audit to the native test utility. This
does not supply a quantitative BLAKE2s bound or the general decoder proof.
