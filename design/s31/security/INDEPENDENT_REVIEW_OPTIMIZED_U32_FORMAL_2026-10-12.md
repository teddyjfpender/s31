# Independent review: optimized decoded trace and public u32 record model

Initially reviewed commits: `1eb8bc9` (`RecordU32BoundaryV2.lean`) and `9cc9c44`
(`OptimizedDecodedTrace.lean`), on release base `a37e659`. The alias finding
was retested after optimized parser extension `bb4391e`. This review checks
exact theorem statements against the Python optimized package parser, Zig
record statement parser, and mixed bridge writer. It is not a proof-system
security audit or an assertion that a native verifier accepts every modeled
trace.

## Results and severity

| Result | Severity for the scoped release | Evidence |
| --- | --- | --- |
| The pinned optimized source/JSON/IR triple satisfies the Lean `checkBytes` premise. | Positive check | `OptimizedDecodedTraceAudit.pinned_checked_byte_triple`, kernel checked. |
| The reviewed alias let now enters the Lean optimized grammar with exactly two arithmetic producers. | Specific grammar gap closed; full v3 compiler correspondence remains open | Python `parse_source_optimized` and production text compilation agree; `OptimizedDecodedTraceAudit.alias_let_inside_modeled_grammar` checks the raw certificate. A second alias plus CSE fixture passes exact source/normalized JSON/compact IR admission via `optimized_alias_exact_byte_triple`. |
| The u32 theorem proves a two-limb integer bijection and a *modeled* accepted claim, conditional on a validated `u32`/width-2 descriptor. | Coverage gap; blocks a claim of native ABI/AIR refinement | `checked_u32_claim_packs` assumes descriptor kind and width; `admitted_u32_alias_same_value` additionally assumes two checked claims. Neither theorem connects Zig descriptor validation or Boolean range gates to Lean claims. |
| The decoded-trace false-claim theorem requires ideal exact Gate balance, fixed-cell matches, nine arithmetic roots, producer uniqueness, and public pins. | Coverage gap; blocks a claim of native proof soundness | `UnpartitionedTrace` and `hbalance` are caller premises. There is no theorem from accepted Zig proof bytes and rooted fixed/main commitments to these facts. The raw challenge-pair theorem also assumes canonical event addresses/counts and independent challenges. |
| Mixed general proof bytes expose private endpoints. | High confidentiality impact for the experimental mixed profile; no false-proof result | Both tagged bridge writers fill eight main columns with endpoint words on every row. The accepted-proof opening regression reads those words from every bridge main-column opening. See `REVIEW_MIXED_PRIVATE_ENDPOINT_DISCLOSURE_2026-10-12.md`. |

## Exact checks

The following Lean modules built and passed `leanchecker` in isolated
worktrees using the reviewed commits and the alias parser extension:

```text
S31.Gadgets.Functional.RecordU32BoundaryV2
S31.Gadgets.Functional.Correspondence.OptimizedDecodedTrace
S31.Gadgets.Functional.Correspondence.OptimizedDecodedTraceAudit
```

The audit module separately proves the pinned byte triple is accepted. This
removes the most direct vacuity risk for `hbytes`. It does **not** construct a
trace satisfying `UnpartitionedTrace` and `balanced`, so the full physical
premise remains conditional. The source-to-roster length, partition, distinct
row, and row-bound conclusions follow from checked bytes; their presence next
to the claim theorem must not be read as a native emitter/commitment proof.

The original alias counterexample is now a positive grammar check:

```python
from package.correspondence import parse_source_optimized
source = b"circuit alias_add(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let copy = a; let b = copy + x; b }"
relation, syntax = parse_source_optimized(source)
assert len(relation["nodes"]) == len(syntax["instructions"]) == 2
assert syntax["output"] == 2
```

The Python parser treats `let copy = a;` as an alias with no arithmetic node.
Lean now does the same: `alias_let_inside_modeled_grammar` checks the resulting
two-instruction raw certificate. The stronger
`optimized_alias_exact_byte_triple` checks a separate alias, redundant
parentheses, and CSE source against exact normalized JSON and compact IR
bytes. This closes the specific alias exclusion found in the initial review.
It does not prove that every Python-admitted source is in the Lean grammar,
that Python always emits the modeled bytes, or that native AIR rows agree.

The paired executable fixture is
[`optimized_alias_gap.s31`](../../../formal/s31/fixtures/correspondence/optimized_alias_gap.s31).
Run `python3 formal/s31/scripts/check_optimized_alias_scope.py` from the repo
root to compare the fixture with the Lean literal and check the independent
Python parser against production text compilation. The Lean audit checks
inclusion for this source and exact-byte admission for the second alias
fixture. The decoded-trace claim theorem still requires the stated physical
trace and ideal Gate balance premises.

For the u32 ABI, `packWords` and `unpackWords` use ordinary `Nat` arithmetic.
The low/high bounds (`< 65536`) make the packed value uniquely less than
`2^32`. Zig's `checkClaim` matches this bound and rejects negative or
noninteger JSON words, so no mismatch was found in the integer encoding. The
formal boundary begins **after** Zig's nominal descriptor, relation shape,
canonical digest, and range-gate checks. A `u16` pair and a `u32` leaf can
have the same two proof words; their distinct type/key identity is enforced
outside the new Lean u32 theorem.

## Release interpretation and next obligations

No accepted false proof was found in this review. The proved optimized claim
is valid for its stated, nonempty byte fragment and for any decoded trace
meeting its explicit physical and ideal Gate premises. Keep the v3 optimized
path opt-in. To promote it, prove or independently check the full admitted
source grammar, emitted fixed/main cells and roots, authenticated openings,
AIR/LogUp-to-balance implication, and transcript challenge step. For u32,
connect validated native descriptors and actual two-limb range gates to the
Lean word model. Keep source `private` documented as statement-private only
until the mixed proof profile has a separate zero-knowledge construction.
