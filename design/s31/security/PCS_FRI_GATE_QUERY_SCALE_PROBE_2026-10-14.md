# Gate query-scale probe: 70 and 232 raw draws

**Status:** engineering measurement only. It supplies no PCS/FRI security bits
and does not change v0.1 release admission.

The [exact paper arithmetic](PCS_FRI_STWO_UDR_FEASIBILITY.md) rules out the
current 70-draw Gate profile as a proven 96-bit paper work-factor profile by
the published ungrinded expression. This probe asks what one 232-draw native
Gate proof costs. The two runs use the same `arith4_m31.s31` text, assignment,
canonical IR (`825cc34485c9229df85640c07c47619fe1f58b3795c0951a0413c8501b13dfe3`),
Stwo gitlink (`59e1f115250b8af01712b9bf3d71616e53094964`), blowup two,
single-step FRI, and 26 native PoW bits. Zig builds used at most four jobs.

The 232-draw run changed the native runtime's two FRI constructors, emitted
key metadata, and key validator from 70 to 232 in a disposable worktree based
on S31 `245e2ce2`. The ordinary package build rejected this profile during
`fold-keygen` with `UnsupportedFixedFoldGeometry`: its recursive verifier
topology does not fit the fixed-fold layout. For the **base Gate PCS measurement
only**, the disposable worktree skipped fixed-fold key generation and the
package check that requires that fold key. It retained the native base proof
and verifier, key check, proof acceptance, independent value oracle, and
changed-public-claim rejection. This temporary package is **not** a valid
release package and was not committed.

| Raw draws | Base proof bytes | Median prove process wall | Median native verify process wall | Base verification |
| ---: | ---: | ---: | ---: | --- |
| 70 | 438,157 | 0.605 s | 0.087 s | accepted; changed claim rejected |
| 232 | 1,212,933 | 0.537 s | 0.128 s | accepted; changed claim rejected |

Each median is from five fresh prover and verifier processes using the same
already-built package, measured sequentially on the same host. Each profile
produced one deterministic proof across its five runs. Proof size rose **2.77×**;
native verification wall rose about **46%** in this small sample. The lower
observed prove wall at 232 is not evidence that more queries prove faster:
the profiles have different deterministic PoW searches, and these five
process timings do not isolate query work. The cold build and first-use runs
also varied; they are excluded from these medians. Proof SHA-256 values are
`c654ef1656ca0f983d779c609459cbe62f4195fd6a9dcd3cbd1d309095d2cb59`
for 70 and `9763ec18489cd410d656c5b872eac7a05d5abacf62b22854cee367b110e02277`
for 232.

The result exposes three independent requirements before raising queries in a
release profile: bind the reported key tuple to the actual native FRI config,
make recursive fixed-fold geometry accommodate that tuple, and complete the
native verifier-to-published-theorem reduction. Even 232 draws by themselves
do not prove the complete bound or close any [release obligation](pcs-fri-v01-blockers.json).
