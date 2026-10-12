# Fixed-call geometry is variable in the admitted mixed profile

The V4–V8 cost cohorts varied call count but stayed at 16 rounds per chip and
under the circuit trace's 512-row floor. Their column widths and constraint
counts were exact functions of call count. That does **not** mean all live
geometry is fixed by call count. Two unscored, manifest-only builds isolate
the two independent trace-height dimensions at **one chip call**:

| Source | Circuit gate change | Chip rounds | Circuit trace log | Chip trace log | Max / composition log | Columns `[pre,main,interaction,quotient]` | Constraints |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: |
| V8 `folded_seed_n1` baseline | ordinary short circuit | 16 | 9 | 4 | 9 / 9 | `[8,29,36,8]` | 30 |
| [Gate probe](language/mixed-cost-v9-feasibility/gates256.s31.json) | 256 live `mul` nodes feeding chip | 16 | **10** | 4 | **10 / 10** | `[8,29,36,8]` | 30 |
| [Chip probe](language/mixed-cost-v9-feasibility/rounds1024.s31.json) | same short circuit | 1,024 | 9 | **10** | **10 / 10** | `[8,29,36,8]` | 30 |

Each manifest reports one call and three slots. The [gate
manifest](language/mixed-cost-v9-feasibility/gates256-manifest.json) binds
source SHA-256
`231abad677f05648ba7000760121bf6795a20066eb17d3dfc3e29f6cb9341d5f`;
its raw manifest SHA-256 is
`f58d931fb5022953294c1ba36b317db8c5791d11d00c33dd6857bfcea6a2f2c1`.
The [chip
manifest](language/mixed-cost-v9-feasibility/rounds1024-manifest.json) binds
source SHA-256
`af67784a4b44662b67aac2f52369370138609e5a4e3390b0fe15faf7c9fa6977`;
its raw manifest SHA-256 is
`3fd049d3260a5def0593af6c1c14f2efba2f4d3c08220469f0e28435505a9dfe`.
The baseline comes from the committed
[V8 result](language/mixed-cost-v8-calibrated-result.json), whose source SHA
is `51b07cc02132ada162448361df633a1de56b67ed7e223e7edfe70b68f929332e`.

The circuit probe inserted a dependent multiplication chain before the chip;
every node lies on the chip input path and survives source admission. The
chip probe changed only the repeat count from 16 to 1,024 and source name.
Both were packaged with `direct-mixed-general`, `ReleaseFast`, S31 source
version 2, and `-j1`; their packaged manifest binaries were run without any
proof timing. Thus the data establish **independent circuit and chip trace
height variation**. They do not establish an independent column-width or
constraint-count effect in this architecture, nor the cost of either change.

V9 uses three fresh heldout sources and claims to score the previously frozen
V8 cost model against gate-only, chip-only, and combined changes. Its score
will be a prospective out-of-domain stress test, not a fit on these probe
manifests. A model that needs geometry-sensitive coefficients will require
clean training data and a further fresh heldout transfer.
