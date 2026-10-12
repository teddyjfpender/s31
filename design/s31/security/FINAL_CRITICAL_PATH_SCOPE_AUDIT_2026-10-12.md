# Final critical-path scope audit

Reviewed the shared branch at `a6cdd81` in an isolated worktree. I found no
new blocker in the four bounded claims below. This is an independent scope and
artifact consistency review, not a new proof of the native verifier.

| Claim | What the implementation establishes | Remaining premise or limit |
| --- | --- | --- |
| Derived Gate roster | `AliasDerivedGateMultiplicities.check` erases supplied island multiplicities, derives all island counts from the scheduled reads and nine public feeders, checks projected counts, and checks the exact Gate ledger. `DerivedRosterArbitraryTrace.checked_roster_arbitrary_trace_claim` covers all 512 fixed rows and concludes the source result for any trace satisfying its premises. | The arbitrary trace still requires fixed-row agreement, local arithmetic, unique yields, designated basis events, public pins, and ideal Gate balance. Neither theorem derives these from native verifier acceptance. |
| Fixed-root package join | `fixed_root_join.check` admits an externally pinned package snapshot, reconstructs its source certificate, recommits all 4,096 fixed words through the native PCS path, requires the sealed key root, and requires one native-accepted proof to carry that root. | Pins, local executable integrity, and native PCS/FRI remain trusted. The copied proof and statement are checked after verification for persistent changes; the check does not establish atomic read isolation against a same-user process. |
| Mixed manifest geometry | `registry_manifest.requireNativeGeometry` checks the ordered slot and column spans, relation IDs, local source hashes, mask-width bounds, tree widths, and PCS lifting heights. `requireSource` rebuilds the manifest from literal source, and the verifier reconstructs native handles. | The manifest report is diagnostic, not a verifier key. The local geometry check alone does not authenticate exact mask points or prove the installed AIR, field arithmetic, or PCS sound. |
| V24 conditional-repeat cost result | The committed protocol, source, result, and score hashes match. Forty-two trials form 21 adjacent same-claim pairs with identical assignment, statement, and proof hashes; all 42 changed-result controls are recorded as rejected. Independently recomputing each repeat prediction as the first proof's measured FRI and interaction PoW plus the frozen 150.346 ms non-PoW center gives the committed 5.83% median relative error and 21/21 hits within 35%. The reported build-plus-process-duration sum recomputes to 88,328,675,412 ns. | The repeat prediction is conditional on the preceding proof's measured PoW. This is one prospective topology and one host, with two documented pre-native tool/compiler-pin amendments. It does not reverse the V17/V23 failures or establish cross-host calibration or a Cairo speedup. |

I inspected the relevant Lean theorem statements, Python join and release
admission code, Zig manifest binding, V24 frozen artifacts, and their existing
independent reviews. The read-only V24 calculation above did not rerun proof
timing. No native runtime or compiler source was changed for this audit.
