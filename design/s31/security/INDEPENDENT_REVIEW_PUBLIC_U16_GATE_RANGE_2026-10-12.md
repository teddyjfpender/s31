# Independent review: public `u16` record input in direct Gate

**Scope.** This review covers the record ABI v2 public `u16` input and alias-result path with **direct-gate** lowering. I found no soundness blocker in that scope, conditional on the Gate lookup and polynomial commitment assumptions below. It is not a claim about arbitrary `u16` expressions or other proving profiles.

## Inspected state

The shared worktree was at `31b1ed34c057b4fd22968bfbd2cc88590e244e10` when inspected; the public-`u16` edits were **uncommitted**. The engine gitlink was `fde847ea374ade2ae07ef5b3a42ba07e15655b64`. SHA-256 pins for the inspected bytes:

| File | SHA-256 |
| --- | --- |
| `src/frontends/s31/language/record_abi.zig` | `81f71820db5c648c60a92eb78b82a4a4296536ed7c05a94aaf62e7700cbb7d27` |
| `src/frontends/s31/language/relation_compiler.zig` | `7a1c8047468eef045e56eff786ec31c49a980f387f2e824bf94dbe481445bd6c` |
| `src/frontends/s31/language/bounded_call_admission.zig` | `f757b0e5e224cc2c62f2b3cb8b48b61ffcb1f560d9a00d76705bb20ad9f76043` |
| `src/frontends/s31/language/gadgets/integer_bits.zig` | `18e880ba7a96f958810d041939e35ba9fa2fc2d0226f98e5a574158e696e853d` |
| `src/frontends/s31/python/abi/binding_v2.py` | `7db2afa1702b120ad819dcec22e4a5809e458168f8d465765d8d4b016a07c48a` |
| `src/frontends/s31/python/package/context.py` | `39a7f9f234d5fd8746d0778dc82fd43383d12c73a2884cc31a0d526ad9debe7d` |
| `src/frontends/s31/tests/acceptance/record_abi/public_u16_direct_gate_v2.py` | `72ea6dd909d5909c1c524e3a0d293ac0382479d049b8d59c1adb4845cb79f41f` |
| `deps/stwo-zig/src/frontends/circuit/air_eval/manual/circuit.zig` | `574d6213cf1f15bce3e14884addc6a29701ed47782199ab5da66cf1a8bec1a50` |
| `deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig` | `72f00e3e4f6481cae641a48a8507e733c95f97a15963149027a6488fc46d2d7c` |
| `deps/stwo-zig/src/frontends/circuit/witness/direct_arithmetic.zig` | `262b15126286fc72f9c9c962e78b632e4d758367291b4efdc328195dd364c91d` |

The Lean files inspected at this state were `RecordAbiV2.lean` (`1cdbc550ef3d577af32aaee483e98c00c3274ed8a0e15fcfd0383fed3cc777d3`) and `RecordDescriptorValidationV2.lean` (`49b4aeb588d5429d82635fb5d556114815151d2305c38d9b024adacef3a8aebe`), both under `formal/s31/S31/Gadgets/Functional/`.

## Constraint argument

For each 16-bit input word `w`, `decomposeWordArithmetic` allocates bits `b_0,...,b_15`, emits a self-product `mulInto(b_i,b_i,b_i)` for each, reconstructs `r = Σ 2^i b_i`, and emits a self-loop addition `addInto(a,r-w,a)`. In the Gate AIR, fixed opcode/address/multiplicity columns select each arithmetic row; all four destination coordinates must equal the selected operation. Thus the self-product enforces `b_i²=b_i` and the self-loop addition enforces `a+(r-w)=a`, hence `r=w` in the field. Each Boolean root is 0 or 1. Consequently `0≤r≤2^16−1=65535<p=2147483647`; the equality has no alternative canonical M31 representative from modular wrap. The witness initializer choosing bits from `w` does not supply this argument; the constraints do.

The Gate relation adds input address/value tuples and subtracts output address/value tuples according to fixed multiplicities. The compiler checks `firstYieldViolation`, requiring a single producing gate for each variable. Under sound lookup balancing, repeated uses of an address must carry the producer's value, including both operands and the destination of each self-loop gate. This uses the ordinary Gate LogUp relation. **No fixed 16-bit range table is needed or used**; fixed Gate layout/opcode/address columns still apply.

The record descriptor binds a `u16` input to a public raw wire. Native and Python statement checks require each word to be below 65536 and enforce alias consistency. Direct-gate compilation applies the arithmetic decomposition to each such word; `u16` result leaves must alias public `u16` input wires. These admission and statement checks are necessary parts of this scoped claim, separate from the AIR equations.

## Assumptions, exclusions, and controls

An accepted proof implies this conclusion only up to the protocol's soundness error: correct binding of fixed Gate columns and public inputs, Gate lookup/LogUp soundness, FRI/PCS low-degree and commitment binding, and transcript challenge generation. This review does not establish a deterministic accepted-proof-to-full-trace extraction theorem or the full Lean compiler-to-AIR correspondence. The inspected Lean lemmas cover descriptor/range facts, not that end-to-end theorem.

The reviewed feature excludes private `u16` record leaves, derived `u16` result leaves, bounded mixed admission, and direct-chip packaging. The Python package admission accepts the reviewed record shape for direct-gate; its direct-chip source check requires one public four-lane M31 repeat. Native direct-chip behavior outside that packaging check was not audited here. Older record ABI v1 paths and non-record arithmetic `u16` operations are outside scope.

I read the acceptance control `public_u16_direct_gate_v2.py` and ran its static mode: `python3 -B src/frontends/s31/tests/acceptance/record_abi/public_u16_direct_gate_v2.py`. It passed boundary values 0 and 65535, rejected 65536 and `p−1`, and reported 16 range gates per input word. The script contains native honest-proof, changed-public-claim, and out-of-range assignment controls; I did not independently run its native mode for this review. No new test was added.
