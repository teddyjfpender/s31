# Bounded general mixed native proof profile

Status: **v1 native local acceptance passed for N=1..8; v2 public record
acceptance passed at N=1 and N=8; CI and full soundness review remain open**.
The fixed N=3 and N=4 profiles retain their
existing transcript tags and proof bytes. This profile extends their source
derived pair/many composition to one through eight calls with its own
transcript tag `0x5333314d49580301`, `V3` identity domains, and `S31MIX07`
proof envelope.

## Source and proof contract

The version-1 source shape has one private four-lane M31 input, one to eight
`square; add_const` repeat calls, and two four-lane public output leaves. A
narrow version-2 shape instead has one **public record** input containing
four M31 words and one derived public record result containing four M31
words. The native verifier derives the canonical eight-word projection from
the embedded v2 ABI descriptor and typed statement. Both shapes expose eight
public M31 words and the circuit's internal public unit value;
the latter makes the native output array nine values. The source inspector
rebuilds the call order, rounds, constants, input and output addresses, the
fixed root and the live selected geometry. The generated typed registry
manifest has one circuit entry followed by a chip and bridge entry for every
call. Calls zero and one use pair AIRs; later calls use many AIRs. Thus the
component count is exactly `1 + 2N` and is at most 17.

The typed registry manifest digest is the proof profile's
`manifest_sha256`. It covers the selected source and canonical IR, each
call's endpoints and parameters, every component's role, registry identity,
relation IDs, proof and claim index, AIR source, bound program, column spans,
constraints and preprocessed indices. The verifier derives it from its
literal embedded source and pinned AIR bundle. A manifest supplied by a
proof or an application cannot select the roster.

The proof header carries magic, call and claim counts, version `03 00`,
source digest, registry manifest digest, circuit identity, interaction PoW
nonce and exactly `1 + 2N` canonical QM31 claimed sums. The native verifier
rebuilds source and geometry before bounded postcard decoding, rejects a
noncanonical or mismatched header and any nonzero unused claimed-sum entry,
checks the circuit's eight public values and all component handles, and then
verifies the shared native PCS proof. The circuit public lookup term plus all
component claimed sums must close to zero. The challenge, claims, three
trace commitments, fixed root, public values and PCS openings share the
ordered transcript. A bare engine API remains caller-scoped: only the S31
`verifyEmbedded*` entrypoint supplies source authority.

`private` is a language visibility marker. The committed base traces are
unblinded and this profile makes no witness confidentiality claim.

## Release gates

On the pinned engine revision `7d544c6839497ca19b6c7ef9b982e464f10cfeed`,
three selected engine tests passed, including the general N=1..8 native
proof and mutation cases. The source-pinned wrapper tests passed for all
eight call counts, and the black-box CLI suite passed each call count with
source binding, malformed-statement, wrong-assignment and changed-claim
controls. That suite independently recomputed the generated manifest digest
from its JSON fields. The legacy N=3 and N=4 native suites also passed.
The version-2 public record slice has separate local native proof and
mutation acceptance at N=1 and N=8. Intermediate v2 call counts share the
bounded profile but have not been separately exercised by that focused gate.

These are **local** results. The dedicated CI job must still pass on the
pinned revision before release admission. The independent static review
found no concrete source-authentication flaw in its reviewed draft; its
original scope did not include the later native runs. The 1–8 call lookup
compression bound is conditional on source output shape and the stated AIR,
transcript and public-output admission assumptions; it is not a global
STARK soundness claim. Full compiler correspondence and cross-profile
security analysis remain separate obligations.
