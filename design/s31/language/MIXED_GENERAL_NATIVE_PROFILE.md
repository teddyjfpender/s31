# Bounded general mixed native proof profile

Status: **draft isolated profile; native compilation, proof acceptance and CI
must pass before admission**. The fixed N=3 and N=4 profiles retain their
existing transcript tags and proof bytes. This profile extends their source
derived pair/many composition to one through eight calls with its own
transcript tag `0x5333314d49580301`, `V3` identity domains, and `S31MIX07`
proof envelope.

## Source and proof contract

The current source shape has one four-lane M31 input, one to eight
`square; add_const` repeat calls, and two four-lane public output leaves. The
circuit exposes eight public M31 words and its internal public unit value;
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

The native engine and source-pinned wrapper tests prove and verify all eight
call counts and mutate public values, claims, unused sums, roles and header
identity. The black-box CLI suite additionally checks every call count,
independently recomputes the generated manifest digest, mutates every
serialized claim, rejects changed sources and malformed public statements,
and checks incorrect witness or output assignments. The dedicated CI job
must run those tests on the pinned engine revision. An independent static
review found no concrete source-authentication flaw in the draft, but it did
not compile or execute native proofs. The 1–8 call lookup compression bound
is conditional on source output shape and the stated AIR, transcript and
public-output admission assumptions; it is not a global STARK soundness
claim. Full compiler correspondence and cross-profile security analysis
remain separate obligations.
