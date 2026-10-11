# Fixed mixed N=4 native proof profile

Status: **source-pinned, proof-backed experimental profile**. The source
inspector and witness audit alone do not admit proofs; `n4_package.zig` and the
`direct-mixed4` binaries use a distinct native prover, transcript, envelope,
and verifier.

The only supported roster is circuit, pair chip 0, pair bridge 0, pair chip 1,
pair bridge 1, many chip 2, many bridge 2, many chip 3, many bridge 3. This
gives nine AIR claims. The source compiler fixes call order, rounds, constants,
and all input/output addresses. The selected live schedule fixes widths,
trace and evaluation logs, masks, fixed indices, composition split, and PCS
tree geometry. The verifier rebuilds these from embedded source and pinned AIR
bytes before decoding a bounded proof. The engine adapter's caller-supplied
manifest digest is never standalone verifier authority.

N=4 uses transcript profile tag `0x5333314d49580201`, circuit identity and
manifest domains ending in `V2`, and envelope magic `S31MIX06`. The header
also carries call count `4`, sum count `9`, and schema bytes `02 00`. The
envelope carries exactly nine canonical QM31 sums; the
in-memory borrowed verifier rejects nonzero unused backing-array entries.
The preprocessed root, public words, main and interaction commitments, lookup
challenge, nine claims, and PCS openings enter the same ordered native
prover/verifier transcript. The sum of the circuit public lookup claim and all
nine component claims must vanish; each AIR must also constrain its own claim.

Admission controls mutate every sum, a compensating chip/bridge sum pair,
call order, source constant and endpoint, a role/descriptor, public words,
PCS geometry, commitment roots, envelope version, and cross-profile replay.
An honest native prove/verify and these rejection tests establish the tested
fixed N=4 profile. They do not establish general composition soundness
or a complete compiler correspondence theorem.

`private` denotes source visibility. The committed base trace is unblinded,
so this profile makes no witness confidentiality claim. V3/V4 and mixed N=3
proof and transcript bytes remain unchanged.

The tested four-call source has eight fixed, 80 main, and 120 interaction
columns, with nine AIR components. Its deterministic ReleaseFast proof is
110,020 bytes with SHA-256
`408ff6a32b9374ea92a8a086ffc4b2ef0114749a2f9b2a09b4e5adb9b849aade`.
This fixture detects any unintended byte or transcript change. A single local
timing is descriptive, not evidence of a speedup or cost-model validity.
