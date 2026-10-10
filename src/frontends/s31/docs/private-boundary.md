# Private circuit-to-chip boundary

[`private_step16.s31`](../examples/boundary/private_step16.s31) takes four private M31 words, applies 16 square-then-add rounds in the repeated-step chip, and publishes only their final sum. Its [checked normalized relation](../examples/boundary/private_step16.s31.json) is the byte-exact output of text lowering. [`private_add_square16.s31`](../examples/boundary/private_add_square16.s31) uses add-then-square. [`private_affine_square16.s31`](../examples/boundary/private_affine_square16.s31) puts nonzero scaling and addition on both sides of one square. Build any of these text sources with `--lowering direct-chip`; their packages use the `direct-m31-private-v5` profile, the `s31-verification-key-v5p` schema, and the `S31NAT5P` native proof envelope.

Every admitted source body has exactly one `square`, with zero or more static `add_const`/`mul_const` steps before and after it. It can be written `T(x) = C(Ax+B)²+D`, where `A` and `C` are nonzero in M31. The compiler sets `s = qx+r`, with `q=C A²` and `r=C A B`. One source round then becomes `s' = s²+k`, where `k=qD+r`, exactly the existing chip transition. At the end, the circuit recovers `x=(s-r)/q`. The circuit constrains every multiplication, addition, subtraction, and inverse-scale multiplication at the eight endpoint wires. In the worked affine example `A=3`, `B=5`, `C=7`, `D=11`, so `q=63`, `r=105`, and the chip constant is `k=798`. A zero `A` or `C`, a second square, or `mix4` is rejected for this profile.

The bridge authenticates the eight transformed wire addresses, and the source digest/key bind the source body and derived chip constant. This is an affine conjugation of one fixed chip, with extra circuit gates at the endpoints when scaling or shifting is needed. It does not admit arbitrary nonlinear step bodies or multiple chip calls.

The normalized source fixes the circuit and chip shape. The compiler creates scalar circuit wires for the source input `x`, transformed chip input `s₀=qx+r`, transformed chip output `s_R`, and source result `x_R=(s_R-r)/q`. It records the four `s₀` and four `s_R` addresses during witness-free compilation. When `q=1,r=0`, these can coincide with the source endpoints. The installed key contains the eight chip endpoint addresses. Before native verification, the verifier re-lowers its embedded source, checks all eight key addresses against the new compilation, rebuilds the private-boundary preprocessed circuit, and compares its root and circuit identity hash to the key. The profile tag, source digest, chip parameters, and addresses also enter the proof transcript. The prover reads endpoint values from the corresponding value-circuit wires; callers do not supply addresses or endpoint values through the public statement.

The direct circuit's Gate lookup yields one extra use at each of the eight addresses. The bridge commits eight M31 value columns and consumes those eight `(Gate, address, value)` tuples. It also contributes the opposite indexed tuples for the chip's initial and final states. The chip proves each square-then-add row and its indexed transition lookup. Circuit, bridge, and chip share the same lookup challenges and one STARK proof. The verifier requires their claimed lookup sums to close to zero, then verifies all three AIR components. Tampering with one side of an endpoint connection, a fixed address, or a chip transition breaks that authenticated closure, subject to the proof system's cryptographic assumptions. A different private witness can still produce a valid proof for a matching public claim.

This private source shape currently requires exactly one private `m31[4]` input; its first node must be a `repeat` with the one-square affine body above, containing at most 16 static steps. The round count must be a power of two from 16 through 32768. Subsequent nodes may compute public claims, but the input and repeat output cannot themselves be declared public outputs. The other direct-M31 compiler restrictions still apply. “Private” means the eight chip endpoint values are absent from the public statement and required public output words. It does **not** mean witness secrecy: the bridge repeats transformed endpoints in committed trace rows, and an opening of `s₀` reveals the original input exactly as `x=(s₀-r)/q` because `q` is nonzero and public through the source. A confidential profile needs a different blinded bridge and a separate privacy analysis.

The focused [proof test](../tests/proofs/private_boundary_proof_test.zig) verifies the square-then-add source proof natively, checks transformed endpoint values for both other examples, and rejects changed public words, source digest, and boundary addresses. The [package acceptance test](../tests/acceptance/acceptance_private_boundary.py) runs all three examples through sealed package builds and native verification. It rejects changed private inputs, public aggregates, source files, input and output key addresses, chip constants, and proof bytes. It also rejects a degenerate affine body before packaging.

The next boundary abstraction needs a compiler-owned list of chip calls with explicit relation IDs, endpoint tuples, wire addresses and multiplicities. The generated manifest must bind that list and its ordered component/lookup-sum roster to the key and transcript. A chip for each new step body needs a separate AIR transition and degree/mask review; multiple calls need per-instance row domains or an indexed shared chip, complete multiset closure, and adversarial omission/duplication tests. The released one-call bridge has eight fixed columns and one chip endpoint pair.

## Experimental two-call source binding

The [two-call normalized example](../examples/boundary/private_pair16_32.s31.json)
has two private `m31[4]` inputs. Call 0 performs `x²+13` for 16 rounds; call 1
performs `x²+17` for 32 rounds. Two ordinary circuit nodes publish the
lane-wise **sum and product of the final states**. The first row of lane 0 is
easy to check by hand: `3²+13=22` for call 0 and `2²+17=21` for call 1. The
last rows, rather than the first rows, feed the two public four-word arrays.
The [assignment](../examples/boundary/private_pair16_32.valid.json) gives
the eight resulting public words.
This milestone accepts normalized version-1 `.s31.json` source only. The
current text frontend emits one public output for a version-1 circuit;
multiple named output leaves use the version-2 public record ABI. Text syntax
for this pair profile stays gated until that ABI and the pair verifier agree.

| Lane | Left input | Right input | Left after 16 rounds | Right after 32 rounds | Public sum | Public product |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 3 | 2 | 532178712 | 1185857477 | 1718036189 | 832988171 |
| 1 | 3 | 4 | 532178712 | 854449153 | 1386627865 | 1177026897 |
| 2 | 7 | 6 | 2108197386 | 1535612364 | 1496326103 | 1841741547 |
| 3 | 11 | 8 | 1611365775 | 1883997554 | 1347879682 | 1786834280 |

Every cell from the fourth column onward is modulo `p = 2147483647`.
For example, lane 0's public sum is
`(532178712 + 1185857477) mod p = 1718036189`; its public product is
`(532178712 × 1185857477) mod p = 832988171`. The source evaluator, the
value-circuit output wires and a separate integer recurrence oracle must all
agree with these eight public cells.

This is an intentionally narrow initial source profile: exactly two private
four-lane inputs; exactly two `square; add_const` repeats with power-of-two
lengths 16–32768; then exactly the sum and product nodes. It excludes affine
changes of variables, extra repeat calls, assertions, public inputs, and
blinded proof mode. Unsupported shapes fail at source admission. The compiler
assigns call IDs 0 and 1 in source order and records each call's eight actual
circuit wire addresses. Value and witness-free compilation must produce the
same Plan and preprocessed root. This is tested without accepting caller
supplied addresses.

The corresponding native proof experiment has five AIR components:

| Proof index | Component | Raw rows here | Main columns | Interaction columns | What it proves |
| --- | --- | ---: | ---: | ---: | --- |
| 0 | direct circuit | source-dependent | 12 | 8 | Circuit arithmetic, eight public words, and Gate yields at each endpoint address |
| 1 | chip 0 | 16 | 9 | 8 | 16 rows of `out=in²+13` and indexed state links tagged call 0 |
| 2 | chip 1 | 32 | 9 | 8 | 32 rows of `out=in²+17` and indexed state links tagged call 1 |
| 3 | bridge 0 | 16 | 8 | 20 | Circuit endpoints equal chip 0's first and last states |
| 4 | bridge 1 | 16 | 8 | 20 | Circuit endpoints equal chip 1's first and last states |

The circuit still compresses its six-field `(Gate,address,value,0,0,0)`
tuple. Each chip uses a seven-field
`(Chip,call_id,step,lane0,lane1,lane2,lane3)` tuple. Both tuple types use the
same Fiat–Shamir pair `(z,α)`. Each bridge is a constant row table: eight
cyclic equalities require its endpoint values to stay the same in all 16
rows, while five LogUp fractions consume eight Gate endpoints and return the
opposite chip endpoint terms. All five claimed sums must close to zero.
The preprocessed Gate multiplicity counts **each occurrence** of a repeated
wire address; two appearances of one address still read one coherent circuit
variable.
In the current direct manifest, `source_index=1` names the official
`qm31_ops` bundle component while `source_index=0` is a sentinel for each
native chip or bridge, whose Zig source hash is stored separately. The
fail-closed `ComponentSource` interpretation checks the exact pair roles and
native program names, including the two canonical call IDs. The numeric wire
field remains versioned legacy syntax; a variable-component scheduler needs
a first-class serialized source kind.
As in the one-call profile, “private” means absent from the eight public
output words. The bridge commits endpoint values and trace openings can
reveal them; this profile makes no witness-secrecy claim.

[`pair_source_binding.zig`](../runtime/pair_source_binding.zig) now derives
the Plan, preprocessed root, exact five-component roster, and typed V3
manifest precommitment from source alone. The manifest commits ordered call
IDs, rounds, constants, endpoints, offsets, columns, AIR source bindings, and
lookup relation IDs. Its circuit hash is excluded from the precommitment to
avoid a hash cycle; the engine's pair-specific effective digest includes the
true source hash and this precommitment before the first trace commitment.
Rebuilding from sealed source rejects a resealed but changed in-memory plan.
The focused source test also changes only a component's metadata, recomputes
the precommitment, and shows why compiling the witness alone is insufficient:
the Plan and root still match, but full manifest reconstruction rejects it.
The staged `proveSealed` and `verifySealed` paths perform that source-binding
check before writing or decoding proof bytes. The circuit identity is checked
separately because it is purposely outside the manifest precommitment.

The experimental source-pinned command-line pair is built directly from the
normalized source:

```sh
cd src/frontends/s31
zig build install -Doptimize=ReleaseFast -Ds31-version=1 \
  -Ds31-lowering=direct-pair \
  -Ds31-source="$PWD/examples/boundary/private_pair16_32.s31.json" \
  -Ds31-name=private_pair16_32
zig-out/bin/s31-private_pair16_32-pair-prover \
  examples/boundary/private_pair16_32.valid.json /tmp/pair.proof /tmp/pair.statement.json
zig-out/bin/s31-private_pair16_32-pair-native-verifier \
  /tmp/pair.proof /tmp/pair.statement.json
```

The verifier executable embeds the source and official AIR bytes. Its caller
supplies only the proof and a JSON statement with schema
`s31-pair-public-words-v1` and eight `public_words`; it cannot supply a
different source or key at verification time. The internal `verifySealed`
helper still accepts explicit source/key bytes for testing and package
assembly. A 16+32-step native proof and a 1024+4096-step trace-lifting proof
pass; malformed envelopes, source/key/manifest mutations, changed public
words, noncanonical proof varints, and changed proof bytes are rejected.

**Release status:** this remains an experimental fixed two-call profile. The
AIR/LogUp/PCS verifier has not been reduced to the exact tagged event-balance
premise used by the Lean path theorem, and no witness-secrecy claim is made.
The fixed V3 profile remains separate from the experimental bounded V4
profile below; their proof magics and public statement schemas differ.

## Experimental bounded V4 native envelope

V4 admits 1–8 canonical `square; add_const` calls with power-of-two round
counts, compiler-derived private endpoint wires, and exactly eight public M31
words. The [one-call example](../examples/boundary/private_many1.s31.json)
publishes `r+x` and `r*x` as two four-lane arrays. Its proof has three
components: direct circuit, chip 0, bridge 0. A three-call proof has seven
components; in general the order is **circuit, all N chips, all N bridges**.
The native scheduler commits one main tree and one interaction tree with
widths `12+17N` and `8+28N`. It mixes exactly `1+2N` claimed sums in that
same component order. The Gate and tagged-chip lookup sums must close to zero.
The preprocessed tree always has eight columns, and the fourth tree is the
composition tree.

The byte envelope begins with the distinct eight-byte magic `S31MNY04`,
then one byte each for N and `1+2N`, two zero reserved bytes, three 32-byte
digests (source, typed manifest precommitment, circuit identity), one
little-endian `u64` interaction nonce, `1+2N` canonical four-limb QM31 sums,
and one canonical postcard STARK proof. Each limb is a little-endian `u32`
strictly below `p`. There are no unused sum slots on wire. The verifier checks
the length, magic, count relation, reserved bytes, and source-derived digests
before proof decoding. It recompiles the embedded source without witness,
checks the endpoint map and fixed-column root, reconstructs the actual AIR
handles and PCS geometry, validates the postcard shape against the roster,
and decodes under a bounded allocator. The eight public words are provided in
a separate `s31-many-public-words-v4` statement and mixed into the transcript
before the main commitment.

Build the source-pinned one-call binaries with:

```sh
cd src/frontends/s31
zig build install -Doptimize=ReleaseFast -Ds31-version=1 \
  -Ds31-lowering=direct-many \
  -Ds31-source="$PWD/examples/boundary/private_many1.s31.json" \
  -Ds31-name=private_many1
zig-out/bin/s31-private_many1-many-prover \
  examples/boundary/private_many1.valid.json /tmp/many.proof /tmp/many.statement.json
zig-out/bin/s31-private_many1-many-native-verifier \
  /tmp/many.proof /tmp/many.statement.json
```

The verifier binary embeds source and official AIR bytes. A caller choosing
which verifier binary and public words to trust is outside this protocol.
The current proof and verification implementation passes native N=1,2,3,4,8
tests, including call ID 7, count/roster and every claimed-sum position
mutations; counts 5–7 still need direct native proof tests. The source-derived
manifest names relation dependencies by reviewed AIR kind; the live preflight
introspects widths, masks, degree and fixed-column indices, but does not
discover lookup relation IDs from evaluator formulas. A full compiler-to-AIR
correspondence proof, independent V4 soundness review, and external prover
interoperability remain release gates. The profile is transparent: committed
bridge rows can expose private endpoint values. No zero-knowledge or witness
confidentiality claim is made.
