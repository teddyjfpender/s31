# Sealed packages

`context.py` owns repository paths, source hashes, the compiler fingerprint,
source lowering and public ABI metadata. The fingerprint includes the CLI,
every Python implementation file in this directory, the language, library and
inspection modules, the Zig sources, pinned AIR assets, the pinned engine
commit and the Zig version.

`source_identity.py` resolves that engine commit. A normal checkout must have
its **own** stwo-zig Git worktree; Git's fallback to an enclosing S31 checkout
is rejected. A complete Git-free release bundle instead carries
`SOURCE-BUNDLE.json`. Before using its engine commit in the fingerprint, the
compiler hashes the engine's build code and relevant vector assets and
compares them with the manifest. It also requires the computed compiler
fingerprint to match the bundle manifest. A missing or edited covered build
file fails package creation. The release asset's external SHA-256 remains the
distribution trust pin; this local consistency check is not an attestation.

`build.py` compiles a JSON relation or `.s31` source into a staging directory.
It checks the compiler and source identities before atomically installing a
package. A text package also contains the original source, its normalized
relation, source map, typed interface and standard-library lock. Before
publishing a text package, it runs complete package verification; direct-gate
packages also require the installed native verifier's `check-key` preflight.

`verify.py` checks the manifest, artifact hashes, source-to-relation lowering,
library lock, verification keys, AIR identifiers and profile-specific recursive
keys before package data is used by the CLI. This is **package integrity**, not
a proof check: the installed native verifier checks a proof and public claim.
The `verify` CLI command reads a private checked copy of an unpinned
package. The standalone native verifier does not read the Python
correspondence certificate.

`lean_effects_admission.py` provides a separate opt-in gate for bounded
effectful text packages. `verify-effects-lean` requires externally supplied
SHA-256 pins for the package source, text, key, prover, verifier, and the Lean
checker executable. It snapshots these inputs, asks Lean to check exact
source/certificate/relation/ABI bytes, then asks Lean to check the exact
canonical assignment and public statement bytes. The same captured public
statement is given to the installed native verifier. This command requires a
`linear-ssa-m31-effects-v1` source relation certificate and rejects all other
profiles. The supplied private assignment is checked against the source, but
the native proof is bound only to the public statement; it may use a different
private witness that yields the same public claim. The checker path must name
a regular file through directories without symlinks. For example:

```sh
s31 verify-effects-lean PACKAGE PROOF ASSIGNMENT \
  --statement PROOF.statement.json \
  --lean-checker PATH/TO/s31-general-linear-effects-package-check \
  --lean-checker-sha256 EXTERNALLY_TRUSTED_CHECKER_SHA256 \
  --source-sha256 EXTERNAL_SOURCE_SHA256 \
  --text-sha256 EXTERNAL_TEXT_SHA256 \
  --key-sha256 EXTERNAL_KEY_SHA256 \
  --prover-sha256 EXTERNAL_PROVER_SHA256 \
  --verifier-sha256 EXTERNAL_VERIFIER_SHA256
```

The exact scope and remaining native proof obligations are in the
[Lean gate note](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/GeneralLinearSSAEffectsPackageCheck.md).

`trust.py` checks externally supplied SHA-256 pins for the normalized source,
key, prover and verifier before full package validation; a text package also requires
the exact `.s31` source pin. The `verify-pinned` CLI command uses this admission
on a private package snapshot immediately before native verification. Pins
obtained from the package itself provide no authentication. A trusted release
channel must supply them; the verifier executes from the checked snapshot.

`release_admission.py` exposes `bounded_direct_gate_snapshot(package, pins)`
for a stricter, opt-in release path. It requires all five externally supplied
pins, the v2 direct-gate key, a rooted correspondence certificate that the
independent checker recomputes, and a successful native `check-key` preflight.
The `verify-release PACKAGE PROOF` CLI command uses this gate and requires
`--source-sha256`, `--key-sha256`, `--prover-sha256`, `--verifier-sha256`, and
`--text-sha256` from a trusted release channel.
Verification callers must use the yielded snapshot while its context is open.
General direct-gate text packages remain buildable; programs outside the
bounded certificate grammar fail this stricter admission. This gate still
inherits the certificate's stated AIR/PCS and native implementation assumptions.
For admitted public four-lane programs, the separate
[pinned public trace audit](../../tools/audit/README.md) verifies one proof and
compares every source-derived Gate base cell with its native public export and
recommits those cells against the accepted main commitment. It is optional,
so ordinary `verify-release` does not pay for rebuilding a public trace.
The v2 grammar now includes up to eight pure static functions with zero to two
parameters, of type `[m31; 4]` or unary
`Fn([m31; 4]) -> [m31; 4]`, and either result type. It accepts bounded bodies of add,
pointwise-multiply, and earlier-declared function calls. Their calls are
independently expanded to existing circuit wires and fresh generated wires before the
same positional SSA, topology, fixed-root, and key checks. The
[release acceptance](../../tests/acceptance/compiler_correspondence/functional_release.py)
compares the function with handwritten gates, proves the function package,
passes `verify-release`, and rejects a changed public claim. The independent
helper parser lives in [source_fragments](source_fragments/README.md) and is
included in the compiler fingerprint.
The same release grammar accepts a bounded lexical `let name = e in body`
inside a circuit let. Its independent parser tracks shadowing and exact
anonymous `_s31_N` wire allocation; the
[lexical release acceptance](../../tests/acceptance/compiler_correspondence/lexical_release.py)
compares the functional and direct AIR, proves the claim, and exercises
`verify-release` and changed-claim rejection.
Named unary functions can also be bound as source-only values and passed
through `Fn` parameters. The
[higher-order release acceptance](../../tests/acceptance/compiler_correspondence/higher_order_release.py)
requires the function value to disappear completely: its package has the
same normalized relation and native AIR geometry as two handwritten gates,
passes `verify-release`, and rejects a changed public claim.
The [captured-lambda release acceptance](../../tests/acceptance/compiler_correspondence/closure_release.py)
additionally checks a unary lambda with a bounded arithmetic and lexical-let
body. Its lexical capture is resolved at function creation, and passing the
closure through a `Fn` parameter adds no relation or AIR node. A later lexical binding with the
same name leaves the captured wire unchanged.
An [inline-lambda release example](../../examples/functional/release_inline_lambda4/README.md)
passes a lambda directly to a `Fn` parameter and invokes it twice. Its
independent certificate checks the exact two-gate result and native AIR
geometry against handwritten arithmetic.
The [curried release example](../../examples/functional/release_curried4/README.md)
returns a captured unary function from a named helper and applies it directly
as `make(x)(x)`. The independent certificate requires only the two handwritten
gates and the matching native AIR geometry.
The [nested release example](../../examples/functional/release_nested4/README.md)
passes both a computed `Fn` value and a computed array value as arguments.
Nested calls are expanded in source evaluation order and require the same
three gates and native AIR geometry as the direct program. Parenthesized
returned callees have the same checked relation.
The [composed helper example](../../examples/functional/release_helper_composition4/README.md)
also certifies nested calls and captured lambdas inside a helper body. Its
static function arguments leave only the two handwritten addition gates.

`inspect-record-proof` also executes from a private copy of the package,
proof, and statement. Its `unpinned_snapshot` check establishes internal
package consistency and prevents caller path changes during inspection from
changing the displayed record claim. The readback also rejects changes to its
copied source, key, verifier, proof, or statement while the verifier runs. It does not establish an externally
trusted source or verifier identity. `inspect-record-proof-pinned` uses the
same readback with `admitted_snapshot` and the exact `verify-pinned` digest
contract, so externally trusted pins gate both verification and display in
one command. These temporary copies and final digest checks do not isolate
against a same-user process that transiently changes and restores copied
bytes during native execution.

`correspondence.py` independently reparses the exact source bytes for a bounded
public four-lane add/multiply fragment. It erases alias lets and redundant
parentheses without allocating SSA nodes, then checks one to sixteen canonical
arithmetic lets. Calls to the bounded static functions are covered as above;
nested arithmetic, other calls, and other functional forms remain outside
this independent package certificate. For direct-gate text packages
in that grammar, build attaches `correspondence-certificate.json` and verification
requires it. The checker compares the complete normalized relation, canonical
SSA, public ABI, native source-map gate schedule, value-free gate topology,
all eight emitted selector/address column hashes, the exact input/source/ABI
gate allocation and base-256 constant and padding schedule, fixed QM31 basis
derivation,
AIR asset hashes and key core.
An explicit `parse_source_optimized` / `make_optimized_certificate` /
`check_optimized_package` v3 API also checks commutative operand reversal and
first-match CSE. It maps every source producer to a compact canonical ID,
checks that duplicate source names reuse the original native gate span, and
replays the compact direct-gate topology and fixed columns. The default text
package builder and `check_package` remain conservative v2. Building a text
source with `--lowering direct-gate --correspondence optimized` records an
explicit v3 marker, attaches the v3 certificate, and requires the independent
v3 checker in package verification and five-pin `verify-release`. A focused
native test checks the reused span for a
four-operation source that lowers to three gates, and Python mutation tests
reject a forged source map after its report digest is recomputed. The
on-demand `tests/python/check_optimized_native_package.py` builds a temporary
real package, attaches v3 explicitly, checks all bound native artifacts, then
reseals and rejects a malformed duplicate span. It also proves one source
claim, verifies it natively, joins the complete fixed and public main exports
to the first two proof commitments, and rejects changed roots and a changed
public output. Use `--work PATH` to retain the exact package and proof. This
remains a separate opt-in trace regression; the checked-in
[`optimized_release.py`](../../tests/acceptance/compiler_correspondence/optimized_release.py)
exercises v3 release admission and both live outputs of the repeated gate.
[`functional_optimized_release.py`](../../tests/acceptance/compiler_correspondence/functional_optimized_release.py)
checks gate reuse across two live pure helper calls; seven normalized nodes
occupy four native arithmetic gates with handwritten AIR geometry.
Both require a clean pinned Stwo dependency. The
[worked source/AIR/root example](../../../../formal/s31/S31/Gadgets/Functional/Correspondence/OptimizedSourceAirRows.md)
gives the handwritten four-lane computation.
It also checks each source instruction directly against the eight **exported
fixed AIR columns**, using the same row formula as Lean's general
`SSADirectGateBridge.expectedRows` and `SSAAirColumnCells.expectedCells`.
The v2 topology inspection computes the fixed-tree root from the same native
preprocessed circuit that supplies those columns. Package admission checks
that root against the sealed verifier key. The installed native verifier
recompiles the fixed circuit from its embedded source and checks the proof's
fixed-tree root. This is an executable binding through native code, not an
independent proof of the native commitment implementation or PCS security.
For `let a = x .* x; let b = x + a; b`, the modeled rows are:

| Source instruction | Circuit row | Grouped AIR row | Selectors `(add, sub, mul, pointwise)` | `(in0, in1, out, uses)` |
| --- | ---: | ---: | --- | --- |
| `a = x .* x` | 6 | 503 | `(0, 0, 0, 1)` | `(22, 22, 23, 1)` |
| `b = x + a` | 7 | 3 | `(1, 0, 0, 0)` | `(22, 23, 24, 4)` |

The grouped AIR row order differs from source order because the native writer
groups additions before pointwise products. Address 22 is the packed input;
23 and 24 are fresh results. The last use count is four because the public
four-lane output extraction reads `b` four times. The checker recomputes these
positions, selectors, addresses and counts from source syntax and reads the
exported column values at those positions. Tests exercise all lengths 1–16,
both operations, dead results, and mutations of every source fixed-cell field.
The certificate still marks native Gate lookup and AIR/PCS soundness as assumptions.
Older v1 topology artifacts have no exported root and retain an explicit
root-binding assumption in their certificate when paired with a legacy v1 key.
A v2 key requires the v2 topology report even if every package artifact is
resealed.
It is a **package-admission** certificate: the standalone native verifier does
not read it. See the [design brief](../../../../../design/s31/language/DIRECT_GATE_CORRESPONDENCE_CERTIFICATE.md).

The public Python API remains in `../s31.py`; its functions import these
modules. The dependency direction is `context -> verify -> build -> CLI`.

`source_relation_fragment.py` is an independent checker for a
bounded one-to-eight-lane M31 fragment with private inputs, canonical splat
constants, assertions, native subtraction, and up to eight pure one- or two-argument
named functions whose calls are statically erased. Its result is explicitly
`source-to-relation-only`. The builder emits an indexed
`source-relation-certificate.json` for conservative text in that grammar,
regardless of native lowering;
ordinary package verification independently recomputes and requires it. This
is package admission for the source-to-relation boundary only. The standalone
native verifier does not read it, and it does not establish relation-to-AIR
or PCS/FRI soundness. The checker independently parses source bytes, compares
the entire normalized relation, and optionally checks direct-gate public ABI
and manifest identities. Its [scope and example](../../../../../design/s31/language/SOURCE_RELATION_FRAGMENT.md)
explain the exact grammar and remaining circuit/AIR gap.
The [general correspondence matrix](../../../../../design/s31/language/GENERAL_COMPILER_CORRESPONDENCE_MATRIX.md)
lists all production expression forms and normalized operations with their
remaining proof obligations.

`record_source_fragment.py` independently parses a bounded version-2 source
with one nominal M31 record, up to two public/private record inputs, explicit
scalar add/multiply lets, and a record result. It reconstructs every relation
input, node, named leaf path, alias, and the v2 ABI digest from source bytes.
The optional package check compares canonical relation and ABI artifacts even
if their manifest hashes are recomputed after tampering. Its capability is
also `source-to-relation-only`; ordinary package verification and native proof
checking do not treat it as a full compiler or AIR certificate. See the
[bounded record plan](../../../../../design/s31/language/RECORD_SOURCE_RELATION_FRAGMENT_V2.md)
and [native package gate](../../tests/acceptance/record_abi/record_source_fragment_v2.py).
