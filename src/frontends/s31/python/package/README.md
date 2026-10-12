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
three gates and native AIR geometry as the direct program.

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
package builder and `check_package` remain v2-only; they do not automatically
admit optimized source. A focused native test checks the reused span for a
four-operation source that lowers to three gates, and Python mutation tests
reject a forged source map after its report digest is recomputed. The
on-demand `tests/python/check_optimized_native_package.py` builds a temporary
real package, attaches v3 explicitly, checks all bound native artifacts, then
reseals and rejects a malformed duplicate span. It also proves one source
claim, verifies it natively, joins the complete fixed and public main exports
to the first two proof commitments, and rejects changed roots and a changed
public output. Use `--work PATH` to retain the exact package and proof. This
is an opt-in regression, not v3 release admission; it requires a clean pinned
Stwo dependency. The [worked source/AIR/root example](../../../../formal/s31/S31/Gadgets/Functional/Correspondence/OptimizedSourceAirRows.md)
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

`source_relation_fragment.py` is a separate development/audit checker for a
bounded one-to-eight-lane M31 fragment with private inputs, canonical splat
constants, assertions, native subtraction, and one pure two-argument named
function whose call is statically erased. Its result is explicitly
`source-to-relation-only`; it is not
used for package admission or native verification. It independently parses
source bytes, compares the entire normalized relation, and optionally checks
direct-gate public ABI and manifest identities. Its [scope and example](../../../../../design/s31/language/SOURCE_RELATION_FRAGMENT.md)
explain the exact grammar and remaining circuit/AIR gap.

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
