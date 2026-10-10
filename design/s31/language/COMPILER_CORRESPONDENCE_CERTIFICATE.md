# S31 compiler correspondence certificate: audit and implementation brief

Status: design audit, 2026-10-10. **No end-to-end compiler correctness proof exists today.** Native proof verification establishes satisfaction of the circuit AIR selected by a sealed key, subject to the Stwo soundness assumptions. It does not by itself establish that the AIR computes the intended `.s31` source semantics.

## The claim to establish

For accepted source bytes `S`, public statement `P`, and proof `π`, the desired theorem is:

> If the generated verifier accepts `(π, P)` under a certificate checked against `S`, then there exists a private source input `W` for which the independently defined S31 semantics of `S(W)` yield exactly `P`.

This needs three separate implications: source semantics imply the normalized relation; the relation implies the circuit and every selected chip boundary; and accepted AIR/lookup/FRI proof implies satisfaction of that circuit. A hash of an artifact establishes identity, not any of these semantic implications. The theorem also needs an explicit statement of cryptographic assumptions and the public ABI encoding.

## Current boundary, and what it does not prove

| Boundary | Implemented check | Remaining correspondence gap |
| --- | --- | --- |
| Text bytes → typed source | `python/text_frontend.py` lexes, parses, checks types, and specializes functions; `python/s31_stdlib.py` and `python/s31_mathlib.py` expand helpers. `python/package/build.py:build_text` stores `source.s31`, a typed interface, source map, and a lock containing library source hashes. | These rules have no independent semantics checker. `bit`, digest families, nominal names, and fixed-width signedness are partly erased into `m31`/`u16` relation shapes. A frontend bug can silently choose the wrong operation while producing a well-typed relation. |
| Text → normalized JSON | `python/package/context.py:lower_text` emits sorted, indented JSON. `verify_package` re-runs the **same** Python frontend and compares bytes with packaged `source.s31.json`; acceptance tests include text-tamper cases. | Re-running the implementation catches tampering and nondeterminism, not a systematic miscompilation in that implementation. Raw JSON programs can enter `build_json` without any text-origin claim. |
| Normalized JSON → canonical IR | `language/relation.zig:parseProgram` rejects unknown fields and `Program.validate` checks operation shapes, names, use-before-definition, and public-word capacity. `language/canonical.zig:build` folds constants, aliases identities, reorders commutative operands, and hash-conses nodes. The key stores the resulting IR hash. | The typed source information is absent. The optimizer has no checked rewrite trace or general proof that every fold, alias, and common-subexpression elimination preserves relation semantics. The IR hash only identifies its output. |
| Canonical IR → circuit | `language/relation_compiler.zig:compileWithSpansMode` constructs a witness-independent `NoValue` topology and a `QM31` value topology, with optional source-to-row maps. `runtime/mvp_runtime.zig:validateCompiledKey` rebuilds topology from embedded normalized JSON and checks padded geometry, preprocessed root, circuit hash, and private boundary when present. | The validator and prover use the same compiler. A shared wrong lowering can pass both. Span maps report positions but are not checked semantic derivations. Equality of `NoValue` and value-mode topology, input range constraints, output order, and helper gadget semantics are tested, not proved universally. |
| Circuit → AIR/proof | The verifier authenticates pinned projection and AIR-bundle bytes in `runtime/mvp_runtime.zig:parseAirBundle`; `integrations/circuit_cpu/air.zig` rebinds selected constraint programs to the circuit layout. `runtime/native_verifier.zig` checks the proof envelope, commitment roots, lookup sums, public words, and PCS/FRI proof. | Bundle authentication does not prove that every bound AIR polynomial enforces the intended gate, range, yield, and lookup equations. Profile-specific SHA and private-chip joins add separate boundary and multiset-closure obligations. The cryptographic soundness of the exact PCS, Fiat–Shamir transcript, lookup compression, and FRI parameters remains an explicit assumption pending independent review. |

The installed verifier in `runtime/mvp_runtime.zig:verifierMain` embeds and validates **normalized JSON**, not the original `.s31` text. The Python package validator checks the stored text by re-lowering it. A certificate must close this split without treating Python's agreement with itself as independent evidence. The `std@1` lock pins implementation bytes but does not prove helper semantics.

Profile identity needs care. The `direct`, `sparse`, and `sparse-wide` paths include a source digest in their identity functions, while the ordinary gate path uses `hostCircuitHash` of circuit geometry and preprocessed root. Decide whether the release promise is semantic equivalence or exact source-byte identity. If exact bytes must be bound to every proof, the gate transcript/key format must change; a certificate hash merely stored in a package manifest would not suffice.

## First certified fragment

Start with an intentionally narrow, independently parsed grammar and `direct-gate` only:

```s31
circuit affine_square(private x: [m31; 4]) -> public [m31; 4] {
    let square = x .* x;
    let result = square + splat<4>(7_m31);
    result
}
```

Allow one circuit, `[m31; 4]` inputs and result, canonical M31 literals, `splat<4>`, `let`, `+`, `.*`, and `assert_eq`. Require at most eight public words in the existing ABI. Reject functions, imports and `std` helpers, loops, array indexing, bits, nominal types, witnesses introduced inside gadgets, hashes, chips, recursion, and JSON-only sources. Require source bytes to be valid UTF-8 with an ASCII token alphabet; define comment and whitespace handling exactly. The checker must reject trailing source bytes, duplicate names, duplicate JSON keys, unknown op fields, noncanonical constants, and undeclared free variables. It must not call `text_frontend.py`, `s31_stdlib.py`, `relation.zig:Program.validate`, or `canonical.zig:build` as its only check of the same property.

The fragment has a small denotational semantics over `F_p^4`: `splat(c)` is `(c,c,c,c)`, `+` and `.*` are pointwise field operations, each assertion requires vector equality, and the final vector is the public result. Private inputs range over canonical field elements. This is small enough to encode in Lean with a decidable checker. A production checker must execute that verified decision procedure, or have its own proved refinement to it; differential tests alone do not turn a separate Zig checker into a formal proof. A theorem for this fragment should quantify over *all* inputs, not sampled assignments.

## Certificate and checker contract

Introduce `s31-correspondence-v1` as a canonical, length-delimited binary certificate. It binds:

1. SHA-256 of exact source bytes; grammar and semantics version; selected proof profile and public ABI order.
2. The typed syntax tree with source byte spans, type derivations, and an expansion trace for every helper or specialized call. The first fragment has an empty expansion trace.
3. Canonical bytes and SHA-256 of normalized relation JSON; a source-expression-to-relation-node map, including constant realization, assertions, and outputs.
4. A relation-node-to-canonical-IR map with an explicit rewrite reason for each alias, fold, commutation, and CSE. The first fragment can reject unrecognized rewrites; later versions add individually proved rewrite rules.
5. A canonical-IR-to-circuit map: every input wire, output wire, assertion, gate row, range check, and public binding position. Include serialized builder topology, padded row counts, preprocessed root, and circuit identity.
6. Exact AIR projection/bundle hashes, selected component list, lookup relations, geometry, and a digest of the verification-key **core** before its certificate field is inserted. Define that key-core serialization once; otherwise key and certificate hashes would depend circularly on each other. These identifiers name the assumed AIR contract; they are not themselves an AIR soundness proof.

The independent checker should return one digest of its *validated statement* (source hash, semantic version, normalized-relation hash, circuit root, profile, ABI, key-core hash, and AIR-contract ID), rather than trusting hashes supplied by the certificate. The final sealed key then records this certificate digest. The checker must recompute all small-fragment semantics and compare the supplied relation graph, canonical graph, gate table, public binding, and key identity. Reject unknown certificate versions, profiles, operations, and rules. Do not silently widen the certified fragment when the production compiler gains syntax.

Suggested new files and integration points:

| File | Role |
| --- | --- |
| `src/frontends/s31/cert/format.zig` | Canonical certificate decoder with strict bounds, duplicate-field rejection, and domain-separated hashes. |
| `src/frontends/s31/cert/source_core.zig` | Independent lexer/parser/type checker and field-vector semantics for the first fragment. |
| `src/frontends/s31/cert/relation_check.zig` | Check source-to-relation derivations and the fixed public ABI without invoking Python or `relation.zig` validation. |
| `src/frontends/s31/cert/canonical_check.zig` | Check each optimizer rewrite, node identity, assertion, and output map. |
| `src/frontends/s31/cert/circuit_check.zig` | Read serialized gate topology; check direct-M31 gate equations, input/output reachability, public binding, and preprocessed-column serialization. |
| `src/frontends/s31/cert/main.zig` | Standalone `s31-cert-check SOURCE CERT KEY` command; print machine-readable validated-statement digest. |
| `src/frontends/s31/python/s31.py` | Certificate producer hook after `lower_text`; package artifacts and manifest entry. Production Python may propose evidence but cannot decide its validity. |
| `src/frontends/s31/runtime/mvp_runtime.zig` | For certified packages, seal certificate bytes/digest and require checker acceptance before native proof verification. Expose a distinct certified key schema or capability; leave uncertified packages honestly labeled. |
| `src/frontends/s31/tests/acceptance/acceptance_correspondence.py` | Good proof plus independently mutated source, relation, type tag, rewrite, gate, public binding, AIR ID, key, and proof. |
| `formal/s31/S31/Gadgets/Functional/` | Extend the existing Lean definitions and proofs for the small source/relation semantics and direct arithmetic gate contracts. Keep the proof checker and generated theorem inputs versioned. |

Do not write a producer that emits only hashes and calls it a certificate. The checker must inspect structural evidence and reject a wrong circuit even if every hash in a forged package is recomputed consistently. A useful negative test is a compiler mutation replacing `mul` with `add`, followed by regeneration of the relation, key, and manifest: the independent checker must reject it against the unchanged source.

## AIR contract and promotion path

First prove or independently check the direct-M31 gate subset: field addition and multiplication rows, assertion equality, M31 input guesses, output/yield binding, padding selectors, and the Gate lookup multiset. Express the contract as: satisfying the selected AIR and lookup closure yields an assignment to the serialized gate table with exactly the public words the verifier mixed into the transcript. The checker may initially report `source-to-circuit-certified; AIR-contract-assumed` until this implication is discharged. A successful STARK proof is not a substitute for that implication.

Promotion should be operation- and profile-specific:

1. Add zero-cost source constructs (pure function inlining, static arrays and views, nominal casts) with explicit type-erasure and expansion derivations. Prove that a `std@1` helper expansion is the checked relation promised by its API, including library source hash/version.
2. Add range and Boolean gadgets, `u16`, fixed-width signed/unsigned integers, `UInt256`, checked carries/borrows/division, and public encoding. Each new gadget needs a range and overflow theorem, not only a value oracle.
3. Add `iterate` and direct private-chip boundaries with endpoint maps and lookup closure. Add SHA-specific profiles only after caller/Gate, schedule/round/feed word-bus, and joint-proof boundary contracts are checked.
4. Add sparse-wide/gate AIR contracts and recursive wrappers; separately validate verifier-circuit and child-proof transcript correspondence. A certificate for a base circuit does not certify recursive verification automatically.

Gate each stage on a checker-produced certificate, a native proof, independently calculated values, mutation tests that regenerate all untrusted package metadata, and a reviewed AIR-contract statement. Continue to report any remaining assumption in the certificate status. Only call a package **end-to-end certified** after the source-to-circuit checker, selected AIR contract, and cryptographic soundness assumptions are all explicit and independently reviewed.
