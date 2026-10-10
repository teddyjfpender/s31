# S31 soundness remediation status

This is the implementation team's current status against the independent
[soundness review](INDEPENDENT_SOUNDNESS_REVIEW_2026-10-10.md). It does not amend
the review's original findings or claim an independent re-audit.

| Finding | Current implementation and evidence | Release gap |
| --- | --- | --- |
| S31-SEC-01: untrusted package executable | `s31 verify-pinned` copies the package to a private temporary directory, checks externally supplied source, key, prover, verifier, and (for text packages) text-source SHA-256 values, then executes that checked snapshot for base-proof verification. The focused admission tests and native record-selection acceptance exercise this path. | The pins need a trusted distribution channel; copying is not an execution sandbox. Recursive/fold verification still needs an independently trusted package or installed verifier. No signed release exists. |
| S31-SEC-02: public ABI sidecar | `verify_package` derives the ABI from the sealed source and rejects a forged sidecar; the adversarial package control records this rejection. | Repeat the control in release CI on supported package profiles. |
| S31-SEC-03: private endpoint exposure | The private boundary removes endpoints from the public statement but writes them to committed bridge rows. The documentation says this explicitly. | Blinding and a privacy analysis are required before promising witness confidentiality. |
| S31-SEC-04: general chip boundary | A source-derived bounded 1–8 call plan, typed component manifest, compiled endpoints and live AIR/PCS preflight feed an experimental V4 `S31MNY04` proof envelope and dedicated source-pinned verifier. Native proofs pass for every call count 1–8; the 2–8 matrix rejects each changed claimed sum, and selected/legacy V4 proof bytes match at counts 1 and 8. Black-box controls reject malformed and changed statements. The [independent guarded-V4 review](INDEPENDENT_REVIEW_GUARDED_V4_AND_EVALUATOR_2026-10-11.md) found no new sealed-verifier false-proof admission; V3 fixed-pair ReleaseFast proofs still pass. | A general mixed-chip scheduler, full transcript/lookup soundness argument, source-to-verifier correspondence and witness confidentiality remain open. The engine adapter alone is not an authenticated proof-byte API. V4 is outside general package admission. |
| S31-SEC-05: compiler correspondence | Lean checks bounded source/SSA and direct-gate input/output AIR-cell bridges, including a mixed 16-operation fixture, a four-word public-input binding lemma, and a theorem that exact source-row cells plus accepted local polynomial residuals force the selected wire to the packed source value under a coherent Gate wire-map premise. A further conditional Lean model covers the 11 decoded direct Gate evaluator residuals; a two-row fixture and native controls reject changed public words, Gate claimed sum, and resealed fixed/main/interaction spans. | Exact installed evaluator bytecode equivalence, proof-committed column authentication, native predecessor-mask equality, PCS/FRI correspondence, production Gate lookup and a full parser-to-verifier theorem remain open. The Lean results retain explicit evaluator, row-authentication and public-closure premises. |

The [profile soundness contract](PROFILE_SOUNDNESS.md) and
[functional v0.1.0 release contract](../language/FUNCTIONAL_V01.md) remain the
release gates. A passing test establishes only its stated profile and control;
it does not establish STARK soundness or source-language correctness for every
program.
