# S31 soundness remediation status

This is the implementation team's current status against the independent
[soundness review](INDEPENDENT_SOUNDNESS_REVIEW_2026-10-10.md). It does not amend
the review's original findings or claim an independent re-audit.

| Finding | Current implementation and evidence | Release gap |
| --- | --- | --- |
| S31-SEC-01: untrusted package executable | `s31 verify-pinned` copies the package to a private temporary directory, checks externally supplied source, key, prover, verifier, and (for text packages) text-source SHA-256 values, then executes that checked snapshot for base-proof verification. The focused admission tests and native record-selection acceptance exercise this path. | The pins need a trusted distribution channel; copying is not an execution sandbox. Recursive/fold verification still needs an independently trusted package or installed verifier. No signed release exists. |
| S31-SEC-02: public ABI sidecar | `verify_package` derives the ABI from the sealed source and rejects a forged sidecar; the adversarial package control records this rejection. | Repeat the control in release CI on supported package profiles. |
| S31-SEC-03: private endpoint exposure | The private boundary removes endpoints from the public statement but writes them to committed bridge rows. The documentation says this explicitly. | Blinding and a privacy analysis are required before promising witness confidentiality. |
| S31-SEC-04: general chip boundary | A source-derived bounded 1–8 call plan, typed component manifest, endpoint checks and live AIR/PCS preflight exist. Experimental V4 in-memory native proofs pass for one and three calls with mutation controls. V3 fixed-pair ReleaseFast proofs also pass. | V4 canonical proof-byte admission, source-pinned installed verifier, every allowed call count, transcript/lookup soundness argument, independent review and witness confidentiality remain open. |
| S31-SEC-05: compiler correspondence | Lean checks bounded source/SSA and direct-gate input/output AIR-cell bridges, with a mixed 16-operation fixture and native mutation controls. | Public value binding, Gate lookup, committed-column and PCS/FRI correspondence, and a full parser-to-verifier theorem remain open. |

The [profile soundness contract](PROFILE_SOUNDNESS.md) and
[functional v0.1.0 release contract](../language/FUNCTIONAL_V01.md) remain the
release gates. A passing test establishes only its stated profile and control;
it does not establish STARK soundness or source-language correctness for every
program.
