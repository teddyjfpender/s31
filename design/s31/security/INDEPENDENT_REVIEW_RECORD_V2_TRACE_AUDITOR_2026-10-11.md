# Independent review: packaged mixed auditor and eight-word record admission

Reviewed S31 commits `4ff7454`, `48b218b`, and `95e9bb7` on 2026-10-11. This
was a read-only code review plus two native-free Python ABI controls. I did not
rebuild Zig or Lean, rerun a native proof, or change the pinned engine during
the prospective cost run. The existing acceptance tests are evidence of their
reported fixtures, not tests rerun by this review.

## Finding: admitted alias shape need not contain a bit (P2 semantic scope)

`language/bounded_call_admission.zig:72-77` admits the second v2 shape by
input visibility, lengths `(1, 2, 4)`, output count, and the first output's
wire name. It does not inspect the first ABI leaf's type. Both `bit` and `m31`
leaves lower to a one-word relation `m31` input, and
`language/record_abi.zig:150-192` checks each leaf's kind against its own
descriptor type tree and relation *shape*, not against this profile's intended
bit type. Hence the prose in `runtime/mixed_boundary/README.md` and the
record acceptance README describes the tested fixture, rather than a type
restriction enforced on every admitted source.

Minimal native-free control: take
`tests/acceptance/record_abi/mixed_eight_alias_bit.s31.json`, change the
`request.flag` and `result.flag` type-tree and leaf kinds from `bit` to `m31`,
change both typed statement alias words from `1` to `2`, recompute the ABI
digest, and leave the remaining fields and relation alone. Python
`validate_binding` and `decode_public_statement` both accept, projecting
`[2, 5, 6, 2, 2076908689, 937667208, 532178712, 555828162]`. With the
original `bit` descriptor, the same statement word `2` fails as
`AbiError: noncanonical public bit word`. This controls descriptor and alias
consistency; I have **not** run a native proof for the changed descriptor.

Reproduction from the repository root, without a native build:

```sh
PYTHONPATH=src/frontends/s31/python python3 -B - <<'PY'
import json
from pathlib import Path
from abi.binding_v2 import binding_digest, decode_public_statement, validate_binding
p = Path('src/frontends/s31/tests/acceptance/record_abi')
source = json.loads((p / 'mixed_eight_alias_bit.s31.json').read_text())
statement = json.loads((p / 'mixed_eight_alias_bit.statement.json').read_text())
for root in (source['public_abi']['inputs'][0], source['public_abi']['result']):
    root['type']['fields'][0]['type']['kind'] = 'm31'
    root['leaves'][0]['kind'] = 'm31'
statement['leaves'][0]['words'] = [2]
statement['leaves'][2]['words'] = [2]
relation = {k: v for k, v in source.items() if k != 'public_abi'}
relation['version'] = 1
validate_binding(relation, source['public_abi'])
statement['abi_sha256'] = binding_digest(relation, source['public_abi'])
encoded = (json.dumps(statement, sort_keys=True, separators=(',', ':')) + '\n').encode()
print(decode_public_statement(relation, source['public_abi'], encoded))
PY
```

This is not evidence that a proof can make a declared `bit` equal `2`.
`record_abi.claimedWords` checks each leaf's range and exact named path,
requires repeated wires to carry equal words (`record_abi.zig:393-415`), and
then projects only distinct public input/output wires to the proof's eight
words (`:370-390`). A mixed `bit`/`m31` pair on the same wire still constrains
the shared value to `{0,1}` through the bit occurrence. The admitted profile
should either require `bit` for both first-wire descriptor occurrences by
wire identity, with a negative source-descriptor mutation test, or describe
the general admitted shape as a one-word public `m31` alias. The former matches
the stated intent.

## Binding checks observed

- The generated auditor embeds source and AIR, parses the typed v2 statement
  with the same `record_abi.claimedWords` call as the ordinary verifier, and
  passes those eight words to `verifyEmbeddedAndInspectWithTraceAudit`
  (`general_trace_audit_main.zig:36-47`). For v1 it additionally calls
  `statement.check` on the source-derived inspection (`:48-58`). A report is
  printed only after those calls succeed.
- The package checks proof envelope source, manifest, circuit identity,
  canonical public words, bounded postcard shape, and native proof verification
  before returning the audit. It independently evaluates the supplied
  assignment against the eight public words and recompiles its witness
  (`general_package.zig:342-433`). The pinned engine's
  `auditVerifiedSourceBoundWitness` verifies the proof, checks circuit,
  chip, bridge, and interaction rows, and compares recomputed fixed/main/
  interaction commitments and claimed sums with the proof
  (`deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig:968-1088`).
- In the v2 fixture, the public salt is unused by computation but is still a
  public input in the compiled circuit output vector
  (`relation_compiler.zig:923-940`). The proof's eight public words include
  that salt. The repeated `y` leaf is checked for equality by wire name and
  adds no second four-word proof output.
- The v2 proof test checks one honest proof, three ABI-valid changed claims
  rejected after parsing, four malformed alias/type/layout claims rejected
  during parsing, a private witness mismatch, and an honest full-trace audit.
  The changed-witness v2 audit test may reject at public evaluation because
  `x` changes while `y` remains fixed; the earlier equal-public sidecar test
  is the evidence for main-root binding when public words stay equal.

## Lower-severity limits and remaining assumptions

- **P3 report provenance:** the CLI's JSON contains three roots, row counts,
  and `verified: true`, but no source, statement, proof, package, or assignment
  digest (`general_trace_audit_main.zig:14-23,60-72`). It is useful as local
  diagnostic output. Detached JSON alone is not an authenticated audit
  certificate or a portable statement-to-proof attestation.
- The CLI caps proof, statement, and assignment file reads at 16 MiB, 1 MiB,
  and 1 MiB respectively; the package has bounded postcard preflight and a
  64 MiB maximum decode arena. The auditor is expensive and requires the
  private assignment. I found no unchecked public input or obvious
  assignment-swap acceptance in this path.
- Native tests here cover one specific v2 source and finite mutations, not
  arbitrary record programs. Full parser/compiler correspondence, accepted
  proof-to-Lean-row extraction, Merkle binding, PCS/FRI soundness, and the
  Fiat-Shamir reduction remain outside this review. Three matching roots
  bind a *supplied* full trace under those assumptions; they do not extract
  every trace row from an arbitrary succinct proof.
