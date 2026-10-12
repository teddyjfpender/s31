# S31 formal live evidence, 2026-10-12

The checked formal gate passed on the S31 release branch. Reproduce it from
`formal/s31` and the repository root:

```sh
lake build S31 S31.Evidence.AxiomAudit s31-check
lake env lean S31/Evidence/AxiomAudit.lean > ../../zig-out/s31/formal/axioms.log
lake env leanchecker -v S31 S31.Evidence.AxiomAudit RiscvRefinement.Field.M31 RiscvRefinement.Recursion.CompactPoseidon > ../../zig-out/s31/formal/kernel.log
cd ../..
python3 scripts/s31_formal.py --audit zig-out/s31/formal/axioms.log --kernel-log zig-out/s31/formal/kernel.log --parity formal/s31/.lake/build/bin/s31-check --controls --report zig-out/s31/formal/evidence.json
```

The latest live run built 4,722 Lake jobs and audited 2,531 theorems over 56
operations. Only Lean's `Classical.choice`, `Quot.sound`, and `propext` appeared
in theorem axiom dependencies. The kernel checker replayed 310 modules. The
independent Python/Lean semantic parity corpus had 1,407 cases: 1,306 accepted
and 101 rejected. The hash schedule gate checked 57 valid profiles and rejected
two malformed schedules. Witness controls accepted 10 honest cases, rejected
10 false cases, and rejected nine gadget mutations. The formal script's 36 unit
tests also passed.

The run includes the [derived-roster arbitrary-trace theorem](../../../formal/s31/S31/Gadgets/Functional/Correspondence/DerivedRosterArbitraryTrace.md),
its ten generated `RuntimeFacts` projections tracked in the source inventory,
and the tightened mixed manifest source binding. The independent theorem
review evaluated the case07 checker to `true` with 512 derived rows. This
evidence checks the modeled semantics and reviewed source bindings.
It does not prove the installed Zig compiler correct, authenticate arbitrary
native PCS openings, establish FRI/transcript soundness, or prove zero
knowledge. The [direct-free alias review](INDEPENDENT_REVIEW_ALIAS_FULL_MODELED_DIRECT_FREE_2026-10-12.md)
identifies where a modeled trace still depends on external native evidence.
