# Alias source to a complete modeled direct-Gate trace

[`AliasCheckedPhysicalModeledComposition.lean`](AliasCheckedPhysicalModeledComposition.lean)
connects an exact alias-source check to the existing complete 512-row
direct-Gate model. An alias adds no arithmetic producer. For example:

```s31
circuit early_alias(public x: [m31; 4]) -> public [m31; 4] {
  let base = (x);
  let a = ((base) .* (base));
  let saved = (a);
  let b = base + saved;
  let c = ((saved) .* (b));
  let returned = saved;
  returned
}
```

The checked producer certificate has three eager gates: `a = x .* x`,
`b = x + a`, and `c = a .* b`; its public output selects `a`. At
`x = [0, 1, 2, 7]`, the gates yield `a = [0, 1, 4, 49]`,
`b = [0, 2, 6, 56]`, and `c = [0, 2, 24, 2744]`. The public result is `a`,
while `b` and `c` still occupy arithmetic rows.

The theorem requires **two exact byte checks** that return the same
certificate: one for the alias source, normalized relation, and canonical IR;
one for a producer-only spelling and its normalized relation. Their checked
semantic equations make both spellings compute the same output for every
four-lane input. A checked constant island supplies the other physical rows,
and a checked address ledger supplies ideal Gate event balance. The conclusion
gives one complete modeled 512-row trace with each selected fixed cell at its
physical row, zero local arithmetic roots, and the selected public output.
It also retains `InputBoundary certificate (compiledAddRows certificate) wire
input` for that **same** wire and trace. This pins the four public scalar
inputs, their copy rows, the zero and basis seeds, and all six input-pack
arithmetic rows. The checked constant island only overlays shared seed
addresses in this input prefix; the seed check proves those values agree
with the projected public witness.

The producer-only spelling is a visible premise. The theorem does not prove
that every accepted alias source has such a spelling, that the Python or Zig
compiler implements these Lean parsers, or that a native proof's openings
equal this modeled trace. Native commitment, LogUp, PCS, and FRI soundness
remain separate obligations.
