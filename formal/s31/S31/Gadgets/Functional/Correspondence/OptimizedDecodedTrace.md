# Optimized source through a decoded AIR trace

[`OptimizedDecodedTrace.lean`](OptimizedDecodedTrace.lean) joins the optimized
four-lane add/pointwise-multiply source grammar to an **arbitrary decoded
512-row trace**. The earlier source proof worked with a freely supplied
logical wire map and local cell equations. This theorem takes fixed and main
row facts about one physical trace, derives its logical wire map through
exact Gate event balance, and proves the original source's public result.

The source fragment has one public `[m31; 4]` input, one public output,
1–16 arithmetic `let` statements using `+` and `.*`, and bounded zero-cost
alias lets such as `let copy = a;`. An alias resolves to an earlier input or
producer and emits no normalized node, canonical node, or AIR row. Parentheses
around references and a single binary expression are erased. The exact source,
normalized JSON, and compact canonical IR bytes must pass `checkBytes`.
Commutative operand sorting and common subexpression elimination may merge
source expressions. `checked_optimized_source_input_used` proves from those
bytes that the compact first producer consumes input wire zero. This removes
the input-pack multiplicity condition that previously had to be supplied by
the caller.

For the handwritten program

```s31
circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {
  let a = x + x;
  let b = x .* x;
  let c = a + b;
  let d = b + a;
  d
}
```

the compact circuit has three producer cells, at modeled rows **3, 503, 4**.
The last source `let` maps to `c` and has no new cell. For input
`[1, 2, 3, 4]`, the output is `[3, 8, 15, 24]`. A *lane* is one independent
M31 coordinate; the four coordinates share one packed circuit wire.

The theorem `optimized_source_to_decoded_air` has these premises:

1. `checkBytes` accepts the three exact byte streams and returns `compact`.
2. The decoded trace's projected fixed cells match the source and public
   input/output roster, and its nine installed arithmetic residuals vanish
   on all 512 rows.
3. Its ideal Gate producer values are unique, the required zero/basis events
   exist, and four input and four output pins use the public values.
4. The trace's complete ideal Gate use/yield multisets balance exactly.

From these, Lean proves `denotation sourceBytes input = some claimed`, at most
16 compact producers, an exact 512-row partition, and distinct in-range
source/public physical row positions. The proof does not assume a chosen add
row count or a chosen logical wire. It derives the add row count from the
compact certificate and the wire values from the decoded trace's Gate
events.

The theorem `optimized_forged_claim_unbalanced` says a wrong public result
cannot satisfy exact Gate balance under the same fixed trace facts.
`optimized_false_claim_raw_pair_bound` reuses the raw LogUp algebraic bound
for exceptional challenge pairs on that fixed trace, with its canonical
address and event-count conditions stated in the theorem.

These are **modeled, conditional** statements. The proof does not establish
that production Zig emits the modeled fixed columns for every accepted
optimized source, that a proof commitment authenticates these decoded cells,
or that challenge sampling, PCS, FRI, and Fiat–Shamir turn the ideal Gate
premise into native verifier soundness. The v3 package checker provides finite
executable evidence for selected compiled programs. The large pinned example
source/JSON/IR byte literals are not themselves kernel-proved to pass the
universal `checkBytes` function; the theorem applies to any triple that does.

`aliased_reversed_exact_bytes` is a pinned positive exception to that last
qualification: Lean checks the exact source bytes below against the captured
normalized JSON and compact canonical IR bytes. The checked compact circuit
has three producers after both alias erasure and common subexpression
elimination; `returned` resolves to producer `d` and the public output is
encoded under `d`. Its source denotation equals compact circuit execution
for every four-lane input via `aliased_reversed_semantics`.

```s31
circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {
  let base = (x);
  let a = (base) + x;
  let keep = (a);
  let b = base .* x;
  let c = keep + b;
  let d = b + a;
  let returned = (d);
  returned
}
```

Lean also rejects forward aliases, duplicate names, aliases of the input as
the final output, and unbalanced alias parentheses. A Python differential
check compares this exact source with the independent fragment parser and
production text compiler, including the complete normalized JSON and
canonical IR byte strings. This finite check does not prove general Python
parser equivalence or native AIR emission.

Focused checks:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.OptimizedDecodedTrace
lake env leanchecker S31.Gadgets.Functional.Correspondence.OptimizedDecodedTrace
```
