# Decoded mixed events: what is proved

`DecodedEvents.lean` connects the one-call and eight-call fixed mixed exports to
the raw all-row algebraic trace contract. The source owns a 512-row Gate roster,
one chip component per call, and one bridge component per call. A Gate read is
an address plus a Qm31 word; a chip event is a call ID, step, and four M31
words. The bridge reads eight Gate words and presents its input and output
four-word states as chip events.

The theorem takes one decoded Gate trace and reconstructs a `Boundary` whose
canonical Gate rows are exactly that trace. The N1 and N8 fixed exports prove
the row address bounds, row count, and multiplicity budget. Equality of each
physical Gate row to the decoded row then proves the entire source Gate row
list equality, including inactive and padding rows. No separate roster
equality is trusted.

`ChipCells` binds every chip row's call ID, step, input state, and output state
to the corresponding source-native row. `BridgeCells` binds its eight anchor
addresses and words, call ID, and round count to the same source boundary.
The Lean lemmas convert these cell equalities to the five component event-list
equalities. The preexisting `RawEventProjection` theorem then derives both
global event permutations, preserving repeated occurrences. For example, if
the source bridge reads the same Gate address twice, both reads remain in the
positive lookup list; a set comparison would be unsound here.

The N1/N8 `pinned_raw_trace` constructors use these derived lists, source
baseline lists known to be empty, exact public output words, and the native
claimed-sum fold to build `RawAuthenticatedMixedTrace`. The Gate, chip, and
bridge objects still carry their all-row AIR residual premises. The trace's
main values and field equalities are explicit, as are the public word and
claimed-sum bindings. No exact lookup balance is assumed or used to infer
the Gate cell values: that would be circular in the false-public-claim proof.

This is a deterministic statement about **given rows**. Native succinct
verification authenticates queried openings and a low-degree claim
probabilistically. It does not expose all 512 Gate rows and all chip/bridge
rows to Lean. A separate PCS/Fiat–Shamir/FRI soundness and trace-extraction
argument is needed before this contract can be concluded from an accepted
proof. The generated source and native component handles must likewise be
bound to these exact rows; fixture inspection alone does not establish that
binding for an adversarial prover.
