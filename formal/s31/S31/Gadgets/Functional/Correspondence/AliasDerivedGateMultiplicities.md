# Source/schedule-derived Gate multiplicities

For a direct-Gate alias program, the compiler certificate determines its
source and public rows. A constant-island address schedule supplies the other
rows. Each row reads `in0` and `in1`. The public boundary also reads nine
addresses, `[2, 3, 4, 5, 6, 7, 8, 9, 10]`, and supplies no Gate yield.

For a producer whose output address is `a`, the required fixed multiplicity is

```text
number of occurrences of a among all row in0/in1 addresses
  + number of occurrences of a among the nine public feeder addresses
```

Repeated operands count twice. For example, a row reading address 7 in both
ports contributes two uses of 7. An unused output gets multiplicity zero.
This is why the fixed multiplicity cannot safely be a free value in an island
certificate: a locally valid arithmetic row could still claim an incorrect
number of Gate lookup yields.

For the checked-in case07 diagnostic, an independent count over its 512
`in0`/`in1` address pairs plus the nine public feeders yields 1,033 reads.
Its 512 fixed output addresses are unique, every native multiplicity equals
the count at its output address, and the multiplicities also sum to 1,033.
The largest count is 632, for the heavily reused constant one.

`addressSchedule` erases every supplied island multiplicity. `derivedIsland`
fills each island cell's multiplicity from the global read count.
`projectedCountsCheck` confirms that the independently source-derived
source/public rows have the same count. The combined `check` also runs the
existing constant-island arithmetic/value checker and bounded exact Gate
ledger. Its full-model theorem constructs a 512-row synthetic trace and
proves that **every** row's multiplicity is the calculated count. A theorem
shows that changing any input island multiplicity leaves this checker and
the constructed island unchanged.

The island's selectors and three addresses remain a supplied schedule that
must pass the checker. This theorem does not derive the Zig constant-address
generator, authenticate fixed columns from PCS openings, or establish STARK
soundness. Those are separate compiler/native-proof correspondence steps.
