# Math native acceptance

`multiplication.py` checks signed and unsigned wrapping products at 8, 32,
and 128 bits, plus checked products at 8, 32, and 128 bits. It recalculates
every expected result with Python integer arithmetic, checks the lowered
width-tagged node, pins AIR geometry, builds the sparse-wide AIR, accepts a
native proof, and rejects a changed public product. Checked cases also reject
an independently constructed overflow witness in the oracle. Zig circuit
tests confirm that the emitted constraints reject overflow, including signed
`MIN * -1`, and reject a byte operand outside its declared range.

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/math/multiplication.py
```
