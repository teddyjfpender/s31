# Math native acceptance

`multiplication.py` checks signed and unsigned wrapping products at 8, 32,
and 128 bits. It recalculates every expected result with Python integer
arithmetic, checks the lowered width-tagged node, builds the sparse-wide AIR,
accepts a native proof, and rejects a changed public product. The Zig circuit
tests also reject a byte operand outside its declared range.

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/math/multiplication.py
```
