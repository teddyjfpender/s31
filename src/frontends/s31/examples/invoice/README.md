# Prove an invoice total

This small application proves that two line items and a delivery fee add up
to a public total. Prices and fees are unsigned integer cents; quantities are
unsigned counts. The reusable `line_total` function specializes into checked
64-bit multiplication. Both additions are checked too: a value exceeding
`2^64 - 1` is rejected rather than wrapping.

The synthetic [assignment](invoice.valid.json) describes:

| Item | Quantity | Unit price (cents) | Line total (cents) |
| --- | ---: | ---: | ---: |
| A | 3 | 125 | 375 |
| B | 2 | 450 | 900 |
| Delivery | | | 25 |
| **Total** | | | **1300** |

The [circuit](invoice.s31) computes `3 * 125 + 2 * 450 + 25 = 1300`.
Its five inputs are witnesses and its only public output is `total`.
The verifier must supply the expected total from the application, rather
than accepting whichever total the prover supplies. This relation proves
arithmetic validity; it does not authenticate an order or a price list.
The `private` declarations describe the proof boundary; see the
[proof privacy guide](../../docs/proof-privacy.md) for profile-specific limits.

## Read the assignment

Each `u64` is encoded as four little-endian `u16` limbs:

```text
value = limb[0] + 65536 * limb[1]
      + 65536^2 * limb[2] + 65536^3 * limb[3]
```

Thus 1300 is `[1300, 0, 0, 0]`, and 65536 is `[0, 1, 0, 0]`.
Each limb must be between 0 and 65535. Zero quantities and zero prices are
allowed; there is no minimum purchase requirement.

## Lower, check, and prove

Run these commands from the repository root, with the pinned engine submodule
initialized and **Zig 0.15.2** on PATH.

Inspect the normalized relation (also checked in as
[invoice.s31.json](invoice.s31.json)):

```sh
python3 src/frontends/s31/python/s31.py lower \
  src/frontends/s31/examples/invoice/invoice.s31
```

Check the calculation with the independent Python value oracle:

```sh
python3 src/frontends/s31/python/s31.py oracle \
  src/frontends/s31/examples/invoice/invoice.s31 \
  src/frontends/s31/examples/invoice/invoice.valid.json
```

Expect `status: passed` and `total: [1300, 0, 0, 0]`. Then build a native
prover/verifier package, prove the assignment, and verify it:

```sh
python3 src/frontends/s31/python/s31.py trial \
  src/frontends/s31/examples/invoice/invoice.s31 \
  src/frontends/s31/examples/invoice/invoice.valid.json \
  --lowering direct-gate --out zig-out/s31/invoice-trial
```

`trial` also checks that the verifier rejects a changed public total. It saves
the proof, public statements, source/geometry reports, and `trial-report.json`
under the output directory. The report does not copy the private assignment.

To experiment, copy the assignment and change quantities or prices, then
recalculate the claimed total. Changing just the claimed total to 1301 makes
the oracle reject the assignment. Setting a quantity to `2^64 - 1` and its
price to 2 makes checked multiplication reject it. Two individually valid
line totals can also overflow their checked subtotal or the final fee addition.

The focused regression checks cover these cases, zero quantities and prices,
multi-limb arithmetic, the maximum valid `u64` total, and agreement between
the text source and checked-in relation:

```sh
python3 -B -m unittest discover -s src/frontends/s31/tests/python \
  -p 'test_invoice.py' -v
```
