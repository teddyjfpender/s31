# Command-line frontend

`parser.py` declares the supported `s31` commands and their arguments.
`commands.py` dispatches parsed requests to package building, package
integrity checks, native prover/verifier commands, trials and fold audits.
Commands that read an existing package call `verify_package` before using its
artifacts. The `explain` and `equations` commands also verify the package
before rendering reports.

`build --lowering direct-gate --correspondence optimized` opts a bounded
public four-lane text program into the independent v3 source-to-gate checker.
It certifies commutative operand sorting and common-subexpression reuse,
records the selected certificate schema in the manifest, and makes subsequent
package checks and `verify-release` recompute that certificate. The default
build remains the conservative v2 source fragment.

`verify-pinned` additionally checks exact source, key, prover and verifier
digests supplied from outside the package; text packages require a fifth
digest for `source.s31`. It performs that check in the same invocation as
native proof verification, after copying the package to a private temporary
directory. The verifier runs from that checked snapshot. This command
currently covers base `verify`; recursive and fold commands still require an
independently trusted package or installed verifier.

`../s31.py` is the executable entry point and stable Python import surface.
It keeps the CLI error boundary and re-exports the package and runtime APIs.
The parser and dispatcher are included in the compiler fingerprint and the
formal source-binding inventory.

## Fast source check

Run `check-source` during editing or before a native build:

```sh
python3 src/frontends/s31/python/s31.py check-source \
  src/frontends/s31/examples/arithmetic/arith4_m31.s31
python3 src/frontends/s31/python/s31.py check-source \
  src/frontends/s31/examples/arithmetic/arith4_m31.s31 --json
```

It runs the same parser, static type and totality checks, specialization,
certified pruning, and normalized-relation construction used by `build`.
The JSON result has schema `s31-source-check-v1`, status `valid` or `invalid`,
and a nonzero exit status for invalid source. Valid results include the
canonical relation SHA-256 and node count. Invalid results carry a message
and nullable line/column; source errors are printed with a short code frame
in human mode. This step does not invoke Zig or establish that any native
lowering profile accepts the relation. Use `build` and native acceptance for
that.
