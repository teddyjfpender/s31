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

## Environment diagnostics

From the repository root:

```sh
python3 -B src/frontends/s31/python/s31.py doctor
python3 -B src/frontends/s31/python/s31.py doctor --native
python3 -B src/frontends/s31/python/s31.py doctor --native --json
```

`doctor.py` uses only standard-library imports at startup. The executable
routes diagnostics before importing compiler/proof modules, so a missing
engine can be reported without an import-time crash. It checks required
source paths, tracked engine modifications, the engine commit against HEAD's
submodule pin, Zig 0.15.2, macOS SDK discovery, a tiny source/oracle calculation,
and compiler identity. Complete source bundles use the existing manifest and
digest checks; hashing their engine tree can take longer than Git inspection.
Python's detected version is reported without asserting an undeclared support
range; importing and exercising the frontend tests its required capabilities.

Each check has a stable ID, `pass`, `fail`, `warn`, or `skip` status, an elapsed
time, and remediation for failures/warnings. Independent checks continue after
a failure; dependent ones are skipped. Exit status is 1 for a blocking failure
and 0 otherwise. JSON includes the same results and `native_passed` separately.
SDK discovery alone does not establish linker compatibility. Optional resource
measurement failure is a warning and does not block proving.

Default diagnostics do not intentionally change project or toolchain files.
`--native` builds a dedicated `direct-gate` smoke package in a temporary
directory, proves `3 + 7 = 10`, verifies the proof, and requires rejection of a
changed result of 11. It runs proof commands directly, without requiring the
profiling wrapper. Zig may populate its normal caches. Temporary files are
removed on success or failure; `--keep-artifacts` retains them and reports the
path. This option requires `--native`. A cleanup failure is a blocking diagnostic
and reports the retained path. Changed-claim rejection must report a recognized
public-binding or transcript error; an unrelated verifier failure or crash
does not count as a successful negative control.

`--timeout SECONDS` sets a positive per-subprocess limit (default 300 seconds);
quick tool discovery and source smoke checks have a maximum of 15 seconds.
On POSIX systems, timeouts terminate the subprocess group, including build
children. Displayed output is truncated to roughly 8,000 characters. Native proofs are
never retried automatically. Doctor does not download tools, patch SDKs,
change PATH, discard local modifications, or certify all proof profiles.
