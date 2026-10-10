# Command-line frontend

`parser.py` declares the supported `s31` commands and their arguments.
`commands.py` dispatches parsed requests to package building, package
integrity checks, native prover/verifier commands, trials and fold audits.
Commands that read an existing package call `verify_package` before using its
artifacts. The `explain` and `equations` commands also verify the package
before rendering reports.

`../s31.py` is the executable entry point and stable Python import surface.
It keeps the CLI error boundary and re-exports the package and runtime APIs.
The parser and dispatcher are included in the compiler fingerprint and the
formal source-binding inventory.
