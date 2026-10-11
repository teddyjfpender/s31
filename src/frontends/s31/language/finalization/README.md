# Circuit finalization policy

`constant_base.zig` selects minimum radix 16 for normalized relations with
at most 64 nodes, at least one fixed-width integer operation, and no hash
or Bitcoin operation. All other relations retain the engine's radix 256.
It uses the engine's public
`finalizeConstantsWithMinBase` API and performs the same reserved-output and
guessed-witness checks as its default `Context.finalize(false)` path.

The policy depends only on normalized source operations, so value and
symbolic compilers choose identical topology. Programs with hash or Bitcoin
operations keep the engine's default schedule. Cost and native proof gates
pin the resulting circuit geometry.
