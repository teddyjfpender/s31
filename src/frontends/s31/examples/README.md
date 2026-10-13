# S31 examples

Examples are grouped by the concept they demonstrate. Where a checked
normalized `.s31.json` relation and assignment (`.valid.json`) are provided,
they stay beside the corresponding `.s31` source. Some release examples build
those artifacts during their acceptance test.

| Directory | Programs |
| --- | --- |
| [`arithmetic/`](arithmetic/) | Field arithmetic, polynomials, and reductions. |
| [`functional/`](functional/) | Pure helpers, closures, static application, and checked gate sharing. |
| [`recurrence/`](recurrence/) | Higher-order static steps that retain the dedicated recurrence chip. |
| [`boundary/`](boundary/) | A private four-lane circuit-to-chip recurrence with one public aggregate. |
| [`arrays/`](arrays/) | Static arrays, views, slices, and matrix operations. |
| [`control/`](control/) | Boolean values, selection, and mixed computations. |
| [`hashes/`](hashes/) | Preimages, Merkle trees, BLAKE2s, and Poseidon2. |
| [`wide/`](wide/) | Checked and wrapping 256-bit operations. |
| [`math/`](math/) | Fixed-width scalar integer operations and typed overflow modes. |
| [`invoice/`](invoice/) | A small application: checked integer line items and a public invoice total. |
| [`payments/`](payments/) | Hash-based Tongo-style note ownership, checked value conservation, delivery and replay protection; validity prototype, without a proof confidentiality guarantee. |
| [`bitcoin/`](bitcoin/) | Header hashing, proof of work, linked headers, and a checked ChainWork transition. |
| [`keys/`](keys/) | Placeholder keys for build-time examples. |

The `cairo*` directories contain comparison programs. Test and benchmark
drivers that select a fixture by name use [`example_path`](../python/example_paths.py)
to find its unique file across these directories. Production S31 packages
always receive an explicit source path.
