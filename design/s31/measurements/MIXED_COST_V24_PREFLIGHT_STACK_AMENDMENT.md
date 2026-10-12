# V24 compiler-stack amendment before native observation

The V24 conditional-repeat source and protocol were originally frozen at commit
`585bcfc` (cherry-picked to the PR as `98bf2c5`), protocol SHA-256
`8456cb986d37a5fac588bb61efb4e424fa01087775925f1e6a3552d3ba96a927`.
The compiler stack on the shared PR then advanced through native manifest
geometry tightening before the one native attempt. The original strict
`freeze.py check` correctly rejected that stack. At the time of this
amendment there is **no V24 attempt marker, package, proof, timing result, or
score**. No native V24 run has started.

Exactly one pinned compiler file differs from the original freeze:
`src/frontends/s31/runtime/mixed_boundary/registry_manifest.zig` changed
from SHA-256 `b30fb96a904d95c2997c5770ea9f21bc3246a51ca25b564f8f3ed294d6ac03a0`
to `67c3f6c6ebfe3b9f1133b9c15d94680759c67072fc80b02b97be39d5660a6e5a`.
The new file strengthens checks for the preprocessed and trace tree lifting
logs and maximum column log size. It does not change the frozen V24 source,
claims, predicted manifest layout, cost-model formula, or gates.

The amendment pins compiler base `6f35bc5802a919e141b6e91248c0d918d9082c0b`,
compiler SHA-256 `9673ab910d98f9558b98faf1663c4b9a0a664f81b838e9217a6752e9bc67b9cf`,
and the amended `freeze.py` tool hash. The resulting canonical protocol SHA-256
is `7d99d482c0cfc4a79ad16eaa152d2a4cce316c73dae416a1c189b63020ef3a80`.
A keyed comparison of old and new canonical protocol objects found differences
**only** in `current_revision`, `compiler_sha256`, the one
`current_pin_sha256` entry, and `tool_sha256["freeze.py"]`. Source SHA-256
remains `9755a1005c8533607e2457b3c900f6d0d81cb4dabfed3b02697c57d0357ee5f9`.

The amended preregistration must be committed, independently checked, and
pushed to the PR before the single quiet-host native attempt. If strict
`freeze.py check` rejects again because the compiler stack changed, stop and
record another pre-native amendment. V17 and V23 remain failed holdouts.
