# Any finite roster of indexed chip paths

[`IndexedManyChipPath.lean`](IndexedManyChipPath.lean) extends the exact-event
argument from two fixed calls to **any finite number** of calls. Each call may
have its own positive round count and transition function. The call tag is
part of every event. The theorem first filters a joint event permutation by
that tag, then applies the arbitrary-row index/path theorem to each call.
For the admitted bound of at most eight calls, it also proves that the
canonical IDs `0..N-1` remain distinct when embedded in M31.

Here is a small integer example. A chip row at index `i` consumes
`(call, i, input)` and produces `(call, i+1, output)`. An external bridge
produces `(call, 0, start)` and consumes `(call, R, finish)`.

| Call | R | Bridge start | Row events, in index order | Bridge finish |
| --- | ---: | ---: | --- | ---: |
| A | 1 | 2 | `(A,0,2) → (A,1,3)` | 3 |
| B | 2 | 5 | `(B,0,5) → (B,1,6)`, `(B,1,6) → (B,2,7)` | 7 |
| C | 3 | 8 | `(C,0,8) → (C,1,9)`, `(C,1,9) → (C,2,10)`, `(C,2,10) → (C,3,11)` | 11 |

For these rows the local rule is `output = input + 1`. The combined event
multiset balances: each consumed tuple has exactly one matching produced
tuple. Filtering by `B` leaves only B's three joins, so the path theorem
forces `7 = 5 + 2`. A malicious B row that reads `(B,1,8)` cannot borrow
`(C,1,9)` or `(A,1,3)` to balance its read: the call tag differs. The same
argument works even if rows are stored out of index order.

The theorem starts from an **exact** permutation of tagged tuples, checked
local transition equations, and `0 < R < p` for every call. It does not show
that the current native one-to-eight-call proof's random compressed LogUp
check implies that exact permutation, that a generated manifest binds the
call tags and row counts, or that PCS openings authenticate the row values.
Those are separate verifier and cryptographic obligations.
