# Static functions and zero-cost source abstractions

S31 now has a small functional source core: lexical `let … in` expressions,
typed `fun` values, closures, and functions that take or return functions.
Function values exist **only in the compiler**. A circuit input or output must
still have a first-order S31 value type. Application specializes the function
at the call site and emits only the underlying relation operations.

## A complete program

The checked-in [source](../examples/arithmetic/functional_square4.s31) is:

```s31
use std@1;

fn apply_twice(f: Fn([m31; 4]) -> [m31; 4], x: [m31; 4]) -> [m31; 4] {
    let once = f(x);
    f(once)
}

circuit functional_square4(public x: [m31; 4]) -> public [m31; 4] {
    let square = fun(v: [m31; 4]) -> [m31; 4] => v .* v;
    let result = apply_twice(square, x);
    result
}
```

`Fn(A) -> B` denotes a compile-time function. `fun(v: A) -> B => body`
constructs one with an explicit result type. Function values can be passed to
other functions, returned, or kept in a local binding; they cannot be public or
private circuit values. `let name = value in body` makes a lexically scoped
expression binding and permits intentional shadowing. Statements of the form
`let name = value;` remain available in function and circuit blocks.

After specialization, the normalized relation has just two nodes:

| Node | Operation | Meaning on each of four M31 lanes |
| --- | --- | --- |
| `w₁` | `mul(x, x)` | `w₁ = x²` |
| `result` | `mul(w₁, w₁)` | `result = x⁴` |

There is no closure node, call node, function table, or function witness. The
[first-order reference](../examples/arithmetic/functional_square4_manual.s31)
emits the same two `mul` nodes. The
[native acceptance gate](../tests/acceptance/acceptance_functional_core.py)
builds both sources and checks equal canonical IR, raw and padded rows,
preprocessed cells and root, public binding, and FRI settings. On the current
`direct-gate` profile each has 322 raw QM31 rows, 512 padded QM31 rows and
4,096 preprocessed cells. Those totals include generic circuit and public
binding overhead, not only the two multiplication gates. Their circuit hashes
differ because the source digest is deliberately bound into package identity.

Run the source through the existing native proof pipeline:

```sh
python3 src/frontends/s31/python/s31.py lower src/frontends/s31/examples/arithmetic/functional_square4.s31
python3 src/frontends/s31/python/s31.py trial \
  src/frontends/s31/examples/arithmetic/functional_square4.s31 \
  src/frontends/s31/examples/arithmetic/functional_square4.valid.json \
  --lowering direct-gate --out zig-out/s31/functional-square4-trial
python3 src/frontends/s31/tests/acceptance/acceptance_functional_core.py
```

The trial checks the independent oracle, creates a native proof, runs the
generated verifier, and confirms that a changed public result is rejected.

## Evaluation and staging

Let `ρ` map source names to compile-time values or references to circuit
values. A binding evaluates its right-hand side once and extends the scope:

```text
eval(let x = e₁ in e₂, ρ) = eval(e₂, ρ[x ↦ eval(e₁, ρ)])
```

A `fun` captures its lexical `ρ` without emitting a relation node. Applying
it checks the declared argument types, extends the captured environment with
the supplied arguments, then specializes its body. This matters when an outer
name is shadowed: the closure still reads the value it captured. Calls and
bindings do not add gates; primitive operations in the specialized body do.
The compiler rejects recursion and caps expansion depth at 32 so circuit
shape remains statically finite. `iterate` retains its restricted named-step
recognizer and its existing chip selection rules.

This design uses the **static/dynamic separation** of partial evaluation:
functions, closures and source scopes are static; field words, bits and
relation nodes are dynamic. The implementation specializes directly into the
existing relation builder. It does not yet implement a general normalization
by evaluation engine, closure conversion, or ANF pass. Those are useful design
tools for a larger typed core, as described by
[Jones, Gomard and Sestoft](https://studwww.itu.dk/people/sestoft/pebook/),
[Danvy and Nielsen](https://tidsskrift.dk/brics/article/view/21684), and
[Flanagan, Sabry, Duba and Felleisen](https://felleisen.org/matthias/papers.html).

## Exact safety boundary

Circuit inputs and outputs reject `Fn` types. A pure elaboration pass checks
every function and lambda body, including unused ones, before specialization
emits relation nodes. It checks source types, lexical scopes, builtin
signatures, static array shapes, and the whole-program function call graph.
Recursive or over-depth call chains are rejected even when unused.
Source-level assertions remain confined to circuit blocks. Specialization
then checks value-dependent facts such as constant inverse failures,
constrained-bit provenance, and the restricted `iterate` step form. There is
no witness-dependent branch in this core. This avoids silently treating a
partial operation such as checked inversion in an inactive branch as though
it need not be proved.

This is a usable **functional subset**, not a completed v0.1.0 language
release. Before a release claim, S31 still needs a defined
conditional/effect model, broader parser diagnostics and adversarial grammar
tests, a correspondence proof for the production Python elaborator and
specializer, and a release gate that
compares generated AIR geometry with equivalent first-order sources across
all supported profiles. The [Lean package](../../../../formal/s31/README.md)
proves semantic preservation for a small typed field/function core and its
strict graph constraints; it does not prove this Python parser or all builtin
typing/lowering rules correct.
