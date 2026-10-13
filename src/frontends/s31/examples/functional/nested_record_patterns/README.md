# Nested record patterns

[`nested.s31`](nested.s31) names a nested record field, renames `base` to
`a`, and destructures a tuple field directly in a helper parameter:

```s31
fn compute(Inputs {
    terms: Terms { base: a, boost },
    pair: (b, c),
}: Inputs) -> [m31; 1] {
    let (product, saved) = (a .* b, boost + c);
    product + saved
}
```

The constructor supplies `terms.base = y`, `terms.boost = x`, and
`pair = (x, y)`. For `x=7` and `y=11`, the result is
`7·11 + 7 + 11 = 95` in M31. The names and product structure are checked at
compile time. The compiler evaluates the constructor once and replaces each
pattern leaf with a typed field or tuple projection. Only three arithmetic
nodes remain:

```text
product = y * x
saved   = x + y
result  = product + saved
```

[`direct.s31`](direct.s31) writes those operations directly. A focused test
checks that both files produce the **exact same normalized relation**, then
checks four assignments and rejects false public results. Record and tuple
patterns themselves add no relation node. Running `s31 explain` on both files
under the default `circuit-v1` profile reports the same canonical IR digest
`f49488afa3a59bba37f1e5f3db14599ed062301b6e06c496bc862940959cc5e9`,
278 raw QM31 operation rows, 512 padded QM31 rows, and 45 preprocessed
columns. These are measurements for this source and profile; other profiles
can have different layouts. Unselected constructor fields still evaluate, so
their arithmetic or possible failures cannot disappear merely because a
pattern omits them.
