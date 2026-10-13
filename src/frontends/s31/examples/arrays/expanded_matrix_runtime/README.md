# Explicit runtime matrix relation

`relation.s31.json` records the former eager lowering of
`array_matrix_runtime.s31`: two aligned four-lane slices, one concatenation,
and the final selection. The adjacent assignment gives the claimed value 17.
The Zig relation compiler test uses these files to keep exercising explicit
slice and concat lowering after the text compiler began erasing complete
ordered reshape/flatten views. The original text example now has a separate
normalized relation containing only `array_get`.
