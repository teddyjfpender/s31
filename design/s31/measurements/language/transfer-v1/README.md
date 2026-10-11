# V6 transfer measurements

These four JSON files are the compact measured corpora and diagnostic audits
for the two runs described in [the transfer report](../../WHOLE_PROVER_TRANSFER_V1.md).
The frozen source and assignment protocol lives one directory above as
`whole-prover-transfer-v1.json` because the runner pins that exact path.

The raw proof binaries, verifier statements, full trial reports and package
artifacts remain in the local ignored `zig-out/s31-cost-transfer-v1` and
`zig-out/s31-cost-transfer-v1-repeat` directories. The JSON corpora bind their
digests but cannot replace those raw artifacts for third-party replay.
