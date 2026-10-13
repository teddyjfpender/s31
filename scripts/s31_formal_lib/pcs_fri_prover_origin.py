"""Pinned source path for lifted prover column-to-root origin.

This is a change detector for the reviewed Zig paths, not a Zig semantics
proof. The native oracle test separately compares all retained nodes with an
independently projected and hashed complete tree.
"""
from __future__ import annotations

from pathlib import Path
from typing import Mapping

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region
from scripts.s31_formal_lib.pcs_fri_capture import check_capture_source

SOURCE_PATHS = {
    "columns": "deps/stwo-zig/src/prover/vcs_lifted/columns.zig",
    "leaves": "deps/stwo-zig/src/prover/vcs_lifted/leaves.zig",
    "expand": "deps/stwo-zig/src/prover/vcs_lifted/expand.zig",
    "layers": "deps/stwo-zig/src/prover/vcs_lifted/layers.zig",
    "prover": "deps/stwo-zig/src/prover/vcs_lifted/prover.zig",
    "revision": "deps/stwo-zig/src/prover/pcs/revision_lifting.zig",
    "commitment_tree": "deps/stwo-zig/src/prover/pcs/commitment_tree.zig",
    "commit_ops": "deps/stwo-zig/src/prover/pcs/commit_ops.zig",
    "cpu_backend": "deps/stwo-zig/src/backends/cpu_scalar/mod.zig",
    "s31_integration": "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig",
    "tiled": "deps/stwo-zig/src/prover/pcs/tiled_commit.zig",
    "streaming": "deps/stwo-zig/src/prover/vcs_lifted/streaming_committer.zig",
    "tree_builders": "deps/stwo-zig/src/prover/pcs/tree_builders.zig",
    "decommit": "deps/stwo-zig/src/prover/vcs_lifted/decommit.zig",
    "backend": "deps/stwo-zig/src/core/crypto/blake2s_backend.zig",
    "verifier": "deps/stwo-zig/src/core/vcs_lifted/verifier.zig",
}


def check_prover_origin_texts(source: Mapping[str, str]) -> None:
    columns = source["columns"]
    ordered_once(region(columns, "pub fn sortByLogSizeAsc(", "pub fn allConstant("),
                 "lifted prover origin column sort",
                 "if (!std.math.isPowerOfTwo(column.len) or column.len < 2)",
                 ".values = column,",
                 ".log_size = @intCast(std.math.log2_int(usize, column.len)),",
                 ".original_index = index,",
                 "std.sort.heap(ColumnRef, result, {}, lessByLogSizeAscStable);")
    ordered_once(region(columns, "fn lessByLogSizeAscStable(",
                        'test "lifted VCS columns retain stable order'),
                 "lifted prover origin tie order",
                 "if (lhs.log_size == rhs.log_size) return lhs.original_index < rhs.original_index;",
                 "return lhs.log_size < rhs.log_size;")

    prover = source["prover"]
    ordered_once(region(prover, "fn commitWithOptions(", "const allColumnsConstant"),
                 "lifted prover origin commitment",
                 "const sorted = try sortColumnsByLogSizeAsc(allocator, columns);",
                 "const height = lifting_log_size orelse max_col_log_size;",
                 "if (height < max_col_log_size or (sorted.len == 0 and height != 0))",
                 "if (allColumnsConstant(sorted)) {",
                 "LeafOps.buildBatched(allocator, layer_alloc, sorted, batch_size);",
                 "LeafOps.build(allocator, layer_alloc, sorted);",
                 "const leaves = try liftLeaves(layer_alloc, column_leaves, height - max_col_log_size);",
                 "try LayerOps.buildUpperLayersSubtree(",
                 "out_layers[i] = layers_bottom_up.items[out_layers.len - 1 - i];")
    ordered_once(region(prover, "fn liftLeaves(", "fn commitConstantColumns("),
                 "lifted prover origin final replication",
                 "if (log_ratio == 0) return leaves;",
                 "HashExpandOps.expandHashers(lifted, leaves, @intCast(log_ratio + 1));")
    ordered_once(region(prover, "pub fn liftTo(", "fn liftLeaves("),
                 "lifted prover origin post-commit lift",
                 "if (lifting_log_size == natural) return;",
                 "if (lifting_log_size < natural) return error.InvalidTreeHeight;",
                 "const leaves = self.layers[natural];",
                 "const lifted = try liftLeaves(",
                 "const rebuilt = try buildTreeFromOwnedLeaves(",
                 "self.* = rebuilt;")
    ordered_once(region(prover, "fn commitConstantColumns(", "pub fn compactForQueries("),
                 "lifted prover origin constant path",
                 "for (columns) |column| leaf_hasher.updateLeaf(column.values[0..1]);",
                 "@memset(leaves, leaf_hash);",
                 "child_hash = H.hashChildren(.{ .left = child_hash, .right = child_hash });")

    leaves = source["leaves"]
    ordered_once(region(leaves, "fn buildLeavesBatchedRange4(", "fn buildLeavesDirectRange4("),
                 "lifted prover origin optimized leaves",
                 'if (comptime @hasDecl(H, "hashDirectLiftedM31LeavesWithSeed4")) {',
                 "H.hashDirectLiftedM31LeavesWithSeed4(seed, ctx.sorted_columns, position, ctx.max_log_size);",
                 "H.hashPackedLeavesWithSeed4(seed, &messages);",
                 "const source_index = ((position >> shift_amt) << 1) + (position & 1);",
                 "hasher.updateLeaf(column.values[source_index .. source_index + 1]);",
                 "ctx.out[position] = hasher.finalize();")
    packed = region(leaves, "fn packBatchedLeafMessages(",
                    "fn buildLeavesBatchedRangeScalar(")
    projection = "const source_index = ((leaf_position >> shift_amt) << 1) + (leaf_position & 1);"
    if packed.count(projection) != 2:
        raise ValueError("lifted prover origin packed row projection changed")
    ordered_once(packed, "lifted prover origin packed row",
                 "const words = std.mem.bytesAsSlice(M31, buffer);",
                 "words[lane * ctx.sorted_columns.len + column_index] = column.values[source_index];",
                 "const encoded = column.values[source_index].toBytesLe();")

    expand = source["expand"]
    ordered_once(region(expand, "fn expandRange(", "pub fn expandHashers("),
                 "lifted prover origin leaf replication",
                 "const run = idx >> ctx.shift;",
                 "const even = ctx.src[2 * run];",
                 "const odd = ctx.src[2 * run + 1];",
                 "ctx.dst[at] = if ((at & 1) == 0) even else odd;")

    backend = source["backend"]
    ordered_once(region(backend, "pub fn hashLiftedM31Columns4WithMode(",
                        "fn addCounter("),
                 "lifted prover origin SIMD projection",
                 "hashM31Columns4FromStateWithMode(mode, seed orelse Self.initWithMode(mode).h, if (seed != null) 64 else 0, columns, position, true, max_log_size)",
                 "const index = if (lifted) (((position + lane) >>",
                 "const index = (position >> shift) << 1;",
                 "const a = column.values[index].v;",
                 "const b = column.values[index + 1].v;",
                 "return .{ a, b, a, b };")

    layers = source["layers"]
    layer_builder = region(layers, "pub fn buildNextLayer(",
                           "pub fn buildUpperLayersSubtree(")
    if layer_builder.count("const out = try allocator.alloc(H.Hash, prev_layer.len >> 1);") != 1:
        raise ValueError("lifted prover origin parent layer size changed")
    for stage in ("out[i] = H.hashChildren(.{",
                  ".left = prev_layer[2 * i],",
                  ".right = prev_layer[2 * i + 1],"):
        if layer_builder.count(stage) != 2:
            raise ValueError(f"lifted prover origin parent hashing changed: {stage}")

    decommit = source["decommit"]
    ordered_once(region(decommit, "fn readQueriedValuesHost(",
                        "fn freeQueriedValues("),
                 "lifted prover origin queried values",
                 "const shift_amt: std.math.Log2Int(usize) = @intCast(shift + 1);",
                 "const column_index = ((position >> shift_amt) << 1) + (position & 1);",
                 "if (column_index >= column.len) return error.InvalidColumnSize;",
                 "value.* = column[column_index];")
    revision = source["revision"]
    ordered_once(region(revision, "pub fn liftCommittedTree(",
                        "pub fn maskLogSize("),
                 "lifted prover origin PCS handoff",
                 "const height = try config.treeHeight(tree_index, log_sizes);",
                 "if (height == tree.commitment.maxLogSize()) return;",
                 "tree.commitment.liftTo(allocator, height) catch |err| switch (err) {",
                 "error.InvalidColumnSize => return recommitLifted(H, allocator, tree, height),",
                 "var lifted = try Tree.commitLifted(allocator, columns, height);")
    commitment_tree = source["commitment_tree"]
    ordered_once(region(commitment_tree, "pub const HostMerkleBackend = struct {",
                        "pub fn CommitmentTreeProver(comptime H: type) type {"),
                 "lifted prover origin host backend",
                 "return vcs_lifted_prover.MerkleProverLifted(H);",
                 "return MerkleTree(H).commit(allocator, columns);")
    ordered_once(region(commitment_tree, "pub fn compactPolynomialStorage(",
                        "pub fn releaseCoefficients("),
                 "lifted prover origin retained compact columns",
                 "const coefficients = self.coefficients orelse return error.MissingCompactCoefficients;",
                 "if (column.log_size < minimum_log_size) {",
                 "column.values = &.{};",
                 "column.coefficient_values = coefficient.coefficients();",
                 "self.compact_polynomials = true;")
    cpu_backend = source["cpu_backend"]
    ordered_once(region(cpu_backend, "pub fn MerkleTree(comptime H: type) type {",
                        "pub fn commitLazyMerkle("),
                 "lifted prover origin S31 CPU backend",
                 "return lifted_merkle.MerkleProverLifted(H);",
                 "return MerkleTree(H).commit(allocator, columns);")
    integration = source["s31_integration"]
    if integration.count('const CpuBackend = @import("stwo_cpu_backend").configured(.{ .wide_preparation = true });') != 1:
        raise ValueError("lifted prover origin S31 CPU backend selection changed")
    ordered_once(region(integration, "fn commit(scheme: *Engine.Scheme,",
                        "fn commitBorrowed(scheme: *Engine.Scheme,"),
                 "lifted prover origin S31 commit routing",
                 "else if (tiles(scheme, columns))",
                 "prover.pcs.tiled_commit.commit(CpuBackend, Hasher, scheme, allocator, columns, .owned, .{}, channel)",
                 "scheme.commitOwnedStreamingWithRecorder(allocator, columns, 0, null, channel);",
                 "try Engine.flushPendingCommit(scheme, allocator, channel);")
    ordered_once(region(integration, "fn commitBorrowed(scheme: *Engine.Scheme,",
                        "fn tiles(scheme: *const Engine.Scheme,"),
                 "lifted prover origin S31 borrowed route",
                 "if (tiles(scheme, columns)) {",
                 "const descriptors = try allocator.dupe(prover.pcs.ColumnEvaluation, columns);",
                 "prover.pcs.tiled_commit.commit(CpuBackend, Hasher, scheme, allocator, descriptors, .borrowed, .{}, channel);",
                 "scheme.commitBorrowedStreamingWithRecorder(allocator, columns, 0, null, channel);",
                 "try Engine.flushPendingCommit(scheme, allocator, channel);")
    tiled = source["tiled"]
    ordered_once(region(tiled, "pub fn commit(", "fn hashParents("),
                 "lifted prover origin tiled route",
                 "std.sort.heap(usize, order, HeightOrder{ .columns = columns }, HeightOrder.less);",
                 "for (order, refs) |index, *ref| {",
                 "const leaves = try LeafOps.buildBatched(allocator, allocator, refs, 1024);",
                 "hashParents(H, current, out);",
                 "while (level > 0) : (level -= 1) hashParents(H, merkle.layers[level], merkle.layers[level - 1]);")
    ordered_once(region(tiled, "// 6. The compact tree:", "fn adopt("),
                 "lifted prover origin tiled coefficient ownership",
                 "const tree_columns = try allocator.alloc(ColumnEvaluation, n);",
                 "coefficient.* = try CircleCoefficients.initOwned(buffer);",
                 "tree_column.* = if (values.len != 0)",
                 ".{ .log_size = log, .values = values }",
                 ".{ .log_size = log, .values = &.{}, .coefficient_values = buffer };",
                 ".compact_polynomials = true,",
                 "try scheme.appendCommittedTree(allocator, tree, channel);")
    commit_ops = source["commit_ops"]
    ordered_once(region(commit_ops, "fn commitStreamingWithBacking(", "fn boundedBatchEnd("),
                 "lifted prover origin streaming input ownership",
                 "std.sort.heap(",
                 "try builder.planCompactTree(owned_columns, order);",
                 "const column = owned_columns[original_index];",
                 "const values = allocator.dupe(M31, column.values)",
                 "try tree_builders.addColumnsOwnedIndexed(&builder, batch, order[consumed..end], recorder);",
                 "try builder.commitWithRecorder(recorder, channel);")
    streaming = source["streaming"]
    if streaming.count("const next_layer = try LayerOps.buildNextLayer(") != 1 or \
            streaming.count("out_layers[i] = layers_bottom_up.items[out_layers.len - 1 - i];") != 1:
        raise ValueError("lifted prover origin streaming parent construction changed")
    tree_builders = source["tree_builders"]
    ordered_once(region(tree_builders, "pub fn appendCommittedTree(",
                        "pub fn addColumnsOwnedIndexed("),
                 "lifted prover origin root publication",
                 "try scheme.liftCommittedTree(allocator, &retained);",
                 "scheme.trees.appendAssumeCapacity(retained);",
                 "const root = retained.root();",
                 "MC.mixRoot(channel, root);")
    check_capture_source(source["verifier"])


def check_pcs_fri_prover_origin(root: Path) -> None:
    check_prover_origin_texts({key: (root / path).read_text()
                               for key, path in SOURCE_PATHS.items()})
