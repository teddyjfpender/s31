//! Constructive binding reduction for two full native Merkle openings.
//!
//! For the same root, height and index, two different canonical M31 rows
//! cannot both be accepted unless their leaf encodings collide or two
//! different ordered child pairs collide. The returned certificate borrows
//! the input rows and must not outlive them. This is an executable reduction,
//! not a collision-resistance estimate for BLAKE2s or a proof that a native
//! compressed multiproof produced either full path.
const std = @import("std");
const core = @import("stwo_core");
const M31 = core.fields.m31.M31;
const modulus = core.fields.m31.Modulus;

pub fn Reduction(comptime H: type) type {
    return struct {
        const Self = @This();
        pub const Hash = H.Hash;
        pub const Collision = union(enum) {
            leaf: struct {
                first_row: []const M31,
                second_row: []const M31,
                digest: Hash,
            },
            parent: struct {
                first_children: H.Children,
                second_children: H.Children,
                digest: Hash,
                level: usize,
            },
        };

        fn hashEq(a: Hash, b: Hash) bool {
            return std.meta.eql(a, b);
        }

        fn childrenEq(a: H.Children, b: H.Children) bool {
            return hashEq(a.left, b.left) and hashEq(a.right, b.right);
        }

        fn rowsEq(a: []const M31, b: []const M31) bool {
            if (a.len != b.len) return false;
            for (a, b) |x, y| if (!x.eql(y)) return false;
            return true;
        }

        fn canonical(row: []const M31) bool {
            for (row) |value| if (value.v >= modulus) return false;
            return true;
        }

        fn leafHash(row: []const M31) Hash {
            var hasher = H.defaultWithInitialState();
            hasher.updateLeaf(row);
            return hasher.finalize();
        }

        fn children(position: usize, current: Hash, sibling: Hash) H.Children {
            return if (position & 1 == 0)
                .{ .left = current, .right = sibling }
            else
                .{ .left = sibling, .right = current };
        }

        fn pathRoot(position: usize, row: []const M31, path: []const Hash) Hash {
            var index = position;
            var current = leafHash(row);
            for (path) |sibling| {
                current = H.hashChildren(children(index, current, sibling));
                index >>= 1;
            }
            return current;
        }

        /// Audit the caller-order full paths of one accepted capture. Native
        /// compressed decoding deduplicates positions, then copies the same
        /// path back to each occurrence. This independent check is bounded
        /// by the query count and allocates nothing. It is not installed in
        /// the production verifier.
        pub fn auditDuplicateQueries(
            height: usize,
            positions: []const usize,
            rows: []const []const M31,
            paths: []const []const Hash,
        ) error{ InvalidOpening, DuplicateMismatch }!void {
            if (height >= @bitSizeOf(usize) or positions.len != rows.len or
                positions.len != paths.len)
                return error.InvalidOpening;
            const domain_size: usize = @as(usize, 1) << @intCast(height);
            for (positions, rows, paths, 0..) |position, row, path, i| {
                if (position >= domain_size or row.len == 0 or !canonical(row) or
                    path.len != height)
                    return error.InvalidOpening;
                for (positions[0..i], 0..) |prior_position, j| {
                    if (position != prior_position) continue;
                    if (!rowsEq(row, rows[j]) or !std.mem.eql(Hash, path, paths[j]))
                        return error.DuplicateMismatch;
                }
            }
        }

        /// Validate a concrete collision certificate against this hasher.
        /// For canonical M31 rows of equal length, distinct rows have
        /// distinct little-endian leaf byte strings in the native encoding.
        pub fn check(collision: Collision) bool {
            return switch (collision) {
                .leaf => |leaf| leaf.first_row.len == leaf.second_row.len and
                    canonical(leaf.first_row) and canonical(leaf.second_row) and
                    !rowsEq(leaf.first_row, leaf.second_row) and
                    hashEq(leafHash(leaf.first_row), leaf.digest) and
                    hashEq(leafHash(leaf.second_row), leaf.digest),
                .parent => |parent| !childrenEq(parent.first_children, parent.second_children) and
                    hashEq(H.hashChildren(parent.first_children), parent.digest) and
                    hashEq(H.hashChildren(parent.second_children), parent.digest),
            };
        }

        /// Either opening must be well shaped and replay to `root`. This
        /// function is uniform in every representable depth below usize's
        /// word width; it does not enumerate a finite subset of trees.
        pub fn extract(
            root: Hash,
            height: usize,
            position: usize,
            first_row: []const M31,
            first_path: []const Hash,
            second_row: []const M31,
            second_path: []const Hash,
        ) error{ InvalidOpening, SameRow, InternalInvariant }!Collision {
            if (height >= @bitSizeOf(usize) or position >= (@as(usize, 1) << @intCast(height)) or
                first_row.len == 0 or first_row.len != second_row.len or
                first_path.len != height or second_path.len != height or
                !canonical(first_row) or !canonical(second_row))
                return error.InvalidOpening;
            if (!hashEq(pathRoot(position, first_row, first_path), root) or
                !hashEq(pathRoot(position, second_row, second_path), root))
                return error.InvalidOpening;
            if (rowsEq(first_row, second_row)) return error.SameRow;

            var first = leafHash(first_row);
            var second = leafHash(second_row);
            if (hashEq(first, second)) {
                const collision: Collision = .{ .leaf = .{
                    .first_row = first_row, .second_row = second_row, .digest = first,
                } };
                std.debug.assert(Self.check(collision));
                return collision;
            }
            var index = position;
            for (first_path, second_path, 0..) |first_sibling, second_sibling, level| {
                const first_children = children(index, first, first_sibling);
                const second_children = children(index, second, second_sibling);
                const next_first = H.hashChildren(first_children);
                const next_second = H.hashChildren(second_children);
                if (!childrenEq(first_children, second_children) and
                    hashEq(next_first, next_second))
                {
                    const collision: Collision = .{ .parent = .{
                        .first_children = first_children,
                        .second_children = second_children,
                        .digest = next_first,
                        .level = level,
                    } };
                    std.debug.assert(Self.check(collision));
                    return collision;
                }
                first = next_first;
                second = next_second;
                index >>= 1;
            }
            // Equal roots and unequal initial leaf hashes imply a first
            // equal parent output with distinct ordered inputs.
            return error.InternalInvariant;
        }
    };
}
