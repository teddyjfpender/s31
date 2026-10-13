"""Independent finite check of pinned lifted-Merkle leaf bytes and path replay.

The oracle roots below came from proving@5a7c5ed (and are also pinned in
stwo-zig's lifted_height_vectors.zig). This checks concrete serialization and
ordering; it is not a proof of collision resistance or arbitrary Zig execution.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path

P = (1 << 31) - 1
LOG_SIZES = (3, 2, 3)
SEEDS = (1, 2, 3)
ORACLE = (
    (3, "4d815dfd1faaf9ee64abe37788572597d44687a4b14283cd4256cebc59b920ad",
     (7, 3, 1, 3), ((1050, 1022, 1008, 1022), (2022, 2008, 2008, 2008),
                     (3050, 3022, 3008, 3022))),
    (4, "360cb50ca1456aafe2955cafde0170044ddf40c48bd68ed4226488069566e82e",
     (15, 3, 1, 3), ((1050, 1008, 1008, 1008), (2022, 2008, 2008, 2008),
                      (3050, 3008, 3008, 3008))),
    (6, "0901de9e022cc45e99374aadbae503cfffcfd1c8f8e04c1fff02d564b018b4b4",
     (63, 3, 1, 3), ((1050, 1008, 1008, 1008), (2022, 2008, 2008, 2008),
                      (3050, 3008, 3008, 3008))),
)

SOURCE_ANCHORS = {
    "deps/stwo-zig/src/core/vcs_lifted/channel_profile.zig": (
        "pub const MerkleHasher = blake2_merkle.Blake2sPlainMerkleHasher;",
        "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{",
    ),
    "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig": (
        "return Blake2sMerkleHasherProtocolGeneric(is_m31_output, .plain);",
        "if (comptime hash_protocol == .domain_prefixed) hasher.inner.update(LEAF_PREFIX[0..]);",
        "return InnerHasher.concatAndHashWithMode(mode, children.left, children.right);",
        "self.inner.update(std.mem.sliceAsBytes(column_values));",
        "const value_bytes = column_values[at + i].toBytesLe();",
        "self.inner.update(packed_bytes);",
    ),
    "deps/stwo-zig/src/prover/vcs_lifted/columns.zig": (
        "std.sort.heap(ColumnRef, result, {}, lessByLogSizeAscStable);",
        "if (lhs.log_size == rhs.log_size) return lhs.original_index < rhs.original_index;",
        "return lhs.log_size < rhs.log_size;",
    ),
    "deps/stwo-zig/src/prover/vcs_lifted/leaves.zig": (
        "const column_index = ((position >> shift_amt) << 1) + (position & 1);",
        "words[lane * ctx.sorted_columns.len + column_index] = column.values[source_index];",
        "const encoded = column.values[source_index].toBytesLe();",
        "hasher.updateLeaf(column.values[source_index .. source_index + 1]);",
    ),
    "deps/stwo-zig/src/core/crypto/blake2s_backend.zig": (
        "const index = if (lifted) (((position + lane) >> @as(std.math.Log2Int(usize), @intCast(max_log_size - column.log_size + 1))) << 1) + ((position + lane) & 1) else position + lane;",
        "std.mem.writeInt(u32, &encoded, column.values[index].v, .little);",
        "return .{ a, b, a, b };",
    ),
    "deps/stwo-zig/src/core/fields/m31.zig": (
        "pub const Modulus: u32 = 0x7fffffff;",
        "std.debug.assert(x < Modulus);",
        "pub fn toBytesLe(self: M31) [4]u8 {",
    ),
    "deps/stwo-zig/src/core/vcs_lifted/verifier.zig": (
        "std.sort.heap(usize, col_indices, self.column_log_sizes, lessByLogSize);",
        "if (lhs_size == rhs_size) return lhs < rhs;",
        "dedup_cols[j] = try dedup.toOwnedSlice(allocator);",
        "row[col_i] = col[col_pos[col_i]];",
        "hasher.updateLeaf(row);",
        "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root))",
    ),
    "src/frontends/s31/runtime/native_verifier.zig": (
        "const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;",
        "const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;",
    ),
}

# Repeated fast/scalar branches are all relevant; losing one copy must fail.
SOURCE_OCCURRENCES = {
    "return InnerHasher.concatAndHashWithMode(mode, children.left, children.right);": 2,
    "const column_index = ((position >> shift_amt) << 1) + (position & 1);": 4,
    "hasher.updateLeaf(column.values[source_index .. source_index + 1]);": 2,
}


def source_texts(root: Path) -> dict[str, str]:
    return {name: (root / name).read_text() for name in SOURCE_ANCHORS}


def check_sources(sources: dict[str, str]) -> None:
    for name, anchors in SOURCE_ANCHORS.items():
        source = sources[name]
        for anchor in anchors:
            if source.count(anchor) != SOURCE_OCCURRENCES.get(anchor, 1):
                raise ValueError(f"Merkle leaf source changed: {name}: {anchor!r}")


def source_index(position: int, height: int, column_log: int) -> int:
    if not (1 <= column_log <= height and 0 <= position < 1 << height):
        raise ValueError("leaf position or column height outside domain")
    return ((position >> (height - column_log + 1)) << 1) + (position & 1)


def oracle_column(column: int, index: int) -> int:
    return SEEDS[column] * 1000 + 7 * index + 1


def row(position: int, height: int) -> tuple[int, ...]:
    # This is the prover's log-size sort and the verifier's same-size tie rule.
    order = sorted(range(len(LOG_SIZES)), key=lambda i: (LOG_SIZES[i], i))
    return tuple(oracle_column(i, source_index(position, height, LOG_SIZES[i]))
                 for i in order)


def encode_row(values: tuple[int, ...]) -> bytes:
    if any(not 0 <= value < P for value in values):
        raise ValueError("noncanonical M31 word in leaf")
    return b"".join(value.to_bytes(4, "little") for value in values)


def digest(payload: bytes) -> bytes:
    return hashlib.blake2s(payload).digest()


def tree(height: int) -> list[list[bytes]]:
    leaves = [digest(encode_row(row(position, height))) for position in range(1 << height)]
    layers = [leaves]
    while len(layers[-1]) > 1:
        lower = layers[-1]
        layers.append([digest(lower[i] + lower[i + 1]) for i in range(0, len(lower), 2)])
    return layers


def path(layers: list[list[bytes]], position: int) -> tuple[bytes, ...]:
    return tuple(layer[(position >> depth) ^ 1] for depth, layer in enumerate(layers[:-1]))


def replay(row_values: tuple[int, ...], position: int, siblings: tuple[bytes, ...]) -> bytes:
    current = digest(encode_row(row_values))
    for sibling in siblings:
        current = digest(current + sibling) if position & 1 == 0 else digest(sibling + current)
        position >>= 1
    if position:
        raise ValueError("query exceeds path height")
    return current


def check_oracle(root: Path) -> int:
    source = (root / "deps/stwo-zig/src/core/vcs_lifted/testdata/lifted_height_vectors.zig").read_text()
    for anchor in ("pub const column_log_sizes = [_]u32{ 3, 2, 3 };",
                   "const column_seeds = [_]u32{ 1, 2, 3 };",
                   "return column_seeds[column] * 1000 + @as(u32, @intCast(row)) * 7 + 1;"):
        if anchor not in source:
            raise ValueError("Merkle Rust oracle column fixture changed")
    parsed = []
    for height, root_hex, positions, value_text in re.findall(
        r'\.height = (\d+),\s*\.root = "([0-9a-f]{64})",\s*'
        r'\.positions = &\.\{([^}]*)\},\s*\.values = &\.\{(.*?)\},\s*\.witness =',
        source, re.S,
    ):
        columns = tuple(tuple(int(word.strip()) for word in words.split(",") if word.strip())
                        for words in re.findall(r'&\.\{([^}]*)\}', value_text))
        parsed.append((int(height), root_hex,
                       tuple(int(word.strip()) for word in positions.split(",") if word.strip()),
                       columns))
    if tuple(parsed) != ORACLE:
        raise ValueError("Merkle Rust oracle root, position or value fixture changed")
    checked = 0
    for height, root_hex, positions, values in ORACLE:
        layers = tree(height)
        expected_root = bytes.fromhex(root_hex)
        if layers[-1] != [expected_root]:
            raise ValueError(f"independent leaf tree disagrees with Rust oracle at height {height}")
        for query_index, position in enumerate(positions):
            for column_index, column_log in enumerate(LOG_SIZES):
                expected = oracle_column(column_index, source_index(position, height, column_log))
                if values[column_index][query_index] != expected:
                    raise ValueError("oracle queried value differs from projected column")
            if replay(row(position, height), position, path(layers, position)) != expected_root:
                raise ValueError("independent opening failed root replay")
            checked += 1
    if digest(b"").hex() != "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9":
        raise ValueError("empty leaf disagrees with plain Blake2s oracle")
    return checked


def check_pcs_fri_leaf_encoding(root: Path) -> int:
    check_sources(source_texts(root))
    return check_oracle(root)
