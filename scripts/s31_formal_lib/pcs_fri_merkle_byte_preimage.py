"""Source-bound plain Merkle byte messages for the Lean P06 preimage lemma.

This pins selected production source stages; the native differential checks
the actual hash results. Neither establishes BLAKE2s collision resistance.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


FILES = (
    "deps/stwo-zig/src/core/vcs_lifted/channel_profile.zig",
    "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig",
    "deps/stwo-zig/src/core/vcs/blake2_hash.zig",
    "deps/stwo-zig/src/core/fields/m31.zig",
    "src/frontends/s31/runtime/native_verifier.zig",
    "src/frontends/s31/runtime/pcs_lifted_capture_admission.zig",
)


def source_texts(root: Path) -> dict[str, str]:
    return {name: (root / name).read_text() for name in FILES}


def check_sources(sources: dict[str, str]) -> None:
    profile, merkle, blake, m31, native, admission = (sources[name] for name in FILES)
    for label, source, anchor in (
        ("channel profile", profile,
         "pub const MerkleHasher = blake2_merkle.Blake2sPlainMerkleHasher;"),
        ("S31 verifier", native,
         "const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;"),
        ("plain factory", merkle,
         "return Blake2sMerkleHasherProtocolGeneric(is_m31_output, .plain);"),
    ):
        if source.count(anchor) != 1:
            raise ValueError(f"Merkle byte profile changed: {label}")

    leaf_init = region(merkle, "pub fn defaultWithInitialStateWithMode(",
                       "pub fn hashChildren(children:")
    ordered_once(leaf_init, "plain leaf domain", 
                 "var hasher = Self.initWithMode(mode);",
                 "if (comptime hash_protocol == .domain_prefixed) hasher.inner.update(LEAF_PREFIX[0..]);",
                 "return hasher;")
    leaf = region(merkle, "pub fn updateLeaf(self:", "pub fn finalize(self:")
    ordered_once(leaf, "canonical leaf bytes",
                 "if (column_values.len == 0) return;",
                 "if (builtin.cpu.arch.endian() == .little)",
                 "self.inner.update(std.mem.sliceAsBytes(column_values));",
                 "const value_bytes = column_values[at + i].toBytesLe();",
                 "self.inner.update(bytes[0 .. chunk * 4]);",
                 "pub fn updateLeafPackedBytes(",
                 "self.inner.update(packed_bytes);")
    children = region(merkle, "pub fn hashChildrenWithMode(",
                      "pub fn domainPrefixBytes(")
    if children.count("return InnerHasher.concatAndHashWithMode(mode, children.left, children.right);") != 1:
        raise ValueError("plain parent hash call changed")
    concat = region(blake, "pub fn concatAndHashWithMode(", "};\n}")
    ordered_once(concat, "ordered parent message",
                 "var payload: [64]u8 = undefined;",
                 "@memcpy(payload[0..32], v1[0..]);",
                 "@memcpy(payload[32..64], v2[0..]);",
                 "return hashFixed64WithMode(mode, &payload);")
    field = region(m31, "pub fn toBytesLe(self:", "pub fn fromBytesLe(")
    ordered_once(field, "canonical M31 LE word",
                 "const x = self.v;",
                 "@intCast(x & 0xff),",
                 "@intCast((x >> 8) & 0xff),",
                 "@intCast((x >> 16) & 0xff),",
                 "@intCast((x >> 24) & 0xff),")
    if m31.count("std.debug.assert(x < Modulus);") != 1:
        raise ValueError("canonical M31 constructor changed")
    ordered_once(admission, "S31 post-success Merkle replay",
                 "row[row_index] = value;",
                 "var hasher = H.defaultWithInitialState();",
                 "hasher.updateLeaf(row);",
                 "H.hashChildren(.{ .left = hash, .right = sibling })",
                 "H.hashChildren(.{ .left = sibling, .right = hash });",
                 "if (current != 0 or !std.mem.eql(u8, &hash, &root))")


def check(root: Path) -> None:
    check_sources(source_texts(root))
