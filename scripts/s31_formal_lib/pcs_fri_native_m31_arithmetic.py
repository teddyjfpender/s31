"""Fail-closed source pin for the M31 arithmetic modeled in Lean.

The Lean proof is about explicit natural-number operations. These body hashes
make changes to their reviewed Zig counterparts invalidate the formal receipt.
The pin is not a machine-checked parser or a proof of Zig/AArch64 semantics.
"""

from __future__ import annotations

import hashlib
from pathlib import Path


SIGNATURES = {
    "canonical constructor": "pub inline fn fromCanonical(x: u32) M31 {",
    "unchecked constructor": "pub inline fn fromU32Unchecked(x: u32) M31 {",
    "u64 constructor": "pub inline fn fromU64(x: u64) M31 {",
    "scalar add": "pub inline fn add(a: M31, b: M31) M31 {",
    "scalar sub": "pub inline fn sub(a: M31, b: M31) M31 {",
    "scalar mul": "pub inline fn mul(a: M31, b: M31) M31 {",
    "u64 reduction": "inline fn reduce64(x: u64) u32 {",
    "product reduction": "inline fn reduceProduct(x: u64) u32 {",
    "AArch64 vector mul": "inline fn mulVec4Aarch64(a: Vec4u32, b: Vec4u32) Vec4u32 {",
    "vector add": "pub inline fn addVec4(a: Vec4u32, b: Vec4u32) Vec4u32 {",
    "vector sub": "pub inline fn subVec4(a: Vec4u32, b: Vec4u32) Vec4u32 {",
    "vector mul dispatch": "pub inline fn mulVec4(a: Vec4u32, b: Vec4u32) Vec4u32 {",
    "vector product reduction": "inline fn reduceProductVec4(x: Vec4u64) Vec4u32 {",
}

# SHA-256 of the exact text between each Zig function's outer braces.
# A reviewer must update this table only after checking that the Lean model
# and the hardware premises still describe the edited implementation.
BODY_SHA256 = {
    "canonical constructor": "013f241c6ceebf2e89619572276975e97b0ccd63bdef033caaa35f63fd83694d",
    "unchecked constructor": "d7283066cd9417549128d970307cd6afd80d9493e3ecb9cab3dc6d144bef0303",
    "u64 constructor": "879571fb2f0431699ff43e0b67284978a23305b59c3cf371210a8f4714f50d3e",
    "scalar add": "d8b78fcd4899046a00f024b1368c349f83bc93653c0126062e024cc72f57eb14",
    "scalar sub": "31384816ca11844ca4cd82eda902f346cfcad9d5b3e402048a4a53f52864b352",
    "scalar mul": "2893d05b9165dbdb5e50ea47564c05535e129c69dd76ace29eda95917f08d707",
    "u64 reduction": "9624e3ece51054f528e18d72d8dd4cfa129c5f9c987d7d601d7e1cda33ccee71",
    "product reduction": "168b7880fc1122c91c730db7fea8cd19ea09ff7af73a85ecd5c6bb2b202a3ecb",
    "AArch64 vector mul": "3278fbc4e250fdba73427c037bc2513cc8be23a01301cc5f4f0674949f6be566",
    "vector add": "0df734e9c4a2d7df79e6d585198c1707f85649ae57fa109560725f6458893b3d",
    "vector sub": "babe5be84f4e336796faf5371e7db6e360cdf117bb07fae780f6f4181ada7bd7",
    "vector mul dispatch": "f185aa7157c309c8747fdcc25673cd98d7e97f015b7edf12e17c5ef9c456628f",
    "vector product reduction": "4ffcbe683ed3e9ab106f5a8c444e984cb0ff38e6ff5bb6b4d19a99b6524d5d3f",
}

DECLARATIONS = (
    "pub const Modulus: u32 = 0x7fffffff;",
    "pub const VEC_WIDTH: usize = 4;",
    "pub const Vec4u32 = @Vector(VEC_WIDTH, u32);",
    "const P_VEC: Vec4u32 = @splat(Modulus);",
)


def body(source: str, signature: str) -> str:
    if source.count(signature) != 1:
        raise ValueError(f"M31 source signature changed: {signature}")
    start = source.index(signature) + len(signature)
    depth = 1
    for end in range(start, len(source)):
        if source[end] == "{":
            depth += 1
        elif source[end] == "}":
            depth -= 1
            if depth == 0:
                return source[start:end]
    raise ValueError(f"M31 function has unbalanced braces: {signature}")


def check_source(source: str) -> None:
    for declaration in DECLARATIONS:
        if source.count(declaration) != 1:
            raise ValueError(f"M31 source declaration changed: {declaration}")
    if set(SIGNATURES) != set(BODY_SHA256):
        raise ValueError("M31 source pin table is incomplete")
    for name, signature in SIGNATURES.items():
        actual = hashlib.sha256(body(source, signature).encode()).hexdigest()
        if actual != BODY_SHA256[name]:
            raise ValueError(f"M31 source changed: {name}")


def check_pcs_fri_native_m31_arithmetic(root: Path) -> None:
    source = root / "deps/stwo-zig/src/core/fields/m31.zig"
    check_source(source.read_text())
