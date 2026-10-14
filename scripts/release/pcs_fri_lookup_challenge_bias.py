#!/usr/bin/env python3
"""Exact conditional P07 likelihood-ratio diagnostic for one lookup pair.

This is finite counting under eight independent uniform raw 32-bit words for
one fixed transcript draw input. It is not a random-oracle/BCS theorem and
does not assign whole-prover security bits.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENGINE_GITLINK = "59e1f115250b8af01712b9bf3d71616e53094964"
SOURCE_SHA256 = {
    "deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig":
        "3c5b2b6c3996a5a1886f4fc57d92082f7eb91578df0b63f9f585fd45acc2899c",
    "deps/stwo-zig/src/core/channel/blake2s.zig":
        "fe0598dd15f70cc84b7098684b6a6f2e0ec319c4f7b5390c3ccd5f781ca32fc1",
    "deps/stwo-zig/src/core/channel/lookup_transcript.zig":
        "3180e2d704a07547a1df3a4c2da3b2dc675b7e18fb8715e39d889f8ddc9bc991",
    "deps/stwo-zig/src/core/vcs/blake2_hash.zig":
        "5600b1d1af9730403bb759b0dd4d7463efa5772cc2d95c567bd26c9d5315b1f0",
    "deps/stwo-zig/src/core/fields/m31.zig":
        "a5d47cc1a8c57a858b943c25e63eb1561b9f994fdff36ea38517bc166ea66d73",
    "src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig":
        "9c9547a7265e18a6330b3342b6e5763d7b68fbe341dd4f6c8968921e21b02bc6",
}
P = 2**31 - 1
WORD_SPACE = 2**32
MAX_LOOKUP_NUMERATOR = 5055289


def ratio(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def classify(sources: dict[str, bytes], engine_gitlink: str) -> dict[str, object]:
    if engine_gitlink != ENGINE_GITLINK:
        raise ValueError("selected native engine gitlink changed")
    if set(sources) != set(SOURCE_SHA256):
        raise ValueError("selected challenge source roster changed")
    digests = {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()}
    if digests != SOURCE_SHA256:
        changed = sorted(name for name in sources if digests[name] != SOURCE_SHA256[name])
        raise ValueError("reviewed lookup draw or budget source changed: " + ", ".join(changed))

    # These anchors document the source-flow interpretation of the pinned
    # hashes. The hashes force renewed review even for source edits that retain
    # these strings; neither check proves compiled Zig semantics.
    channel = sources["deps/stwo-zig/src/core/channel/blake2s.zig"].decode()
    mixed = sources["deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig"].decode()
    lookup = sources["deps/stwo-zig/src/core/channel/lookup_transcript.zig"].decode()
    hasher = sources["deps/stwo-zig/src/core/vcs/blake2_hash.zig"].decode()
    m31 = sources["deps/stwo-zig/src/core/fields/m31.zig"].decode()
    budget = sources["src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig"].decode()
    required = (
        (mixed, "const MC = old.profiles.Blake2sM31MerkleChannel;"),
        (mixed, "core.channel.lookup_transcript.drawLookupElements(allocator, &channel);"),
        (channel, "pub const Blake2sM31Channel = Blake2sChannelGeneric(true);"),
        (channel, "out[produced] = QM31.fromM31Array(.{"),
        (channel, "const words = self.drawU32s();"),
        (channel, "if (x >= two_p)"),
        (lookup, "const values = try channel.drawSecureFelts(allocator, 2);"),
        (lookup, "return .{ .z = values[0], .alpha = values[1] };"),
        (hasher, "if (is_m31_output) out = reduceToM31(out);"),
        (hasher, "pub fn reduceToM31(value: Blake2sHash) Blake2sHash"),
        (m31, "pub const Modulus: u32 = 0x7fffffff;"),
        (budget, "const numerator = try std.math.sub(u64, try std.math.mul(u64, 7, occurrences), 6);"),
        (budget, "try std.testing.expectEqual(@as(u64, 5055289), eight.conditional_lookup_numerator);"),
    )
    for source, marker in required:
        if marker not in source:
            raise ValueError("reviewed lookup challenge flow changed: " + marker)

    if WORD_SPACE != 2 * P + 2:
        raise ValueError("M31 raw-word fiber arithmetic changed")
    max_density_ratio = Fraction((3 * P) ** 8, WORD_SPACE ** 8)
    uniform_lookup = Fraction(MAX_LOOKUP_NUMERATOR, P**4)
    biased_lookup = max_density_ratio * uniform_lookup
    return {
        "schema": "s31-pcs-fri-lookup-pair-bias-v1",
        "status": "conditional_fixed_prefix_counting_only",
        "engine_gitlink": engine_gitlink,
        "source_sha256": digests,
        "raw_words_per_lookup_pair": 8,
        "raw_word_space": WORD_SPACE,
        "m31_modulus": P,
        "preimages_for_residues_0_and_1": 3,
        "preimages_for_other_residues": 2,
        "max_density_ratio_over_uniform_QM31_squared": ratio(max_density_ratio),
        "max_density_ratio_approx": float(max_density_ratio),
        "mixed_n1_n8_conditional_uniform_lookup_bound": ratio(uniform_lookup),
        "mixed_n1_n8_conditional_biased_lookup_bound": ratio(biased_lookup),
        "mixed_n1_n8_conditional_biased_lookup_bits_approx": -math.log2(float(biased_lookup)),
        "repeated_valid_continuations": "min(1, Q_L * conditional_biased_lookup_bound)",
        "premises": [
            "one fixed pre-challenge tuple multiset and a fixed transcript draw input",
            "eight raw BLAKE2s output words ideal independent uniform u32",
            "the existing fixed-roster lookup polynomial and AIR premises",
        ],
        "unproved_joins": [
            "raw-word independence after adaptive BCS transcript and valid-nonce selection",
            "bound on all attacker-tested valid transcript continuations Q_L",
            "accepted-proof to committed fixed-roster lookup reduction",
            "whole-prover PCS/FRI/Merkle/Fiat-Shamir error budget",
        ],
        "p07_discharged": False,
        "p09_discharged": False,
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
    }


def audit(root: Path = ROOT) -> dict[str, object]:
    root = root.resolve()
    gitlink = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True).strip()
    checked = subprocess.check_output(
        ["git", "-C", str(root / "deps/stwo-zig"), "rev-parse", "HEAD"], text=True).strip()
    if gitlink != checked:
        raise ValueError("native engine differs from selected gitlink")
    return classify({name: (root / name).read_bytes() for name in SOURCE_SHA256}, gitlink)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print exact-rational JSON")
    args = parser.parse_args()
    try:
        result = audit()
    except (OSError, subprocess.CalledProcessError, ValueError) as exc:
        parser.exit(2, f"lookup challenge bias audit refused: {exc}\n")
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(result["mixed_n1_n8_conditional_biased_lookup_bound"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
