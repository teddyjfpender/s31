#!/usr/bin/env python3
"""Source-bound OOD seed geometry diagnostic for the pinned native engine.

This classifies a reviewed source snapshot and exact finite-field seed counts.
It is not a distribution proof for the Fiat–Shamir channel or a PCS theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENGINE_GITLINK = "59e1f115250b8af01712b9bf3d71616e53094964"
Q = 2**31 - 1
SOURCE_SHA256 = {
    "deps/stwo-zig/src/core/circle.zig":
        "71176ae60dc3bb2b799d0463c50b27f65ed908fd05e4405cdcda44f2e3aac5cf",
    "deps/stwo-zig/src/core/verifier.zig":
        "85e70cea004f82060d94363b3552e0f2d9cd4203cee69fff0fb47b5345056381",
    "deps/stwo-zig/src/prover/prove.zig":
        "b53626bfa0c8ea38ca20dbe1698e90d4919a683e6d776c40cb79011f1ea7bdfc",
    "deps/stwo-zig/src/core/pcs/quotients/row_evaluation.zig":
        "30e9e8768b083ca3d218b9d4903d7e3805b4219971e7d92847303d9de5778442",
    "deps/stwo-zig/src/core/fields/cm31.zig":
        "4b7a14c91fba7c467f92e924ce90c7230a22d08329591e3d5b8874d862b31288",
    "deps/stwo-zig/src/core/fields/qm31.zig":
        "a60c2a5a6f10bf91b1bfab41a526e41b589d0d1d83275e0516cf68b7228be931",
    "deps/stwo-zig/src/core/fields/m31.zig":
        "a5d47cc1a8c57a858b943c25e63eb1561b9f994fdff36ea38517bc166ea66d73",
    "deps/stwo-zig/src/core/channel/blake2s.zig":
        "fe0598dd15f70cc84b7098684b6a6f2e0ec319c4f7b5390c3ccd5f781ca32fc1",
    "deps/stwo-zig/src/core/vcs/blake2_hash.zig":
        "5600b1d1af9730403bb759b0dd4d7463efa5772cc2d95c567bd26c9d5315b1f0",
}


def ratio(numerator: int, denominator: int) -> str:
    value = Fraction(numerator, denominator)
    return f"{value.numerator}/{value.denominator}"


def classify(sources: dict[str, bytes], gitlink: str) -> dict[str, object]:
    if gitlink != ENGINE_GITLINK:
        raise ValueError("native engine gitlink changed; OOD geometry needs review")
    if set(sources) != set(SOURCE_SHA256):
        raise ValueError("native OOD source roster changed")
    observed = {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()}
    if observed != SOURCE_SHA256:
        changed = sorted(name for name in sources if observed[name] != SOURCE_SHA256[name])
        raise ValueError("native OOD source changed; review required: " + ", ".join(changed))

    circle = sources["deps/stwo-zig/src/core/circle.zig"].decode()
    verifier = sources["deps/stwo-zig/src/core/verifier.zig"].decode()
    prover = sources["deps/stwo-zig/src/prover/prove.zig"].decode()
    quotient = sources["deps/stwo-zig/src/core/pcs/quotients/row_evaluation.zig"].decode()
    cm31 = sources["deps/stwo-zig/src/core/fields/cm31.zig"].decode()
    qm31 = sources["deps/stwo-zig/src/core/fields/qm31.zig"].decode()
    m31 = sources["deps/stwo-zig/src/core/fields/m31.zig"].decode()
    channel = sources["deps/stwo-zig/src/core/channel/blake2s.zig"].decode()
    blake2_hash = sources["deps/stwo-zig/src/core/vcs/blake2_hash.zig"].decode()
    required = (
        (circle, "pub fn secureFieldPointFromRandomSeedChecked(t: QM31)"),
        (circle, "const one_plus_t_square_inv = try t_square.add(QM31.one()).inv();"),
        (circle, "const x = QM31.one().sub(t_square).mul(one_plus_t_square_inv);"),
        (circle, "const y = t.add(t).mul(one_plus_t_square_inv);"),
        (verifier, "const oods_seed = channel.drawSecureFelt();"),
        (verifier, "const oods_point = try pointFromOodsSeed(oods_seed);"),
        (verifier, "return circle.secureFieldPointFromRandomSeedChecked(seed) catch"),
        (prover, "const oods_point = try pointFromOodsSeed(channel.drawSecureFelt());"),
        (prover, "return circle.secureFieldPointFromRandomSeedChecked(seed) catch"),
        (quotient, "const pix = sample_point.x.c1;"),
        (quotient, "const piy = sample_point.y.c1;"),
        (quotient, "denominators[i] = prx.sub(domain_x).mul(piy).sub(pry.sub(domain_y).mul(pix));"),
        (cm31, "a + bi"),
        (qm31, "u^2 = 2 + i"),
        (qm31, "pub const R: CM31 = CM31.fromU32Unchecked(2, 1);"),
        (m31, "pub inline fn fromU64(x: u64) M31"),
        (m31, "return .{ .v = reduce64(x) };"),
        (channel, "pub fn drawSecureFelt(self: *Self) QM31"),
        (channel, "pub const Blake2sM31Channel = Blake2sChannelGeneric(true);"),
        (channel, "const Hasher = blake2_hash.Blake2sHasherGeneric(is_m31_output);"),
        (channel, "const hash = hashBytes(hash_input[0..]);"),
        (channel, "const words = self.drawU32s();"),
        (channel, "return hasher.finalize();"),
        (channel, "const felts = self.drawBaseFelts();"),
        (channel, "return QM31.fromM31Array(.{ felts[0], felts[1], felts[2], felts[3] });"),
        (channel, "self.n_draws = nextDrawCounter(self.n_draws)"),
        (channel, "const two_p = 2 * m31.Modulus;"),
        (channel, "if (x >= two_p)"),
        (channel, "felts[i] = M31.fromU64(x);"),
        (blake2_hash, "pub fn Blake2sHasherGeneric(comptime is_m31_output: bool) type"),
        (blake2_hash, "var out = self.ctx.finalize();"),
        (blake2_hash, "if (is_m31_output) out = reduceToM31(out);"),
        (blake2_hash, "pub fn reduceToM31(value: Blake2sHash) Blake2sHash"),
    )
    for source, marker in required:
        if marker not in source:
            raise ValueError("reviewed OOD control flow changed: " + marker)

    # R=2+i is a nonsquare in CM31: its norm to M31 is 5, and 5 is a
    # nonsquare modulo q (q mod 5 = 2). Thus a²-R*b²=1 has q²+1 solutions
    # over CM31, two with b=0. For regular t=a+b*u, the u coefficient of
    # y=2t/(1+t²) vanishes iff b=0 or a²-R*b²=1. The sets overlap at the
    # two b=0 norm-one points; the two t²=-1 exceptional roots are in CM31.
    # Hence 2*q²-3 regular seeds have y.c1=0. This is an algebraic seed-set
    # count, not a native rejection or security probability.
    if Q % 4 != 3 or Q % 5 != 2 or pow(5, (Q - 1) // 2, Q) != Q - 1:
        raise ValueError("reviewed QM31 quadratic-tower assumptions changed")
    # The selected M31 hasher reduces each raw 32-bit word before drawU32s
    # exposes it to drawBaseFelts. Hence the later x >= 2q filter accepts every
    # block. Under ideal independent uniform raw digest words, residues 0 and 1
    # have three preimages; all other residues have two. This is a fixed-input
    # ideal-word calculation, not a native BCS/random-oracle security proof.
    if 2 * Q != 2**32 - 2:
        raise ValueError("reviewed M31 channel acceptance geometry changed")
    # The rational parametrization has two exceptional roots of t²+1 in
    # CM31 and none in M31 (q ≡ 3 mod 4). For every other CM31 seed both
    # output coordinates have zero c1, so the reviewed denominator is zero
    # at every M31 domain row. These counts assume an ideal uniform QM31
    # seed; the native channel's distribution is not proved here.
    return {
        "schema": "s31-pcs-fri-ood-seed-geometry-v4",
        "status": "reviewed_source_and_conditional_field_count_only",
        "engine_gitlink_commit": gitlink,
        "source_sha256": observed,
        "field_cardinality": Q**4,
        "exceptional_seed_count": 2,
        "exceptional_seed_fraction_if_uniform": ratio(2, Q**4),
        "base_field_seed_count": Q,
        "base_field_seed_fraction_if_uniform": ratio(Q, Q**4),
        "quadratic_subfield_nonexceptional_seed_count": Q**2 - 2,
        "quadratic_subfield_nonexceptional_fraction_if_uniform": ratio(Q**2 - 2, Q**4),
        "y_c1_zero_regular_seed_count": 2 * Q**2 - 3,
        "y_c1_zero_regular_fraction_if_uniform": ratio(2 * Q**2 - 3, Q**4),
        "ideal_raw_u32_preimages_for_residues_zero_one": 3,
        "ideal_raw_u32_preimages_for_other_residues": 2,
        "ideal_raw_m31_coordinate_tv_from_uniform": ratio(Q - 2, Q * (Q + 1)),
        "ideal_independent_raw_words_qm31_max_point_mass": ratio(3**4, 2**128),
        "ideal_independent_raw_words_qm31_max_density_ratio_to_uniform": ratio(3**4 * Q**4, 2**128),
        "selected_post_reduction_eight_word_block_acceptance_fraction": "1/1",
        "rom_uniform_qm31_seed_conditional_on_success": False,
        "native_blake2s_rom_and_adaptive_bcs_reduction_proven": False,
        "reviewed_point_wrapper_explicitly_excludes_quadratic_subfield": False,
        "reviewed_row_quotient_denominator_zero_for_quadratic_subfield_point": True,
        "published_ood_distribution_instantiated": False,
        "native_proven_security_bits": None,
        "remaining_discharge": [
            "bound the biased native Fiat–Shamir seed distribution and exact point image",
            "model exceptional, subfield, and other y.c1-zero seeds in the complete prover/verifier schedule",
            "establish the paper's OOD sampling premise or prove a bound for the actual accepted-seed distribution",
            "connect every native quotient denominator to that sampled point and its committed oracle",
        ],
    }


def audit(root: Path = ROOT) -> dict[str, object]:
    gitlink = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True
    ).strip()
    sources = {name: (root / name).read_bytes() for name in SOURCE_SHA256}
    return classify(sources, gitlink)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = audit()
    except (OSError, subprocess.CalledProcessError, UnicodeDecodeError, ValueError) as exc:
        print(f"OOD source audit rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
