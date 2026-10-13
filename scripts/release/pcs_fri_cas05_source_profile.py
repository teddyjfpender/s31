#!/usr/bin/env python3
"""Source-pinned profile geometry for the experimental CAS05 paired PCS.

This checks an exact Git commit and reviewed source bytes. It does not verify
an installed binary, establish the published theorem's protocol premises, or
assign native security bits. Production S31 remains on its separate engine
gitlink and quotient-only PCS.
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
PRODUCTION_GITLINK = "59e1f115250b8af01712b9bf3d71616e53094964"
DRAFT_COMMIT = "234ac67b2819e6b102e8d43da93a38a4a902075e"
DRAFT_REF = "origin/codex/paired-degree-protocol-20261013"
Q = 2**31 - 1
SOURCE_SHA256 = {
    "src/core/fields/m31.zig": "a5d47cc1a8c57a858b943c25e63eb1561b9f994fdff36ea38517bc166ea66d73",
    "src/core/fields/cm31.zig": "4b7a14c91fba7c467f92e924ce90c7230a22d08329591e3d5b8874d862b31288",
    "src/core/fields/qm31.zig": "a60c2a5a6f10bf91b1bfab41a526e41b589d0d1d83275e0516cf68b7228be931",
    "src/core/constraints.zig": "4b8eb20e43d45ec28777f343a43e25566788c598b895d1f230b62da25e33dfea",
    "src/core/pcs/paired_sparse_cascade_experimental.zig": "6b0dba9fb57cdc4690d51326b338760c488c33519354d9ef758a751a201b5487",
    "src/core/pcs/paired_sparse_cascade_wire.zig": "22fecbb35c2a075a7f26786b0b44cfc3523c109ec31d3928a442cfc6c16b8542",
    "src/core/pcs/transposed_merkle_sparse.zig": "6fbb6bd496a9d2916cdaa141c0c44f05fc26ed45ba74e27fedb017b20ee661a9",
    "src/core/pcs/transposed_merkle_cascade.zig": "7bc0793234e902ae37080e2c8b90d4df87120fd3a87c441d669c928fcb85bb92",
    "src/core/pcs/transposed_paired_sparse.zig": "56bd8cf46b8897044b4dc9f70d4dd22c8bd10d01b584165daa21625f4e3dffca",
    "src/prover/pcs/paired_sparse_cascade_experimental.zig": "e76677cdf644a47561d8f02e7b65715cd38d57a4e1af10db7c729371fb82030f",
    "src/prover/pcs/transposed_cascade_experimental.zig": "b079122ef4c3203a0150fce52c0f29833d9f73fe56b357f530299861a8983316",
}


def _contains(source: str, markers: tuple[str, ...], label: str) -> None:
    for marker in markers:
        if marker not in source:
            raise ValueError(f"reviewed {label} shape changed: {marker}")


def verify_hashes(sources: dict[str, bytes], expected: dict[str, str]) -> dict[str, str]:
    if set(sources) != set(expected):
        raise ValueError("CAS05 source roster changed")
    observed = {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()}
    if observed != expected:
        changed = sorted(name for name in expected if observed[name] != expected[name])
        raise ValueError(f"CAS05 source changed; review required: {', '.join(changed)}")
    return observed


def classify_sources(sources: dict[str, bytes]) -> dict:
    """Classify only the exact draft source bytes reviewed at `DRAFT_COMMIT`."""
    observed = verify_hashes(sources, SOURCE_SHA256)
    decoded = {name: data.decode("utf-8") for name, data in sources.items()}
    _contains(decoded["src/core/pcs/transposed_merkle_sparse.zig"], (
        "pub const MAX_LOG_SIZE: u32 = 22;",
        "self.query_count == 0 or self.query_count > (1 << 14)",
        "self.height_count < 2 or self.height_count > tree.MAX_HEIGHTS",
        "if (fixed_bytes > MAX_WIRE_BYTES - 128)",
    ), "sparse verifier profile")
    _contains(decoded["src/core/pcs/transposed_merkle_cascade.zig"], (
        "pub const MAX_HEIGHTS: usize = 8;",
        "pub const MAX_COLUMNS: usize = 64;",
        "pub const MAX_LOG_SIZE: u32 = 16;",
        "pub const MAX_WIRE_BYTES: usize = 64 * 1024 * 1024;",
        "self.query_count * (@as(usize, 1) << @intCast(self.height_count)) > (1 << 16)",
    ), "legacy XDM03 source profile")
    _contains(decoded["src/core/pcs/paired_sparse_cascade_experimental.zig"], (
        "pub const OUTER_VERSION: u16 = 6;",
        "pub fn terminalLength(self: Profile) usize",
        "self.source.largest_log_size - @as(u32, @intCast(self.source.height_count)) - self.log_blowup",
        "var opened = try xdm.verifyAndCollect(",
        "var answers = try paired.fromVerifiedOpenings(",
        "try verifyFolds(allocator, proof, raw, answers.values, alphas);",
        "try requireCanonicalQM31(proof.sampled_point.x);",
        "for (claims) |claim| try requireCanonicalQM31(claim);",
        "for (column) |coordinate| try requireCanonicalM31(coordinate);",
        "const point = try circle.secureFieldPointFromRandomSeedChecked(staged.drawSecureFelt());",
        "if (point.y.c1.isZero()) return error.DegenerateOodPoint;",
        "channel.* = staged;",
    ), "CAS05 verifier")
    _contains(decoded["src/core/pcs/paired_sparse_cascade_wire.zig"], (
        'pub const MAGIC = "S31CAS05";',
        "pub const VERSION: u16 = cascade.OUTER_VERSION;",
        "pub fn verifyAgainstStatement(",
    ), "CAS05 versioned wire")
    _contains(decoded["src/core/pcs/transposed_paired_sparse.zig"], (
        "const p = domain.at(utils.bitReverseIndex(base + j, log_size));",
        "const denominator = point.x.c0.sub(CM31.fromBase(p.x)).mul(point.y.c1)",
        ".sub(point.y.c0.sub(CM31.fromBase(p.y)).mul(point.x.c1));",
        "const inverse = try denominator.inv();",
        "coefficient.* = try constraints.complexConjugateLineCoeffs(point, claim, QM31.one());",
        "pair[0] = power;",
        "power = power.mul(batch);",
        "pair[1] = power;",
        "const original = opened.at(height, query, j, col);",
        "const numerator = coefficient.c.mulM31(original)",
        ".sub(coefficient.a.mulM31(p.y)).sub(coefficient.b);",
        "const quotient = numerator.mulCM31(inverse);",
        "answer = answer.add(pair[0].mul(QM31.fromBase(original)))",
        ".add(pair[1].mul(quotient));",
        "values[height][query * 2 + j] = answer;",
    ), "authenticated original and own-quotient batch")
    _contains(decoded["src/core/fields/qm31.zig"], (
        "pub inline fn fromBase(x: M31) QM31 {",
        "return .{ .c0 = CM31.fromBase(x), .c1 = CM31.zero() };",
        "pub inline fn mulCM31(self: QM31, rhs: CM31) QM31 {",
        ".c0 = self.c0.mul(rhs),",
        ".c1 = self.c1.mul(rhs),",
        "pub inline fn mulM31(lhs: QM31, rhs: M31) QM31 {",
        "const product = m31_mod.mulVec4(lanes, @splat(rhs.v));",
        "return fromU32Unchecked(product[0], product[1], product[2], product[3]);",
    ), "CAS05 QM31 row arithmetic")
    _contains(decoded["src/core/fields/cm31.zig"], (
        "pub inline fn fromBase(x: M31) CM31 {",
        "return .{ .a = x, .b = M31.zero() };",
        "pub fn inv(self: CM31) Error!CM31 {",
        "if (self.isZero()) return Error.DivisionByZero;",
    ), "CAS05 CM31 embedding and checked inverse")
    _contains(decoded["src/core/constraints.zig"], (
        "pub fn complexConjugateLineCoeffs(",
        "if (point.y.eql(point.y.complexConjugate())) return error.DegenerateLine;",
        "const a = value.complexConjugate().sub(value);",
        "const c = point.complexConjugate().y.sub(point.y);",
        "const b = value.mul(c).sub(a.mul(point.y));",
    ), "CAS05 conjugate line")
    _contains(decoded["src/prover/pcs/paired_sparse_cascade_experimental.zig"], (
        "var source = try source_prover.Commitment.commitSparse(a, input.source_columns, input.n_queries);",
        "try old.validateSourceDegree(a, domains[i], columns, log_size - input.log_blowup);",
        "batches[i] = try old.pairedHeight(a, domains[i], columns, claims[i], point, challenges);",
        "return error.TerminalDegreeExceeded;",
    ), "CAS05 host prover")
    _contains(decoded["src/prover/pcs/transposed_cascade_experimental.zig"], (
        "const profile = xdm.Profile{",
        "pub const MAX_SPARSE_HOST_BYTES: usize = 192 * 1024 * 1024;",
        "pub fn estimatedSparseHostBytes(k: u32, source_words: usize) !usize {",
        "return commitImpl(allocator, source_columns, query_count, .sparse);",
        "try (sparse.Profile{",
        "if (try estimatedSparseHostBytes(k, source_words) > MAX_SPARSE_HOST_BYTES)",
        "if (self.mode != .dense) return error.UnsupportedProofFormat;",
    ), "bounded sparse CAS05 host commitment")
    return {"draft_commit": DRAFT_COMMIT, "source_sha256": observed,
            "source_classification": "versioned_experimental_original_plus_own_quotient_cascade"}


def profile_geometry(k: int, heights: int, beta: int, queries: int,
                     columns: tuple[int, ...], theta: Fraction) -> dict:
    """Exact native-cap and candidate paper-shape arithmetic, no theorem join."""
    if any(type(x) is not int for x in (k, heights, beta, queries, *columns)):
        raise ValueError("profile integers must be integers")
    if type(theta) is not Fraction:
        raise ValueError("theta must be an exact Fraction")
    if (len(columns) != heights or not 2 <= heights <= 8 or not 1 <= beta or
            not heights + 2 <= k <= 22 or not 1 <= queries <= 1 << 14 or
            any(not 1 <= count <= 64 for count in columns) or
            not Fraction(0) < theta < Fraction(1)):
        raise ValueError("profile outside reviewed CAS05 sparse shape")
    if k < heights + beta:
        raise ValueError("CAS05 terminal exponent would be negative")
    # XDM04's fixed query bytes are an admitted upper budget, not its final
    # witness length. The actual variable hash witness is checked at decode.
    sparse_fixed = queries * (4 + sum(8 * count for count in columns))
    sparse_admitted = sparse_fixed <= 64 * 1024 * 1024 - 128
    dense_fixed = queries * (4 + sum(
        (1 << (heights - i)) * count * 4 for i, count in enumerate(columns)))
    dense_admitted = (k <= 16 and queries * (1 << heights) <= 1 << 16 and
                      dense_fixed <= 64 * 1024 * 1024 - 128)
    # The experimental CAS05 host uses the XDM04 shape but still allocates
    # the full XDM03-format Merkle tree. Its source columns are borrowed;
    # this is the exact constructor preflight, not a whole-prover peak bound.
    tree_bytes = ((1 << (k + 1)) - 1) * 32
    source_bytes = sum((1 << (k - i)) * count * 4
                       for i, count in enumerate(columns))
    host_preflight_bytes = tree_bytes + source_bytes
    host_budget_bytes = 192 * 1024 * 1024
    cas05_host_admitted = sparse_admitted and host_preflight_bytes <= host_budget_bytes
    blowup = 1 << beta
    domains = [1 << (k - i) for i in range(heights)]
    code_dimensions = [rows // blowup for rows in domains]
    if any(size < 1 for size in code_dimensions):
        raise ValueError("empty source code dimension")
    # This is the *published single-point* Protocol-4 inequality. CAS05 uses
    # a conjugate two-point zeroifier, represented by a circle-algebra line.
    # Its exact circle-basis filtration and Eq. 80 uniqueness threshold need
    # a separate proof; passing these numbers never discharges P05.
    single_point_margins = [1 - theta - Fraction(1, blowup) *
                            (1 + Fraction(2, size)) for size in code_dimensions]
    single_point_condition = [margin > 0 for margin in single_point_margins]
    terminal_rows = 1 << (k - heights)
    terminal_words = 1 << (k - beta - heights)
    return {
        "profile": {"largest_log_size": k, "height_count": heights,
                    "log_blowup": beta, "queries": queries, "columns": columns,
                    "theta": str(theta)},
        "native_sparse_verifier_visible_caps_pass": sparse_admitted,
        "legacy_xdm03_dense_host_visible_caps_pass": dense_admitted,
        "native_cas05_bounded_sparse_host_visible_caps_pass": cas05_host_admitted,
        "sparse_fixed_source_wire_bytes_before_witness": sparse_fixed,
        "legacy_xdm03_dense_fixed_source_wire_bytes_before_witness": dense_fixed,
        "native_cas05_host_merkle_tree_bytes": tree_bytes,
        "native_cas05_host_logical_borrowed_source_bytes": source_bytes,
        "native_cas05_host_preflight_estimate_bytes": host_preflight_bytes,
        "native_cas05_host_preflight_budget_bytes": host_budget_bytes,
        "source_domain_rows_by_height": domains,
        "candidate_code_dimensions_by_height": code_dimensions,
        "published_single_point_small_table_margins_by_height":
            [str(value) for value in single_point_margins],
        "published_single_point_small_table_numeric_by_height": single_point_condition,
        "published_single_point_small_table_numeric_all_pass": all(single_point_condition),
        "cas05_two_point_uniqueness_threshold_derived": False,
        "derived_batch_oracle_substitution_proved": False,
        "candidate_theta_in_strict_unique_decoding_interval":
            theta < (1 - Fraction(1, blowup)) / 2,
        "candidate_N_if_D0_equals_N_times_B_squared":
            (1 << (k - 2 * beta)) if k >= 2 * beta else None,
        "terminal_domain_rows": terminal_rows,
        "terminal_qm31_coefficient_words": terminal_words,
        "paper_protocol3_indices_if_refined": {"n": k - beta, "r": heights - 1},
        "minimum_idealized_BCS_round_count": heights + 5,
        "native_BCS_round_count_R": None,
        "native_adversary_hash_query_budget_T": None,
        "full_single_fold_count": k - beta,
        "short_fold_count": heights,
        "native_profile_or_theorem_admitted": False,
        "qualification": ("Visible source caps, CAS05 host tree/source preflight, "
                          "and exact candidate geometry only; the preflight "
                          "omits FRI working arrays and proof buffers. "
                          "The source code dimensions are not an authenticated "
                          "S31 AIR table roster. The paper's single-point "
                          "small-table inequality is only a numeric comparator; "
                          "CAS05's two-point zeroifier and derived batch need "
                          "new uniqueness/oracle arguments. No native-to-paper, OOD, FRI, "
                          "Merkle, or BCS theorem is established."),
    }


def conditional_ood_support() -> dict:
    """Cardinality comparison only, not a native OOD bad-set reduction."""
    paper_single = Q**4 - Q - 2
    two_point = Q**4 - Q**2
    native_guard = (Q**2 - 1) ** 2
    if two_point - native_guard != Q**2 - 1:
        raise ValueError("two-point support arithmetic changed")
    return {
        "published_protocol4_single_point_support": paper_single,
        "section_4_5_two_point_candidate_support": two_point,
        "native_guarded_seed_image_if_uniform": native_guard,
        "two_point_minus_guarded": two_point - native_guard,
        "two_point_to_guarded_ratio": str(Fraction(two_point, native_guard)),
        "two_point_bad_set_bound_or_adaptive_sampler_proved": False,
        "qualification": ("Section 4.5 sketches, but does not prove, the "
                          "native conjugate two-point reduction. The single-point "
                          "Protocol-4 OOD denominator must not be substituted "
                          "for the two-point support or guarded seed image."),
    }


def audit(engine_repo: Path, k: int, heights: int, beta: int, queries: int,
          columns: tuple[int, ...], theta: Fraction, head_ref: str | None = None) -> dict:
    def git(*args: str) -> bytes:
        return subprocess.check_output(["git", "-C", str(engine_repo), *args])
    if git("cat-file", "-t", DRAFT_COMMIT).strip() != b"commit":
        raise ValueError("reviewed CAS05 commit unavailable")
    if head_ref is not None and git("rev-parse", head_ref).decode().strip() != DRAFT_COMMIT:
        raise ValueError("CAS05 draft ref advanced; source review required")
    sources = {name: git("show", f"{DRAFT_COMMIT}:{name}") for name in SOURCE_SHA256}
    source = classify_sources(sources)
    geometry = profile_geometry(k, heights, beta, queries, columns, theta)
    production = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD:deps/stwo-zig"], text=True
    ).strip()
    if production != PRODUCTION_GITLINK:
        raise ValueError("production engine gitlink changed; P05 source review required")
    return {
        "schema": "s31-cas05-p05-source-profile-v1",
        "status": "experimental_draft_geometry_only",
        "draft_source": source,
        "draft_ref_checked": head_ref,
        "production_engine_gitlink": production,
        "draft_is_production_engine": production == DRAFT_COMMIT,
        "installed_binary_correspondence_checked": False,
        "geometry": geometry,
        "conditional_ood_support_arithmetic": conditional_ood_support(),
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "remaining_p05": [
            "migrate a versioned original-plus-own-quotient PCS prover/verifier into production dispatch and pin the new engine",
            "prove all committed source and quotient words meet the published degree-corrected multi-domain relation",
            "derive the conjugate two-point line's circle-basis filtration and small-domain uniqueness threshold, then justify derived-batch oracle substitution",
            "instantiate the paper's exact table heights, query/round errors, guarded OOD and BCS/ROM hypotheses for an installed binary",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("engine_repo", type=Path, help="local stwo-zig Git repository containing the reviewed draft commit")
    parser.add_argument("--head-ref", default=DRAFT_REF, help="ref whose tip must equal the reviewed draft commit")
    parser.add_argument("--largest-log-size", type=int, required=True)
    parser.add_argument("--height-count", type=int, required=True)
    parser.add_argument("--log-blowup", type=int, required=True)
    parser.add_argument("--queries", type=int, required=True)
    parser.add_argument("--columns", required=True, help="comma-separated positive column counts, one per height")
    parser.add_argument("--theta", required=True, help="candidate paper proximity fraction, e.g. 16383/65536")
    parser.add_argument("--require-proven", action="store_true", help="fail closed until native theorem correspondence exists")
    args = parser.parse_args(argv)
    try:
        columns = tuple(int(word) for word in args.columns.split(","))
        report = audit(args.engine_repo, args.largest_log_size,
                       args.height_count, args.log_blowup, args.queries,
                       columns, Fraction(args.theta), args.head_ref)
    except (OSError, subprocess.CalledProcessError, UnicodeDecodeError,
            ValueError, ZeroDivisionError) as exc:
        print(f"CAS05 P05 source/profile audit rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
