"""Pin raw PCS/FRI replay on the three v0.1 SHA package verifier paths.

This is a source-order regression gate, not Zig semantics or a cryptographic
soundness proof. Any new SHA release verifier needs an explicit roster review.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once


RELEASE_PATHS = (
    ("sha_joint_native_verifier.zig", "pcs", "sha_package_runtime.zig",
     "s31.sha_joint_native_verifier", "native.verify(allocator, topo.key.admission(&claimed),"),
    ("sha_shift_circuit_native_verifier.zig", "key.pcs",
     "sha_shift_package_runtime.zig", "s31.sha_shift_circuit_native_verifier",
     "native.verifyBytes(allocator, .{ .key = topo.key, .public_outputs = &claimed },"),
    ("sha_fused_circuit_native_verifier.zig", "key.pcs",
     "sha_fused_package_runtime.zig", "s31.sha_fused_circuit_native_verifier",
     "native.verifyBytes(allocator, .{ .key = topo.key, .public_outputs = &claimed },"),
)


def check_sources(helper: str, verifiers: dict[str, str],
                  packages: dict[str, str]) -> None:
    ordered_once(
        helper, "SHA release raw PCS/FRI replay",
        "try deep.validate(allocator, pcs.trace_lifting_log_size,",
        "capture.queries.raw, capture.column_log_sizes, capture.sampled_points,",
        "capture.sampled_values, capture.queried_values, capture.deep_answers,",
        "capture.deep_randomness);",
        "try fri.validate(H, allocator, pcs.fri_config.folding(),",
        "capture.queries.raw, capture.deep_answers, capture.fri,",
        "capture.last_layer_coefficients);",
        "try fri_merkle.validate(allocator, capture.queries.raw, capture.fri);",
    )
    if helper.count("pub fn validate(") != 1:
        raise ValueError("SHA capture admission entry point changed")
    for verifier_name, pcs_name, package_name, native_name, package_call in RELEASE_PATHS:
        native = verifiers[verifier_name]
        package = packages[package_name]
        if f"const native = {native_name};" not in package:
            raise ValueError(f"release SHA package verifier changed: {package_name}")
        if package.count(package_call) != 2:
            raise ValueError(f"release SHA package native dispatch changed: {package_name}")
        call = f"try pcs_capture_admission.validate(H, allocator, {pcs_name}, capture);"
        if native.count(call) != 1:
            raise ValueError(f"SHA capture admission call count changed: {verifier_name}")
        if native.count("pub fn verify") != 1:
            raise ValueError(f"SHA release verify entry changed: {verifier_name}")
        verify = native[native.index("pub fn verify"):]
        ordered_once(
            verify, f"SHA release verifier {verifier_name}",
            "try core.verifier.verifyBorrowedExWithProofCapture(",
            "defer capture.deinit(allocator);",
            call,
        )


def check_sha_release_capture(root: Path) -> None:
    verifier_dir = root / "src/frontends/s31/sha/verification"
    package_dir = root / "src/frontends/s31/sha/package"
    check_sources(
        (verifier_dir / "pcs_capture_admission.zig").read_text(),
        {name: (verifier_dir / name).read_text()
         for name, _, _, _, _ in RELEASE_PATHS},
        {name: (package_dir / name).read_text()
         for _, _, name, _, _ in RELEASE_PATHS},
    )
