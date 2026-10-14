#!/usr/bin/env python3
"""Audit one sealed control program's public statement against native pins.

The native verifier is run on the supplied proof and public-only statement.
The remaining inference from accepted lookup sums to committed Gate cells is
an explicit soundness premise of the Lean join, not asserted by this script.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import abi  # noqa: E402
from package.control_air_correspondence import check_control_air  # noqa: E402
from package.verify import verify_package  # noqa: E402

P = 2**31 - 1
SCHEMA = "s31-control-public-statement-pins-v1"
ABI = {
    "schema": "s31-public-abi-v1",
    "encoding": "eight little-endian u32 words; unused words are zero",
    "public_inputs": [{"name": "x", "kind": "m31", "length": 1}],
    "public_outputs": [{"name": "result", "kind": "m31", "length": 4}],
}
SOURCE_ROUTE = {
    "src/frontends/s31/language/relation.zig": (
        "if (assignment.public_inputs.object.count() != expected_public_inputs or",
        "var out = [_]u32{0} ** 8;",
        "for (program.inputs) |input| {",
        "if (input.visibility != .public) continue;",
        "const values = try arrayValues(allocator, assignment.public_inputs, input.name,",
        "for (program.public_outputs) |name| {",
        "const values = try arrayValues(allocator, assignment.public_outputs, name, shape);",
    ),
    "src/frontends/s31/runtime/mvp_runtime.zig": (
        "if (!std.mem.eql(u8, external_key, embedded_key)) return error.InvalidVerificationKey;",
        "if (statement.value.private_inputs != null) return error.InvalidPublicStatement;",
        "break :blk try relation.claimedWords(allocator, parsed.value, statement.value);",
        "const public_words = admitted.public_words;",
        "try native.verify(allocator, &layout, &bundle, try showcasePcsConfig(key.trace_log_size), root, hash, public_words, encoded);",
    ),
    "src/frontends/s31/runtime/native_verifier.zig": (
        "for (public_words, &outputs) |word, *output|",
        "output.* = QM31.fromU32Unchecked(word & 0xffff, word >> 16, 0, 0);",
        "channel.mixFelts(&outputs);",
        "circuit.witness.trace.lookupSum(&outputs, PerComponent(QM31).fromArray(sums), lookup.z, lookup.alpha)",
    ),
    "deps/stwo-zig/src/frontends/circuit/witness/trace.zig": (
        "for (output_values, 0..) |output, index|",
        "outputTerm(&elements, U_VAR_IDX + 1 + index, output)",
        "return sum.add(try outputTerm(&elements, U_VAR_IDX, U_VALUE));",
    ),
}
ROUTE_SCOPE = {
    "src/frontends/s31/language/relation.zig":
        ("pub fn claimedWords(", "pub fn evaluate("),
    "src/frontends/s31/runtime/mvp_runtime.zig":
        ("fn verify(allocator:", "fn validateKey("),
    "src/frontends/s31/runtime/native_verifier.zig":
        ("fn verifyProfile(", "pub fn verifySparse("),
    "deps/stwo-zig/src/frontends/circuit/witness/trace.zig":
        ("pub fn lookupSum(", "/// `circuits::context::U_VALUE`."),
}


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("control public statement audit: " + reason)


def source_route_guard(root: Path = ROOT, sources: dict[str, str] | None = None) -> dict[str, str]:
    """Pin the native statement-to-output-lookup call path, not its soundness."""
    digests = {}
    for path, markers in SOURCE_ROUTE.items():
        source = (root / path).read_text() if sources is None else sources[path]
        digests[path] = hashlib.sha256(source.encode()).hexdigest()
        start, end = ROUTE_SCOPE[path]
        require(source.count(start) == 1 and source.count(end) == 1,
                f"native statement route scope changed: {path}")
        source = source.split(start, 1)[1].split(end, 1)[0]
        for marker in markers:
            require(source.count(marker) == 1,
                    f"native statement route changed: {path}: {marker}")
    return digests


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for name, value in pairs:
        require(name not in result, f"duplicate statement key {name}")
        result[name] = value
    return result


def public_words(statement_bytes: bytes, public_abi: dict[str, object]) -> list[int]:
    require(public_abi == ABI, "sealed ABI differs from the bounded control profile")
    require(len(statement_bytes) <= 1 << 20, "statement too large")
    try:
        statement = json.loads(statement_bytes, object_pairs_hook=_unique_object)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError("control public statement audit: invalid statement JSON") from exc
    require(type(statement) is dict and set(statement) == {"public_inputs", "public_outputs"},
            "statement must contain exactly public inputs and outputs")
    inputs = statement["public_inputs"]
    outputs = statement["public_outputs"]
    require(type(inputs) is dict and set(inputs) == {"x"} and
            type(outputs) is dict and set(outputs) == {"result"},
            "statement fields differ from sealed ABI")
    x = inputs["x"]
    result = outputs["result"]
    require(type(x) is list and len(x) == 1 and
            type(result) is list and len(result) == 4 and
            all(type(word) is int and 0 <= word < P for word in x + result),
            "statement contains a noncanonical M31 word or wrong array length")
    return [*x, *result, 0, 0, 0]


def audit(package: Path, proof: Path, statement: Path, lean_checker: Path) -> dict[str, object]:
    package = package.resolve()
    proof = proof.resolve()
    statement = statement.resolve()
    verify_package(package)
    route_digests = source_route_guard()
    manifest = json.loads((package / "manifest.json").read_text())
    source = json.loads((package / "source.s31.json").read_text())
    displayed_abi = json.loads((package / "public-abi.json").read_text())
    require(displayed_abi == abi(source, manifest["lowering"]),
            "displayed public ABI differs from the sealed source")
    require(lean_checker.is_file(), "build the Lean exact-source byte checker")
    exact = subprocess.run((
        str(lean_checker), str(package / "source.s31"),
        str(package / "pure-field-derivation.json"), str(package / "source.s31.json"),
    ), capture_output=True, text=True, check=False, timeout=30)
    require(exact.returncode == 0 and "accepted: exact source" in exact.stdout,
            "Lean exact-source derivation rejected package")
    topology = check_control_air(package)
    pins = [3, *topology["public_output_pin_addresses"], 8, 9, 10]
    require(pins == list(range(3, 11)), "captured Gate pin order changed")
    words = public_words(statement.read_bytes(), displayed_abi)
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    accepted = subprocess.run((str(verifier), str(proof), str(statement),
                               str(package / "verification-key.json")),
                              capture_output=True, text=True, check=False, timeout=120)
    require(accepted.returncode == 0 and "native verification accepted" in
            accepted.stdout + accepted.stderr, "native verifier rejected proof or statement")
    return {
        "schema": SCHEMA,
        "program_sha256": topology["program_sha256"],
        "preprocessed_root": topology["preprocessed_root"],
        "public_abi_schema": displayed_abi["schema"],
        "public_abi_sha256": hashlib.sha256((package / "public-abi.json").read_bytes()).hexdigest(),
        "verification_key_sha256": hashlib.sha256(
            (package / "verification-key.json").read_bytes()).hexdigest(),
        "public_words": words,
        "public_pin_addresses": pins,
        "proof_sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
        "statement_sha256": hashlib.sha256(statement.read_bytes()).hexdigest(),
        "native_verifier_accepted": True,
        "lean_exact_source_derivation": True,
        "native_route_source_sha256": route_digests,
        "lookup_to_committed_pins_proved": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("--lean-checker", type=Path, default=(
        ROOT / "formal/s31/.lake/build/bin/s31-pure-field-derivation-bytes-check"))
    args = parser.parse_args()
    print(json.dumps(audit(args.package, args.proof, args.statement, args.lean_checker),
                     indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
