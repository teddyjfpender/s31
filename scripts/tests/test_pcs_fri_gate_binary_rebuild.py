"""Gate verifier rebuild safety boundary and exact recipe controls."""

from __future__ import annotations

import json
import struct
import subprocess
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

from scripts.release.pcs_fri_gate_binary_rebuild import (
    BUILD_FILE, accepted_gate_geometry, build_command, rebuild_verifier,
    same_executable_image,
)


class GateVerifierRebuildTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.package = Path(self.temporary.name) / "package"
        self.package.mkdir()
        (self.package / "source.s31.json").write_text(
            json.dumps({"version": 1, "name": "guard"}))
        for name in ("verification-key.json", "recursive-verification-key.json",
                     "recursive-verification-key-level2.json",
                     "fixed-fold-verification-key.json"):
            (self.package / name).write_text("{}")
        self.manifest = {"schema": "s31-package-v1", "name": "guard",
                         "lowering": "gate", "fri_fold_step": 1,
                         "optimize": "ReleaseFast"}

    def test_macho_metadata_normalization_preserves_code(self) -> None:
        name = "s31-guard-native-verifier"

        def fixture(cache: bytes, uuid: bytes, timestamp: int,
                    code: bytes, signature: bytes) -> bytes:
            source = (b"src/frontends/s31/.zig-cache/o/" + cache +
                      b"/" + name.encode() + b"_zcu.o\x00")
            header = struct.pack("<IiiIIIII", 0xfeedfacf, 0x100000c, 0,
                                 2, 3, 64, 0, 0)
            commands = (struct.pack("<II", 0x1b, 24) + uuid +
                        struct.pack("<IIIIII", 0x2, 24, 128, 1, 144, len(source)) +
                        struct.pack("<IIII", 0x1d, 16, 144 + len(source), len(signature)))
            return (header + commands + code +
                    struct.pack("<IBBHQ", 0, 0x66, 0, 1, timestamp) +
                    source + signature)

        first = self.package / "first"
        second = self.package / "second"
        first.write_bytes(fixture(b"a" * 32, b"a" * 16, 1, b"A" * 32, b"sig-one!"))
        second.write_bytes(fixture(b"b" * 32, b"b" * 16, 2, b"A" * 32, b"sig-two!"))
        ok = subprocess.CompletedProcess([], 0, "", "")
        with patch("scripts.release.pcs_fri_gate_binary_rebuild.subprocess.run", return_value=ok):
            self.assertTrue(same_executable_image(first, second, name))
            second.write_bytes(fixture(b"b" * 32, b"b" * 16, 2, b"B" + b"A" * 31,
                                       b"sig-two!"))
            self.assertFalse(same_executable_image(first, second, name))

    def test_recipe_binds_all_keys_and_bounded_jobs(self) -> None:
        with patch("scripts.release.pcs_fri_gate_binary_rebuild.os.cpu_count", return_value=18):
            command = build_command(self.package, self.manifest,
                                    Path(self.temporary.name) / "out", 8)
        self.assertEqual(command[:5], ["zig", "build", "--build-file",
                                       str(BUILD_FILE), "install"])
        self.assertIn("-Ds31-source=" + str(self.package / "source.s31.json"), command)
        self.assertIn("-Ds31-key=" + str(self.package / "verification-key.json"), command)
        self.assertIn("-Ds31-recursive-key=" + str(self.package / "recursive-verification-key.json"), command)
        self.assertIn("-Ds31-recursive-next-key=" + str(self.package / "recursive-verification-key-level2.json"), command)
        self.assertIn("-Ds31-fold-key=" + str(self.package / "fixed-fold-verification-key.json"), command)
        self.assertEqual(command[-1], "-j8")

    def test_wrong_profile_missing_key_or_excess_jobs_fail_before_build(self) -> None:
        for field, value in (("lowering", "chip"), ("fri_fold_step", 4),
                             ("optimize", "Debug"), ("proof_mode", "blinded")):
            with self.subTest(field=field):
                changed = self.manifest | {field: value}
                with self.assertRaisesRegex(ValueError, "unreviewed"):
                    build_command(self.package, changed, self.package / "out", 8)
        with patch("scripts.release.pcs_fri_gate_binary_rebuild.os.cpu_count", return_value=18):
            with self.assertRaisesRegex(ValueError, "job limit"):
                build_command(self.package, self.manifest, self.package / "out", 13)
        (self.package / "fixed-fold-verification-key.json").unlink()
        with self.assertRaisesRegex(ValueError, "missing sealed"):
            build_command(self.package, self.manifest, self.package / "out", 8)

    def test_resealed_wrong_binary_is_rejected_before_package_execution(self) -> None:
        binary = self.package / "bin" / "s31-guard-native-verifier"
        binary.parent.mkdir()
        binary.write_bytes(b"self-authored but wrong verifier")
        manifest = self.manifest | {"compiler_sha256": "a" * 64,
                                    "zig_version": "0.15.2"}

        @contextmanager
        def checked_copy(_package):
            yield self.package, manifest

        def run(command, **_kwargs):
            if command[:2] == ["zig", "version"]:
                return subprocess.CompletedProcess(command, 0, "0.15.2\n", "")
            output = Path(command[command.index("--prefix") + 1]) / "bin"
            output.mkdir()
            (output / binary.name).write_bytes(b"fresh trusted rebuild")
            return subprocess.CompletedProcess(command, 0, "", "")

        with patch("scripts.release.pcs_fri_gate_binary_rebuild.unpinned_snapshot", checked_copy), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.compiler_fingerprint",
                   return_value="a" * 64), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.same_executable_image",
                   return_value=False), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.subprocess.run",
                   side_effect=run), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.extract_gate") as gate:
            with self.assertRaisesRegex(ValueError, "differs from package executable"):
                rebuild_verifier(self.package, jobs=1)
            gate.assert_not_called()

    def test_accepted_proof_joins_only_native_fri_domain(self) -> None:
        geometry = {
            "status": "incomplete", "proven_release_admissible": False,
            "package_checks": {"native_check_key": "accepted",
                               "verification_key_sha256": "a" * 64,
                               "package_manifest_sha256": "b" * 64},
            "source_binding": {"engine_gitlink": "c" * 40},
            "theorem_inputs": {"D_final_fri_domain": 1 << 21},
            "gate_final_domain": {
                "status": "conditional_source_bound_geometry",
                "fri_input_domain_log": 21,
                "fri_input_domain_rows": 1 << 21,
                "fri_input_degree_bound_log": 20,
                "candidate_paper_protocol4_D0_if_N_is_trace_rows": 1 << 22,
                "native_fri_domain_equals_candidate_paper_protocol4_D0": False,
            },
        }
        proof_control = {"proof_sha256": "d" * 64, "statement_sha256": "e" * 64}
        joined = accepted_gate_geometry(geometry, proof_control, "f" * 64)
        self.assertEqual(joined["native_fri_input_domain_rows"], 1 << 21)
        self.assertEqual(joined["candidate_paper_protocol4_D0_if_N_is_trace_rows"], 1 << 22)
        self.assertFalse(joined["native_fri_domain_equals_candidate_paper_protocol4_D0"])
        self.assertIsNone(joined["native_proven_security_bits"])
        self.assertFalse(joined["proven_release_admissible"])
        with self.assertRaisesRegex(ValueError, "do not join"):
            accepted_gate_geometry(geometry, {}, "f" * 64)
        geometry["theorem_inputs"]["D_final_fri_domain"] = 1 << 22
        with self.assertRaisesRegex(ValueError, "do not join"):
            accepted_gate_geometry(geometry, proof_control, "f" * 64)

        binary = self.package / "bin" / "s31-guard-native-verifier"
        binary.parent.mkdir()
        binary.write_bytes(b"matched verifier")
        proof = self.package / "proof.bin"
        statement = self.package / "statement.json"
        proof.write_bytes(b"proof")
        statement.write_text("{}")
        manifest = self.manifest | {"compiler_sha256": "a" * 64,
                                    "zig_version": "0.15.2"}

        @contextmanager
        def checked_copy(_package):
            yield self.package, manifest

        def run(command, **_kwargs):
            if command[:2] == ["zig", "version"]:
                return subprocess.CompletedProcess(command, 0, "0.15.2\n", "")
            if command[0] == "zig":
                output = Path(command[command.index("--prefix") + 1]) / "bin"
                output.mkdir()
                (output / binary.name).write_bytes(binary.read_bytes())
            return subprocess.CompletedProcess(command, 0, "", "")

        geometry["theorem_inputs"]["D_final_fri_domain"] = 1 << 21
        with patch("scripts.release.pcs_fri_gate_binary_rebuild.unpinned_snapshot", checked_copy), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.compiler_fingerprint",
                   return_value="a" * 64), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.subprocess.run", side_effect=run), \
             patch("scripts.release.pcs_fri_gate_binary_rebuild.extract_gate",
                   return_value=geometry):
            without_proof = rebuild_verifier(self.package, jobs=1)
            self.assertIsNone(without_proof["accepted_proof_gate_geometry"])
            with_proof = rebuild_verifier(self.package, jobs=1, proof=proof,
                                          statement=statement)
            self.assertEqual(with_proof["accepted_proof_gate_geometry"][
                "native_fri_input_domain_rows"], 1 << 21)
            self.assertEqual(with_proof["accepted_proof_gate_geometry"][
                "proof_sha256"], with_proof["supplied_proof"]["proof_sha256"])


if __name__ == "__main__":
    unittest.main()
