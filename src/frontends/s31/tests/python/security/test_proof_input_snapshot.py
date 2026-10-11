"""Base verification sees bounded immutable proof and statement bytes."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from runtime.proof_inputs import (MAX_PROOF_BYTES, MAX_STATEMENT_BYTES,
                                  proof_inputs_snapshot)  # noqa: E402


class ProofInputSnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-proof-input-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.proof = self.root / "proof.bin"
        self.statement = self.root / "proof.bin.statement.json"
        self.proof.write_bytes(b"first proof")
        self.statement.write_bytes(b"first statement")

    def test_original_mutation_does_not_change_captured_inputs(self) -> None:
        with proof_inputs_snapshot(self.proof) as (proof, statement):
            self.proof.write_bytes(b"second proof")
            self.statement.write_bytes(b"second statement")
            self.assertEqual(proof.read_bytes(), b"first proof")
            self.assertEqual(statement.read_bytes(), b"first statement")
        self.assertFalse(proof.exists())
        self.assertFalse(statement.exists())

    def test_final_and_parent_symlinks_are_rejected(self) -> None:
        linked_file = self.root / "linked-proof.bin"
        linked_file.symlink_to(self.proof)
        with self.assertRaisesRegex(ValueError, "linked"):
            with proof_inputs_snapshot(linked_file, self.statement):
                self.fail("linked proof admitted")
        linked_directory = self.root / "linked-directory"
        linked_directory.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "linked"):
            with proof_inputs_snapshot(linked_directory / self.proof.name, self.statement):
                self.fail("linked parent admitted")

    def test_oversized_proof_and_statement_are_rejected(self) -> None:
        with self.proof.open("wb") as stream:
            stream.truncate(MAX_PROOF_BYTES + 1)
        with self.assertRaisesRegex(ValueError, "exceeds"):
            with proof_inputs_snapshot(self.proof):
                self.fail("oversized proof admitted")
        self.proof.write_bytes(b"small")
        with self.statement.open("wb") as stream:
            stream.truncate(MAX_STATEMENT_BYTES + 1)
        with self.assertRaisesRegex(ValueError, "exceeds"):
            with proof_inputs_snapshot(self.proof):
                self.fail("oversized statement admitted")

    def test_native_mutation_of_private_copy_is_detected(self) -> None:
        with self.assertRaisesRegex(ValueError, "snapshot changed"):
            with proof_inputs_snapshot(self.proof) as (proof, _statement):
                proof.write_bytes(b"mutated by native")

    @unittest.skipUnless(sys.platform == "darwin" and Path("/tmp").is_symlink(),
                         "macOS /tmp system alias")
    def test_system_tmp_alias_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s31-system-tmp-", dir="/tmp") as directory:
            proof = Path(directory) / "proof.bin"
            proof.write_bytes(b"proof through system alias")
            Path(str(proof) + ".statement.json").write_bytes(b"statement")
            with proof_inputs_snapshot(proof) as (captured, _statement):
                self.assertEqual(captured.read_bytes(), b"proof through system alias")


if __name__ == "__main__":
    unittest.main()
