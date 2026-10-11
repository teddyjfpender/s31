"""Exact source/ABI byte bridge for the pinned public Pair alias example."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parents[1]
SOURCE = FORMAL / "fixtures/record_pair_alias_v2.s31"
CHECKER = "S31/Audit/RecordPairAliasCheck.lean"
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from abi.binding_v2 import DOMAIN, binding_digest, decode_public_statement, encode_public_statement  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")


def check_bytes(source: bytes, abi: bytes) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="s31-record-pair-lean-") as directory:
        work = Path(directory)
        source_file = work / "source.s31"
        abi_file = work / "abi.json"
        source_file.write_bytes(source)
        abi_file.write_bytes(abi)
        return subprocess.run(
            ["lake", "env", "lean", "--run", CHECKER, str(source_file), str(abi_file)],
            cwd=FORMAL, capture_output=True, text=True, check=False,
        )


class RecordPairAliasCheckTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not (FORMAL / ".lake/build/lib/lean/S31/Gadgets/Functional/RecordPinnedPairAliasV2.olean").is_file():
            raise RuntimeError("build first: cd formal/s31 && lake build S31.Gadgets.Functional.RecordPinnedPairAliasV2")
        cls.source = SOURCE.read_bytes()
        cls.produced, _ = compile_text(cls.source.decode("utf-8"))
        cls.abi = cls.produced["public_abi"]
        cls.flat_relation = {**cls.produced, "version": 1}
        del cls.flat_relation["public_abi"]
        cls.abi_bytes = canonical(cls.abi)

    def test_compiler_descriptor_matches_lean_bytes_and_typed_projection(self) -> None:
        result = check_bytes(self.source, self.abi_bytes)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue(json.loads(result.stdout)["accepted"])
        self.assertEqual(self.produced["inputs"], [
            {"kind": "m31", "length": 1, "name": "x", "visibility": "public"},
        ])
        self.assertEqual(self.produced["nodes"], [
            {"name": "square", "op": "mul", "lhs": "x", "rhs": "x"},
        ])
        self.assertEqual(self.produced["public_outputs"], ["square"])
        digest = binding_digest(self.flat_relation, self.abi)
        self.assertEqual(digest, "fb44caccd29cb52bedc6ef2cdf27c7f864b980f5d4ffe709032819b89447c71a")
        self.assertEqual(digest, hashlib.sha256(DOMAIN + self.abi_bytes).hexdigest())
        statement = encode_public_statement(self.flat_relation, self.abi, [[7], [49], [49]])
        self.assertEqual(decode_public_statement(self.flat_relation, self.abi, statement),
                         [7, 49, 0, 0, 0, 0, 0, 0])

    def test_exact_source_and_descriptor_mutations_rejected(self) -> None:
        changed_source = self.source.replace(b"again: square", b"again: x")
        result = check_bytes(changed_source, self.abi_bytes)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)["reason"], "source bytes differ")

        mutations: dict[str, bytes] = {}
        for label in ("field_name", "field_order", "output_alias", "leaf_width", "path"):
            changed = copy.deepcopy(self.abi)
            if label == "field_name":
                changed["result"]["type"]["fields"][1]["name"] = "other"
            elif label == "field_order":
                changed["result"]["leaves"].reverse()
            elif label == "output_alias":
                changed["result"]["leaves"][1]["wire"] = "x"
            elif label == "leaf_width":
                changed["result"]["leaves"][1]["length"] = 2
            else:
                changed["result"]["leaves"][1]["path"][1]["field"] = "other"
            mutations[label] = canonical(changed)
        mutations["noncanonical_spacing"] = json.dumps(self.abi, indent=2).encode() + b"\n"
        mutations["trailing_byte"] = self.abi_bytes + b" "
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                result = check_bytes(self.source, mutated)
                self.assertEqual(result.returncode, 1, result.stderr + result.stdout)
                self.assertEqual(json.loads(result.stdout)["reason"], "canonical ABI bytes differ")

    def test_statement_alias_path_and_digest_mutations_rejected(self) -> None:
        honest = json.loads(encode_public_statement(
            self.flat_relation, self.abi, [[7], [49], [49]]))
        for label in ("first_alias", "second_alias", "path", "digest", "noncanonical_word"):
            changed = copy.deepcopy(honest)
            if label == "first_alias":
                changed["leaves"][1]["words"] = [50]
            elif label == "second_alias":
                changed["leaves"][2]["words"] = [50]
            elif label == "path":
                changed["leaves"][2]["path"][1]["field"] = "other"
            elif label == "digest":
                changed["abi_sha256"] = "0" * 64
            else:
                changed["leaves"][0]["words"] = [2**31 - 1]
            with self.subTest(label=label), self.assertRaises(AbiError):
                decode_public_statement(self.flat_relation, self.abi, canonical(changed))


if __name__ == "__main__":
    unittest.main()
