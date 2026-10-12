#!/usr/bin/env python3
"""Boundary-value and exact-byte matrix for the admitted mixed v2 record.

This is a parser test. Accepted changed statements need not satisfy the
program; a proof verifier must authenticate their projected public words.
The optional native mode sends the identical source and statement bytes to
the production Zig record parser without building a mixed proof.
"""

from __future__ import annotations

import argparse
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from mixed_eight_lean_correspondence_v2 import S31, SOURCE, STATEMENT, canonical

sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import decode_public_statement  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402

P = 2**31 - 1
SCHEMA = "s31-record-statement-native-corpus-v2"


def matrix() -> list[dict]:
    source_bytes = SOURCE.read_bytes()
    source = json.loads(source_bytes)
    statement_bytes = STATEMENT.read_bytes()
    honest = json.loads(statement_bytes)
    relation = {key: value for key, value in {**source, "version": 1}.items()
                if key != "public_abi"}
    cases: list[dict] = []

    def add(label: str, encoded: bytes, expected: list[int] | None) -> None:
        try:
            actual = decode_public_statement(relation, source["public_abi"], encoded)
        except AbiError:
            actual = None
        if actual != expected:
            raise AssertionError(f"Python codec disagrees for {label}: {actual} != {expected}")
        cases.append({"label": label, "source": source_bytes.decode("utf-8"),
                      "statement": encoded.decode("utf-8"), "expected_words": expected})

    add("honest", statement_bytes, [1, 5, 6, 1, *honest["leaves"][3]["words"]])
    edge = copy.deepcopy(honest)
    edge["leaves"][0]["words"] = [0]
    edge["leaves"][1]["words"] = [0, P - 1]
    edge["leaves"][2]["words"] = [0]
    edge["leaves"][3]["words"] = [P - 1, 0, 1, P - 2]
    edge["leaves"][4]["words"] = list(edge["leaves"][3]["words"])
    add("canonical_field_edges_and_aliases", canonical(edge),
        [0, 0, P - 1, 0, P - 1, 0, 1, P - 2])

    def changed(label: str, edit) -> None:
        value = copy.deepcopy(honest)
        edit(value)
        add(label, canonical(value), None)

    changed("public_bit_above_one", lambda value: value["leaves"][0].update(words=[2]))
    changed("result_bit_above_one", lambda value: value["leaves"][2].update(words=[2]))
    changed("negative_public_bit", lambda value: value["leaves"][0].update(words=[-1]))
    changed("salt_equals_modulus", lambda value: value["leaves"][1].update(words=[P, 6]))
    changed("result_equals_modulus", lambda value: value["leaves"][3].update(words=[P, *value["leaves"][3]["words"][1:]]))
    changed("negative_result_word", lambda value: value["leaves"][3].update(words=[-1, *value["leaves"][3]["words"][1:]]))
    changed("short_salt_vector", lambda value: value["leaves"][1].update(words=[5]))
    changed("long_result_vector", lambda value: value["leaves"][3]["words"].append(11))
    changed("split_public_bit_alias", lambda value: value["leaves"][2].update(words=[0]))
    changed("split_repeated_result_alias", lambda value: value["leaves"][4]["words"].__setitem__(0, 1))
    changed("wrong_salt_field_path", lambda value: value["leaves"][1]["path"][1].update(field="pepper"))
    changed("wrong_result_root_path", lambda value: value["leaves"][3]["path"][0].update(root="request"))
    changed("missing_result_alias_leaf", lambda value: value["leaves"].pop())
    changed("extra_private_input_leaf", lambda value: value["leaves"].insert(2, {"path": [{"root": "x"}], "words": [1, 2, 3, 4]}))
    changed("wrong_abi_digest", lambda value: value.update(abi_sha256="0" * 64))
    changed("wrong_statement_version", lambda value: value.update(version=1))

    canonical_honest = canonical(honest)
    add("missing_terminal_newline", canonical_honest[:-1], None)
    add("extra_terminal_newline", canonical_honest + b"\n", None)
    add("leading_space", b" " + canonical_honest, None)
    add("pretty_json", (json.dumps(honest, indent=2, sort_keys=True) + "\n").encode(), None)
    reordered = {"version": honest["version"], "abi_sha256": honest["abi_sha256"],
                 "leaves": honest["leaves"]}
    add("reordered_envelope_keys", (json.dumps(reordered, separators=(",", ":")) + "\n").encode(), None)
    if len({case["label"] for case in cases}) != len(cases):
        raise AssertionError("duplicate matrix labels")
    return cases


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="also run the production Zig parser")
    args = parser.parse_args()
    cases = matrix()
    accepted = sum(case["expected_words"] is not None for case in cases)
    report = {"schema": "s31-mixed-eight-statement-edges-v2", "accepted": accepted,
              "rejected": len(cases) - accepted}
    if args.native:
        with tempfile.TemporaryDirectory(prefix="s31-mixed-eight-statement-edges-") as temporary:
            path = Path(temporary) / "corpus.json"
            path.write_bytes(canonical({"schema": SCHEMA, "cases": cases}))
            result = subprocess.run(
                ["zig", "build", "--build-file", str(S31 / "build.zig"),
                 "record-statement-parser-corpus", "-j1", "--", str(path)],
                capture_output=True, text=True, check=False,
            )
        if result.returncode:
            raise AssertionError("native parser matrix failed:\n" + result.stderr[-6000:])
        observed = json.loads(result.stdout)
        if observed != {"accepted": report["accepted"], "rejected": report["rejected"]}:
            raise AssertionError(f"native counts differ: {observed} != {report}")
        report["native"] = observed
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
