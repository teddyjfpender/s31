#!/usr/bin/env python3
"""Pin real direct-Gate source rows to independently generated SSA cells.

The existing package checker verifies the entire 512-row native topology.
This fixture exports the source-owned eight-column cells from four real
native packages into Lean, where they are compared with a separate exact
source-byte parser and the modeled direct-Gate row projection.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))

import s31
from package.correspondence import DIRECT_COLUMN_IDS, canonical_ir_bytes, check_package, parse_source
from test_source_mutation_correspondence import CORPUS_SHA256, corpus, corpus_digest
from text_frontend import compile_text

SELECTED = (("00:direct", "case00"), ("07:aliases", "case07"),
            ("14:direct", "case14"), ("15:comments", "case16"))
SNAPSHOT = ROOT / "formal/s31/fixtures/correspondence/native_source_cells.json"
LEAN = (ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/"
        "GeneratedNativeSourceCells.lean")
P = 2_147_483_647
EXPORTER_SOURCE = ROOT / "src/frontends/s31/runtime/mvp_runtime.zig"
LOWERING_SOURCE = ROOT / "src/frontends/s31/language/relation_compiler.zig"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def chosen_samples():
    samples = corpus()
    if corpus_digest(samples) != CORPUS_SHA256:
        raise AssertionError("pinned positional source corpus changed")
    by_label = {sample.label: sample for sample in samples}
    if not {label for label, _ in SELECTED} <= set(by_label):
        raise AssertionError("native source labels missing from pinned corpus")
    return [(by_label[label], prefix) for label, prefix in SELECTED]


def provenance() -> dict:
    gitlink = subprocess.run(
        ["git", "rev-parse", "HEAD:deps/stwo-zig"], cwd=ROOT,
        capture_output=True, text=True, check=True).stdout.strip()
    if len(gitlink) != 40 or any(c not in "0123456789abcdef" for c in gitlink):
        raise AssertionError("Stwo engine gitlink is not a 40-digit commit ID")
    return {"engine_gitlink": gitlink,
            "exporter_source_sha256": sha(EXPORTER_SOURCE.read_bytes()),
            "lowering_source_sha256": sha(LOWERING_SOURCE.read_bytes())}


def expected_cells(sample) -> list[list[int]]:
    """Compute source-owned cells from generator steps, independent of Zig.

    This deliberately does not call `check_source_fixed_rows` or read native
    gate lists. The accepted source parser and Lean byte fixture independently
    check that these generator steps are the actual source instructions.
    """
    products = sum(op == ".*" for op, _, _ in sample.steps)
    add_rows = 476 - products
    uses = [0] * (sample.gate_count + 1)
    for _, lhs, rhs in sample.steps:
        uses[lhs] += 1
        uses[rhs] += 1
    uses[sample.return_id] += 4
    cells = []
    prior_adds = prior_products = 0
    for wire_id, (op, lhs, rhs) in enumerate(sample.steps, 1):
        product = op == ".*"
        trace_row = (add_rows + 28 + prior_products if product
                     else 3 + prior_adds)
        cells.append([trace_row, int(not product), 0, 0, int(product),
                      22 + lhs, 22 + rhs, 22 + wire_id, uses[wire_id]])
        prior_products += product
        prior_adds += not product
    if (len(cells) != sample.gate_count or
            len({cell[0] for cell in cells}) != len(cells) or
            any(cell[0] >= 512 for cell in cells)):
        raise AssertionError("independent source row schedule is invalid")
    return cells


def source_identity(sample, prefix: str) -> dict:
    source = sample.source.encode()
    relation, syntax = parse_source(source)
    produced, _ = compile_text(sample.source)
    if relation != produced or syntax["output"] != sample.return_id:
        raise AssertionError(f"source parser disagreement: {sample.label}")
    steps = [("+" if node["op"] == "add" else ".*", node["lhs"], node["rhs"])
             for node in syntax["instructions"]]
    if steps != list(sample.steps):
        raise AssertionError(f"source instructions differ from generator: {sample.label}")
    normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
    return {"label": sample.label, "lean_prefix": prefix,
            "program_name": relation["name"],
            "source_utf8": sample.source,
            "normalized_json": normalized.decode("utf-8"),
            "source_sha256": sha(source), "normalized_sha256": sha(normalized),
            "canonical_ir_sha256": sha(canonical_ir_bytes(syntax)),
            "source_rows": expected_cells(sample)}


def native_case(work: Path, sample, prefix: str) -> dict:
    identity = source_identity(sample, prefix)
    source = work / f"{prefix}.s31"
    source.write_bytes(sample.source.encode())
    package = s31.build(source, work / f"package-{prefix}", "direct-gate")
    check_package(package)
    prover = package / "bin" / f"s31-{identity['program_name']}-prover"
    if not prover.is_file():
        raise AssertionError(f"native prover missing: {prover}")
    exported = json.loads(s31.invoke(str(prover), "inspect-topology"))
    packaged = json.loads((package / "gate-topology.json").read_bytes())
    if exported != packaged:
        raise AssertionError("fresh native export differs from sealed topology")
    manifest = json.loads((package / "manifest.json").read_bytes())
    key = json.loads((package / "verification-key.json").read_bytes())
    if (manifest.get("source_text_sha256") != identity["source_sha256"] or
            manifest.get("program_sha256") != identity["normalized_sha256"] or
            manifest.get("canonical_ir_sha256") != identity["canonical_ir_sha256"] or
            exported.get("preprocessed_root") != key.get("preprocessed_root")):
        raise AssertionError("native source, canonical IR or fixed root changed")
    columns = exported["columns"]
    if ([column["id"] for column in columns] != list(DIRECT_COLUMN_IDS) or
            any(len(column["values"]) != 512 for column in columns)):
        raise AssertionError("native direct-Gate fixed column shape changed")
    all_values = [value for column in columns for value in column["values"]]
    if any(type(value) is not int or not 0 <= value < P for value in all_values):
        raise AssertionError("native fixed column contains a noncanonical word")
    observed = []
    for expected in identity["source_rows"]:
        trace_row = expected[0]
        actual = [trace_row, *(column["values"][trace_row] for column in columns)]
        if actual != expected:
            raise AssertionError(f"{sample.label} native source row {trace_row} differs")
        observed.append(actual)
    full_bytes = b"".join(struct.pack("<I", value) for value in all_values)
    identity.update({"preprocessed_root": exported["preprocessed_root"],
                     "exporter_binary_sha256": sha(prover.read_bytes()),
                     "compiler_sha256": manifest["compiler_sha256"],
                     "all_fixed_columns_sha256": sha(full_bytes),
                     "native_source_rows": observed})
    return identity


def render_lean(snapshot: dict) -> str:
    lines = [
        "import S31.Gadgets.Functional.Correspondence.GeneratedMutationRows",
        "import S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows",
        "",
        "/-!", "Native `inspect-topology` source-row cells for four checked direct-Gate",
        "programs. The generator checks the complete sealed topology and",
        "compares each captured eight-column row with an independently parsed",
        "positional DAG. These literal cell values are then checked against",
        "Lean's exact source-byte parser and modeled physical row projection.",
        "Proof acceptance and PCS authentication are not inferred here.", "-/", "",
        "namespace S31.Functional.Correspondence.GeneratedNativeSourceCells", "",
        "open S31.Functional.SSAAirColumnCells",
        "open S31.Functional.SSAAliasTextBytes",
        "open S31.Functional.Correspondence.GeneratedMutationRows",
        "open S31.Functional.Correspondence.AliasCanonicalIrBytes",
        "open S31.Functional.Correspondence.SourceDeterminedDirectRows", "",
        f"-- Stwo engine gitlink: {snapshot['provenance']['engine_gitlink']}",
        f"-- Native exporter source SHA-256: {snapshot['provenance']['exporter_source_sha256']}",
        f"-- Relation lowering source SHA-256: {snapshot['provenance']['lowering_source_sha256']}",
        "",
        "set_option maxRecDepth 8192", "set_option maxHeartbeats 2000000", "",
    ]
    fields = ("traceRow", "addFlag", "subFlag", "mulFlag",
              "pointwiseMulFlag", "in0", "in1", "out", "mults")
    for case in snapshot["cases"]:
        prefix = case["lean_prefix"]
        lines += [
            f"-- {case['label']}; source SHA-256: {case['source_sha256']}",
            f"-- Normalized JSON SHA-256: {case['normalized_sha256']}",
            f"-- Native exporter binary SHA-256: {case['exporter_binary_sha256']}",
            f"-- Native full fixed-column SHA-256: {case['all_fixed_columns_sha256']}",
            f"-- Native preprocessed root: {case['preprocessed_root']}",
            f"def {prefix}NativeCells : List ColumnCell := [",
        ]
        for cell in case["native_source_rows"]:
            parts = ", ".join(f"{name} := {value}" for name, value in zip(fields, cell, strict=True))
            lines.append(f"  {{{parts}}},")
        lines += [
            "]",
            f"theorem {prefix}_source_to_native_cells :",
            f"    checkAliasCanonical {prefix}Bytes {prefix}NormalizedBytes",
            f"      {prefix}CanonicalBytes = some {prefix}Certificate ∧",
            f"    {prefix}NativeCells =",
            f"      expectedCells {prefix}Certificate (compiledAddRows {prefix}Certificate) := by",
            "  constructor",
            f"  · exact {prefix}CanonicalChecks.1",
            "  · decide", "",
        ]
    lines += ["end S31.Functional.Correspondence.GeneratedNativeSourceCells", ""]
    return "\n".join(lines)


def validate_snapshot(snapshot: dict) -> None:
    if (snapshot.get("schema") != "s31-native-source-cells-v1" or
            snapshot.get("corpus_sha256") != CORPUS_SHA256 or
            len(snapshot.get("cases", [])) != len(SELECTED)):
        raise AssertionError("native source-cell fixture header differs")
    for (sample, prefix), case in zip(chosen_samples(), snapshot["cases"], strict=True):
        identity = source_identity(sample, prefix)
        for key, value in identity.items():
            if case.get(key) != value:
                raise AssertionError(f"{sample.label} fixture {key} differs")
        if (case.get("native_source_rows") != identity["source_rows"] or
                not isinstance(case.get("preprocessed_root"), str) or
                len(case["preprocessed_root"]) != 64 or
                not isinstance(case.get("exporter_binary_sha256"), str) or
                len(case["exporter_binary_sha256"]) != 64 or
                not isinstance(case.get("compiler_sha256"), str) or
                len(case["compiler_sha256"]) != 64 or
                not isinstance(case.get("all_fixed_columns_sha256"), str) or
                len(case["all_fixed_columns_sha256"]) != 64):
            raise AssertionError(f"{sample.label} native fixture rows differ")
    if snapshot.get("provenance") != provenance():
        raise AssertionError("native exporter sources or engine gitlink changed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build and inspect real native packages")
    parser.add_argument("--write", action="store_true", help="write the native snapshot and Lean module")
    parser.add_argument("--work", type=Path, help="retain native packages")
    args = parser.parse_args()
    if args.write and not args.native:
        parser.error("--write requires --native")
    if args.native:
        def run(work: Path) -> dict:
            work.mkdir(parents=True, exist_ok=True)
            start_provenance = provenance()
            cases = []
            for sample, prefix in chosen_samples():
                print(f"native source-cell export: {sample.label}", file=sys.stderr, flush=True)
                cases.append(native_case(work, sample, prefix))
                if provenance() != start_provenance:
                    raise AssertionError("exporter sources or engine gitlink changed during native build")
            if len({case["compiler_sha256"] for case in cases}) != 1:
                raise AssertionError("native packages were built with different compiler fingerprints")
            return {"schema": "s31-native-source-cells-v1",
                    "corpus_sha256": CORPUS_SHA256,
                    "provenance": start_provenance, "cases": cases}
        if args.work:
            snapshot = run(args.work.resolve())
        else:
            with tempfile.TemporaryDirectory(prefix="s31-native-source-cells-") as temp:
                snapshot = run(Path(temp))
    else:
        snapshot = json.loads(SNAPSHOT.read_bytes())
    validate_snapshot(snapshot)
    lean = render_lean(snapshot)
    encoded = json.dumps(snapshot, indent=2, sort_keys=True).encode() + b"\n"
    if args.write:
        SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
        SNAPSHOT.write_bytes(encoded)
        LEAN.write_text(lean)
        print(f"wrote {SNAPSHOT.relative_to(ROOT)} and {LEAN.relative_to(ROOT)}")
    elif SNAPSHOT.read_bytes() != encoded or LEAN.read_text() != lean:
        raise AssertionError("committed native source-cell fixture differs")
    else:
        print(f"checked {len(snapshot['cases'])} native source-cell cases")


if __name__ == "__main__":
    main()
