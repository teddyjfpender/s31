#!/usr/bin/env python3
"""Inspect fixed native Gate pin producers for the bounded control program.

This is an executable source/topology check. It does not authenticate trace
values or prove that accepted lookup claims imply an exact global event list.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.control_air_correspondence import check_control_air  # noqa: E402
from package.effects_gate_ownership import _load_topology  # noqa: E402
from package.verify import verify_package  # noqa: E402

PINS = list(range(3, 11))


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("control Gate pin roster audit: " + reason)


def check_pin_roster(topology: dict[str, object]) -> dict[str, object]:
    """Check the fixed selected rows; injected topology is for tests only."""
    columns = topology.get("columns")
    require(type(columns) is list and all(type(c) is dict for c in columns),
            "missing fixed columns")
    by_id = {c.get("id"): c.get("values") for c in columns}
    require(len(by_id) == len(columns), "duplicate fixed column id")
    addresses = by_id.get("qm31_ops_out_address")
    mults = by_id.get("qm31_ops_mults")
    input0 = by_id.get("qm31_ops_in0_address")
    input1 = by_id.get("qm31_ops_in1_address")
    converted = by_id.get("m31_to_u32_output_addr")
    converted_mults = by_id.get("m31_to_u32_multiplicity")
    require(all(type(a) is list for a in (addresses, mults, input0, input1,
                                          converted, converted_mults)) and
            len(addresses) == len(mults) == len(input0) == len(input1) and
            len(converted) == len(converted_mults),
            "fixed output/multiplicity column shape changed")
    flags = {
        kind: by_id.get("qm31_ops_" + tag + "_flag")
        for kind, tag in (("add", "add"), ("sub", "sub"),
                          ("mul", "mul"), ("pointwise_mul", "pointwise_mul"))
    }
    require(all(type(values) is list and len(values) == len(addresses)
                for values in flags.values()) and
            all(type(value) is int and value in (0, 1)
                for values in flags.values() for value in values) and
            all(sum(flags[kind][row] for kind in flags) == 1
                for row in range(len(addresses))),
            "QM31 fixed operation flags are not one-hot")
    n_vars = topology.get("n_vars")
    require(type(n_vars) is int and 10 < n_vars < 2**31 - 1,
            "invalid Gate address bound")
    require(all(type(address) is int and 0 <= address < n_vars
                for address in addresses + converted + input0 + input1) and
            all(type(mult) is int and 0 <= mult < 2**31 - 1
                for mult in mults + converted_mults),
            "noncanonical fixed address or multiplicity")
    for kind, kind_flags in flags.items():
        fixed = [{"in0": input0[row], "in1": input1[row], "out": addresses[row]}
                 for row, enabled in enumerate(kind_flags) if enabled == 1]
        require(topology.get(kind) == fixed,
                f"{kind} graph rows differ from fixed physical row order")
    active = [(row, address, mult) for row, (address, mult) in
              enumerate(zip(addresses, mults)) if mult > 0]
    active_conversion = [address for address, mult in
                         zip(converted, converted_mults) if mult > 0]
    active_addresses = [address for _, address, _ in active]
    require(len(set(active_addresses)) == len(active_addresses),
            "two positive QM31 rows own one output address")
    require(len(set(active_conversion)) == len(active_conversion) and
            not set(active_addresses).intersection(active_conversion),
            "positive conversion output collides with another producer")
    pin_rows = [(row, address, mult) for row, address, mult in active
                if address in PINS]
    require([address for _, address, _ in pin_rows] == PINS and
            all(mult == 1 for _, _, mult in pin_rows),
            "ordered public pins lack unique unit-multiplicity QM31 rows")
    require(topology.get("output") == [2, *PINS],
            "public output ABI pin order changed")
    return {
        "schema": "s31-control-gate-pin-roster-v1",
        "public_pin_addresses": PINS,
        "public_pin_physical_rows": [row for row, _, _ in pin_rows],
        "positive_qm31_producers": len(active),
        "positive_conversion_producers": len(active_conversion),
        "positive_qm31_addresses_unique": True,
        "positive_conversion_addresses_disjoint": True,
        "all_component_producer_coverage_proved": False,
        "global_lookup_claim_authenticated": False,
    }


def audit(package: Path) -> dict[str, object]:
    """Production path always captures topology from a validated binary."""
    package = package.resolve()
    verify_package(package)
    correspondence = check_control_air(package)
    manifest = json.loads((package / "manifest.json").read_text())
    topology = _load_topology(package / "bin" / f"s31-{manifest['name']}-prover")
    require(topology.get("program_sha256") == correspondence["program_sha256"] and
            topology.get("preprocessed_root") == correspondence["preprocessed_root"],
            "second native topology capture differs from sealed source")
    return {**check_pin_roster(topology),
            "program_sha256": correspondence["program_sha256"],
            "preprocessed_root": correspondence["preprocessed_root"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    args = parser.parse_args()
    print(json.dumps(audit(args.package), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
