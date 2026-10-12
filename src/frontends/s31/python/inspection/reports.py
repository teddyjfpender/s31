"""Source equation and cost reports derived from sealed S31 packages.

The package verifier is supplied by the CLI boundary so this module
cannot accidentally accept an unverified package on its own.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Callable


def explain(package: Path, verify_package: Callable[[Path], dict]) -> dict:
    verify_package(package)
    report = json.loads((package / "cost-report.json").read_text())
    relation = json.loads((package / "source.s31.json").read_text())
    locations = (json.loads((package / "source-map.json").read_text())["nodes"]
                 if (package / "source-map.json").exists() else {})
    operations = {item["name"]: item["op"] for item in relation["nodes"]}
    components = ("qm31", "m31_to_u32", "eq", "triple_xor", "blake_g")
    nodes = []
    groups = {}
    for item in report["source_map"]:
        name = item["name"]
        entry = {
            "name": name,
            "op": operations.get(name, "input"),
            "source": locations.get(name),
            "gate_rows": {component: item[f"{component}_end"] - item[f"{component}_start"]
                          for component in components},
            "canonical_id": item["canonical_id"],
        }
        nodes.append(entry)
        if entry["source"] is not None:
            key = (entry["source"]["line"], entry["source"]["column"])
            if key not in groups:
                groups[key] = {"source": entry["source"], "nodes": [],
                               "gate_rows": {component: 0 for component in components},
                               "chip_rows": 0, "_ids": set()}
            group = groups[key]
            group["nodes"].append(name)
            if entry["canonical_id"] not in group["_ids"]:
                group["_ids"].add(entry["canonical_id"])
                for component in components:
                    group["gate_rows"][component] += entry["gate_rows"][component]
                if entry["op"] == "repeat" and report["chip"] is not None:
                    group["chip_rows"] += report["chip"]["rounds"]
    source_expressions = []
    for group in groups.values():
        del group["_ids"]
        source_expressions.append(group)
    return {
        "name": report["name"], "profile": report["profile"],
        "chip": report["chip"], "raw": report["raw"], "padded": report["padded"],
        "preprocessed_cells": report["preprocessed_cells"],
        "preprocessed_columns": report["preprocessed_columns"],
        "canonical_ir_sha256": report["canonical_ir_sha256"], "nodes": nodes,
        "source_expressions": source_expressions,
        "typed_interface": (json.loads((package / "typed-interface.json").read_text())
                            if (package / "typed-interface.json").exists() else None),
    }


def equations(package: Path, verify_package: Callable[[Path], dict]) -> dict:
    """Explain node semantics; this is not a dump of the pinned circuit AIR."""
    report = explain(package, verify_package)
    relation = json.loads((package / "source.s31.json").read_text())
    cost_nodes = {node["name"]: node for node in report["nodes"]}
    shapes = {item["name"]: (item["kind"], item["length"]) for item in relation["inputs"]}
    nodes = []
    hashes = {
        "hash_blake2s", "hash_blake2s_leaf", "hash_blake2s_pair",
        "hash_poseidon2_leaf", "hash_poseidon2_pair",
    }
    for node in relation["nodes"]:
        name, op = node["name"], node["op"]
        field_equations: list[str] = []
        functional_spec: str | None = None
        notes: list[str] = []
        if op == "constant":
            shape = ("m31", node["length"])
            field_equations.append(f"{name}[j] - {node['constant']} = 0")
        elif op == "sum_lanes":
            shape = ("m31", 1)
            length = shapes[node["lhs"]][1]
            field_equations.append(f"{name}[0] - sum({node['lhs']}[j] for j=0..{length - 1}) = 0")
        elif op == "array_get":
            shape = (shapes[node["lhs"]][0], 1)
            field_equations.append(f"{name}[0] - {node['lhs']}[{node['index']}] = 0")
            notes.append("This is a view of an already constrained array position; it introduces no independent witness value.")
        elif op == "array_slice":
            shape = (shapes[node["lhs"]][0], node["length"])
            field_equations.append(
                f"{name}[j] - {node['lhs']}[{node['index']}+j] = 0, 0 <= j < {node['length']}")
            notes.append("Aligned packed words can alias source wires; shifted views use constrained coordinate unpacking and repacking.")
        elif op == "array_concat":
            left = shapes[node["lhs"]]
            right = shapes[node["rhs"]]
            shape = (left[0], left[1] + right[1])
            field_equations.extend((
                f"{name}[j] - {node['lhs']}[j] = 0, 0 <= j < {left[1]}",
                f"{name}[{left[1]}+j] - {node['rhs']}[j] = 0, 0 <= j < {right[1]}",
            ))
            notes.append("This is a concatenated view of constrained positions; it introduces no independent witness values.")
        elif op in {"int_view", "int_add_checked", "int_add_wrapping", "int_sub_checked", "int_sub_wrapping", "int_le", "int_mul_wrapping", "int_mul_checked"}:
            width = node["constant"] & 255
            signed = bool(node["constant"] & 256)
            limb_count = max(1, width // 16)
            base = 256 if width == 8 else 65536
            shape = ("m31", 1) if op == "int_le" else ("u16", limb_count)
            functional_spec = f"{name} = {op}<{('i' if signed else 'u')}{width}>({node['lhs']}" + (")" if op == "int_view" else f", {node['rhs']})")
            if width == 8:
                if op == "int_view":
                    field_equations.append(f"256*{node['lhs']}[0] is range checked as u16, proving 0 <= {node['lhs']}[0] < 256")
                else:
                    field_equations.append("Both operand bytes are proved below 256 by their producer or a local range gadget.")
            if op in {"int_mul_wrapping", "int_mul_checked"}:
                byte_count = width // 8
                product_bytes = byte_count if op == "int_mul_wrapping" else 2 * byte_count
                if width > 8:
                    field_equations.append(
                        "Each input u16 limb is split as limb[j] = byte[2j] + 256*byte[2j+1]. The low byte has a direct range check; the high byte's bound follows from the u16 limb and the equation.")
                field_equations.extend((
                    f"c[0] = 0; 0 <= digit[k] < 256; 0 <= c[k+1] < 65536, for 0 <= k < {product_bytes}",
                    "c[k] + sum_{i+j=k, 0<=i,j<n} a[i]*b[j] - digit[k] - 256*c[k+1] = 0",
                    (f"{name}[0] = digit[0]" if width == 8 else
                     f"{name}[j] = digit[2j] + 256*digit[2j+1]"),
                ))
                if op == "int_mul_checked":
                    field_equations.append(f"c[{product_bytes}] = 0, fixing the complete 2W-bit product")
                    if signed:
                        field_equations.append("For M=2^W and U=low+M*high, constrain high+M*c = sign(a)*b + sign(b)*a + sign(low)*(M-1), with c=sign(a)*sign(b)+sign(low). Each correction carry is bounded (base 256 for W=8, otherwise 2^16).")
                        notes.append("The upper product word equals the sign extension required for a representable signed result.")
                    else:
                        field_equations.append("Every high product byte is zero, so the unsigned result fits W bits.")
                else:
                    notes.append("Only the low product bytes are computed; the final carry is discarded. Each column equality is below the M31 modulus on both sides.")
                if signed and op == "int_mul_wrapping":
                    notes.append("Signed wrapping multiplication uses the same low bit pattern as unsigned multiplication.")
            elif op == "int_view":
                notes.append("The view binds width and signedness into the canonical relation. Its result aliases the input limbs.")
            else:
                field_equations.append(f"c[0] = 0; c[j] in {{0,1}}; each arithmetic digit is in [0,{base - 1}]")
                if op.startswith("int_add"):
                    field_equations.append(f"{node['lhs']}[j] + {node['rhs']}[j] + c[j] - {name}[j] - {base}*c[j+1] = 0")
                else:
                    dividend, divisor = (node["rhs"], node["lhs"]) if op == "int_le" else (node["lhs"], node["rhs"])
                    digit = "d" if op == "int_le" else name
                    field_equations.append(f"{dividend}[j] + {base}*c[j+1] - {divisor}[j] - c[j] - {digit}[j] = 0")
                if op.endswith("checked"):
                    field_equations.append("Equal operand signs for add, or opposite signs for sub, cannot produce a changed result sign." if signed else "The final carry/borrow is zero.")
                elif op == "int_le":
                    field_equations.append(f"Unsigned result = 1 - c[{limb_count}]; signed result chooses the left sign when signs differ, otherwise unsigned result")
                else:
                    notes.append(f"Wrapping discards c[{limb_count}] and returns the low {width} bits.")
                if signed:
                    notes.append("Top-limb sign bits are Boolean and extracted with a bounded low part: top = low + sign*2^(top_limb_bits-1).")
        elif op in {"u256_add", "u256_le", "u256_add_checked", "u256_sub", "u256_sub_checked"}:
            shape = ("u16", 16) if op in {"u256_add", "u256_add_checked", "u256_sub", "u256_sub_checked"} else ("m31", 1)
            functional_spec = f"{name} = {op}({node['lhs']}, {node['rhs']})"
            if op in {"u256_add", "u256_add_checked"}:
                field_equations.extend((
                    f"c[0] = 0; c[i] in {{0,1}}; {name}[i] in [0,65535]",
                    f"{node['lhs']}[i] + {node['rhs']}[i] + c[i] - {name}[i] - 65536*c[i+1] = 0",
                    ("the final carry is zero (checked addition)" if op == "u256_add_checked"
                     else "the final carry is discarded (addition modulo 2^256)"),
                ))
            elif op in {"u256_sub", "u256_sub_checked"}:
                field_equations.extend((
                    f"b[0] = 0; b[i] in {{0,1}}; {name}[i] in [0,65535]",
                    f"{node['lhs']}[i] + 65536*b[i+1] - {node['rhs']}[i] - b[i] - {name}[i] = 0",
                    ("the final borrow is zero (checked subtraction)" if op == "u256_sub_checked"
                     else "the final borrow is discarded (subtraction modulo 2^256)"),
                ))
            else:
                field_equations.extend((
                    "b[0] = 0; b[i] in {0,1}; d[i] in [0,65535]",
                    f"{node['rhs']}[i] + 65536*b[i+1] - {node['lhs']}[i] - b[i] - d[i] = 0",
                    f"{name}[0] = 1 - b[16]",
                ))
            notes.append("These are limb equations; the circuit also range checks each digit and constrains each carry/borrow Boolean.")
        elif op == "u32_lt":
            shape = ("m31", 1)
            functional_spec = f"{name} = unsigned32({node['lhs']}) < unsigned32({node['rhs']})"
            field_equations.extend((
                "b[0] = 1; b[i] in {0,1}; d[i] in [0,65535]",
                f"{node['rhs']}[i] + 65536*b[i+1] - {node['lhs']}[i] - b[i] - d[i] = 0, i=0..1",
                f"{name}[0] = 1 - b[2]",
            ))
            notes.append("The initial borrow of one makes equality false; both limbs are range checked.")
        elif op == "hash_sha256d_header":
            shape = ("u16", 16)
            functional_spec = f"{name} = SHA256(SHA256(LE16_bytes({node['lhs']}[0..39])))"
            field_equations.extend((
                "input and output limbs each lie in [0,65535]",
                "each decomposed bit b satisfies b * (b - 1) = 0",
                "low16 + 65536*carry_low = low16_a + low16_b",
                "high16 + 65536*carry_high = high16_a + high16_b + carry_low",
            ))
            notes.append("SHA-256 uses three fixed 64-byte compression blocks: two for the header and one for the second hash. Padding and bit lengths 640 and 256 are constants.")
            notes.append("Rotations and shifts permute constrained bits; choose, majority, and XOR use field multiplication. The output is raw digest bytes in little-endian u16 limbs.")
        elif op == "bitcoin_target_mainnet":
            shape = ("u16", 16)
            functional_spec = f"{name} = DecodeCompactMainnet(LE16_bytes({node['lhs']})[72..75])"
            field_equations.extend((
                "header nBits limbs decompose into Boolean bits and four little-endian bytes",
                "s[e] in {0,1}; sum(s[e], e=1..32)=1; sum(e*s[e])=exponent",
                "target byte[j] = sum(s[e] * mantissa byte[j-e+3]) over valid e and byte positions",
                "mantissa sign bit = 0; target bytes[28..31] = 0; target != 0",
            ))
            notes.append("The high-byte zero rule is equivalent to target <= Bitcoin mainnet powLimit, whose highest nonzero byte is 27 and equals 255.")
        elif op == "bitcoin_block_work":
            shape = ("u16", 16)
            functional_spec = f"{name} = floor(2^256 / ({node['lhs']} + 1))"
            field_equations.extend((
                "target + 1 and quotient + 1 are checked 256-bit additions",
                "q*d + r = (2^256-1)-target across 64 base-256 columns, with c[0]=c[64]=0",
                "0 <= r < d via sixteen base-65536 subtract-and-borrow equations",
            ))
            notes.append("Each byte convolution column and carry equation stays below M31, so field equality is integer equality. Zero target and maximum target are rejected.")
        elif op in {"bitcoin_prev_hash", "bitcoin_header_bits", "bitcoin_header_time"}:
            start, length = (2, 16) if op == "bitcoin_prev_hash" else (34, 2) if op == "bitcoin_header_time" else (36, 2)
            shape = ("u16", length)
            field_equations.append(f"{name}[j] = {node['lhs']}[{start}+j], 0 <= j < {length}")
            notes.append("This is a fixed view of already range-checked header limbs; assertions against the view reuse those same circuit wires.")
        elif op == "bitcoin_genesis_hash_mainnet":
            shape = ("u16", 16)
            field_equations.append(f"{name}[j] = little_endian_u16(mainnet_genesis_raw_bytes[2j:2j+2]), 0 <= j < 16")
            notes.append("The raw mainnet genesis digest is a compiler-owned constant, not a prover input.")
        elif op in hashes:
            shape = ("m31", 8)
            arguments = ", ".join(node[key] for key in ("lhs", "rhs") if key in node)
            functional_spec = f"{name} = {op}({arguments})"
            notes.append("The hash's internal circuit equations are not expanded here.")
        else:
            shape = ("m31", shapes[node["lhs"]][1])
            lhs = f"{node['lhs']}[j]"
            rhs = f"{node['rhs']}[j]" if "rhs" in node else ""
            constant = node.get("constant")
            if op == "cast_m31":
                field_equations.append(f"{name}[j] - {lhs} = 0")
                notes.append("The u16 input has a separate range obligation.")
            elif op == "add":
                field_equations.append(f"{name}[j] - {lhs} - {rhs} = 0")
            elif op == "mul":
                field_equations.append(f"{name}[j] - {lhs} * {rhs} = 0")
            elif op == "inv":
                field_equations.append(f"{lhs} * {name}[j] - 1 = 0")
                notes.append("A zero active lane has no satisfying inverse. Each packed group uses a pointwise product, difference, and arithmetic zero assertion; the assertion preserves one producer per lookup address.")
            elif op == "is_zero":
                field_equations.extend((
                    f"{lhs} * inverse - (1 - {name}[0]) = 0",
                    f"{lhs} * {name}[0] = 0",
                ))
                notes.append("These two equations force the output to be one exactly when the input is zero; the Boolean rule follows algebraically. Inverse is a private witness.")
            elif op in {"bool_not", "bool_and", "bool_or", "bool_xor", "bool_select"}:
                operands = [f"{node['lhs']}[0]"]
                if op != "bool_not":
                    operands.append(f"{node['rhs']}[0]")
                if op == "bool_select":
                    operands.append(f"{node['selector']}[0]")
                for operand in operands:
                    field_equations.append(f"{operand} * ({operand} - 1) = 0")
                a = operands[0]
                b = operands[1] if len(operands) > 1 else ""
                formula = {
                    "bool_not": f"1 - {a}",
                    "bool_and": f"{a} * {b}",
                    "bool_or": f"{a} + {b} - {a} * {b}",
                    "bool_xor": f"{a} + {b} - 2 * {a} * {b}",
                    "bool_select": f"(1 - {operands[-1]}) * {a} + {operands[-1]} * {b}",
                }[op]
                field_equations.append(f"{name}[0] - ({formula}) = 0")
                notes.append("Boolean operands are constrained to 0 or 1; the output is Boolean by the formula, with no output hint.")
            elif op == "add_const":
                field_equations.append(f"{name}[j] - {lhs} - {constant} = 0")
            elif op == "mul_const":
                field_equations.append(f"{name}[j] - {lhs} * {constant} = 0")
            elif op == "select":
                shape = shapes[node["lhs"]]
                selector = f"{node['selector']}[0]"
                field_equations.extend((
                    f"{selector} * ({selector} - 1) = 0",
                    f"{name}[j] - (1 - {selector}) * {lhs} - {selector} * {rhs} = 0",
                ))
                if shape[0] == "u16":
                    notes.append("Every selected limb equals one of two range-checked u16 limbs because the selector is Boolean; no new range witness is needed.")
            elif op == "repeat":
                mixes_lanes = any(step["op"] == "mix4" for step in node["body"])
                functional_spec = (f"{name} = F^{node['rounds']}({lhs})" if mixes_lanes else
                                   f"{name}[j] = F^{node['rounds']}({lhs})")
                for index, step in enumerate(node["body"], start=1):
                    previous = f"v{index - 1}"
                    if step["op"] == "square":
                        expression = f"{previous} * {previous}"
                    elif step["op"] == "add_const":
                        expression = f"{previous} + {step['constant']}"
                    elif step["op"] == "mix4":
                        expression = f"{previous} + splat<4>(sum({previous}))"
                    else:
                        expression = f"{previous} * {step['constant']}"
                    notes.append(f"F step {index}: v{index} = {expression} (v0 is the current state)")
                notes.append("The selected profile either unrolls this body or uses the pinned step AIR chip.")
            else:
                functional_spec = f"{name} = {op}({lhs})"
                notes.append("No source-level equation is available for this operation.")
        shapes[name] = shape
        cost = cost_nodes.get(name, {})
        nodes.append({
            "name": name, "op": op,
            "output": {"kind": shape[0], "length": shape[1]},
            "field_equations": field_equations,
            "functional_spec": functional_spec,
            "notes": notes,
            "index": "j ranges over the output array" if shape[1] > 1 else "j=0",
            "source": cost.get("source"),
            "canonical_id": cost.get("canonical_id"),
            "builder_gate_rows": cost.get("gate_rows"),
            "expanded_air_terms": False,
        })
    assertions = [f"{item['lhs']}[j] - {item['rhs']}[j] = 0"
                  for item in relation["assertions"]]
    return {
        "schema": "s31-semantic-equations-v1",
        "program": relation["name"],
        "field_modulus": 2147483647,
        "scope": ("Source-level field equations. The pinned circuit AIR also constrains "
                  "wire lookup closure, public binding, range/bit rules, and profile-specific rows. "
                  "Builder gate counts are not physical AIR row ownership."),
        "profile": report["profile"],
        "nodes": nodes,
        "assertions": assertions,
        "public_inputs": [item["name"] for item in relation["inputs"]
                          if item["visibility"] == "public"],
        "public_outputs": relation["public_outputs"],
    }
