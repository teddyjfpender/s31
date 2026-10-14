"""Independent gate-order replay of the structural compiler's finalization.

This covers the fixed-base constant pass and source input guesses in an
assignment-specific exported graph. It is an executable audit, not a proof
that the installed prover committed this graph.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PINNED_SOURCES = {
    "deps/stwo-zig/src/frontends/circuit/builder/finalize_constants.zig":
        "64e9e2a82512eca5b0f194b650f0c02e4ef5a6596d4015e6c90b78d04efc2b6b",
    "deps/stwo-zig/src/frontends/circuit/builder/context.zig":
        "efe7f2bd64402ebd3983d025fbaf6301ae2004e6739bf04f753db3d0191142ef",
    "src/frontends/s31/language/finalization/constant_base.zig":
        "354f3e5a25b42d4dec1ded5f721805c2cb69543c4f671d43c4861bfda084a0ca",
}

P = 2**31 - 1


def limbs(key: int) -> tuple[int, int, int, int]:
    return tuple((key >> (32 * i)) & 0xffffffff for i in range(4))


def key_of(a: int, b: int = 0, c: int = 0, d: int = 0) -> int:
    return a | b << 32 | c << 64 | d << 96


class Pending:
    """The Zig AutoArrayHashMap fetchSwapRemove iteration order."""

    def __init__(self, entries: list[tuple[int, int]]):
        self.entries = entries

    def take(self, key: int) -> int | None:
        for i, (candidate, address) in enumerate(self.entries):
            if candidate == key:
                self.entries[i] = self.entries[-1]
                self.entries.pop()
                return address
        return None

    def first(self) -> int:
        return self.entries[0][0]

    def __bool__(self) -> bool:
        return bool(self.entries)


class Replay:
    def __init__(self, graph: dict):
        self.graph = graph
        self.next_fresh = graph["n_vars"]  # virtual; shifted back after replay
        self.expected: dict[str, list[dict]] = {name: [] for name in
                                                ("add", "sub", "mul", "pointwise_mul")}
        keys, vars_ = graph["constant_keys"], graph["constant_vars"]
        entries = [(key, var["idx"]) for key, var in zip(keys, vars_, strict=True)]
        self.m31 = Pending([(limbs(key)[0], var) for key, var in entries
                            if limbs(key)[1:] == (0, 0, 0)])
        self.qm31 = Pending([(key, var) for key, var in entries
                             if limbs(key)[1:] != (0, 0, 0)])
        self.mc: dict[int, int] = {}
        self.qc: dict[int, int] = {}
        self.empty = Pending([])

    def fresh(self) -> int:
        out = self.next_fresh
        self.next_fresh += 1
        return out

    def gate(self, op: str, a: int, b: int, out: int) -> None:
        self.expected[op].append({"in0": a, "in1": b, "out": out})

    def mvar(self, table: Pending, value: int) -> int:
        existing = table.take(value)
        return existing if existing is not None else self.fresh()

    def qvar(self, key: int) -> int:
        existing = self.qm31.take(key)
        return existing if existing is not None else self.fresh()

    def from_base(self, table: Pending, base: int, value: int) -> int:
        if value in self.mc:
            return self.mc[value]
        digits: list[int] = []
        while value:
            digits.append(value % base)
            value //= base
        if not digits:
            raise ValueError("zero missing from finalization cache")
        acc = digits.pop()
        acc_var = self.mc[acc]
        while digits:
            digit = digits.pop()
            digit_var = self.mc[digit]
            product = acc * base % P
            if product not in self.mc:
                out = self.mvar(table, product)
                self.gate("mul", acc_var, self.mc[base], out)
                self.mc[product] = out
            product_var = self.mc[product]
            total = (product + digit) % P
            if total not in self.mc:
                out = self.mvar(table, total)
                self.gate("add", product_var, digit_var, out)
                self.mc[total] = out
            acc, acc_var = total, self.mc[total]
        return self.mc[acc]

    def basis(self, key: int) -> int:
        out = self.qvar(key)
        self.qc[key] = out
        return out

    def cm31(self, base: int, i_var: int, a: int, b: int) -> int:
        a_var = self.from_base(self.empty, base, a)
        b_var = self.from_base(self.empty, base, b)
        if b == 0:
            return a_var
        bi = key_of(0, b)
        if bi not in self.qc:
            out = self.qvar(bi)
            self.gate("mul", i_var, b_var, out)
            self.qc[bi] = out
        result = key_of(a, b)
        if result not in self.qc:
            out = self.qvar(result)
            self.gate("add", a_var, self.qc[bi], out)
            self.qc[result] = out
        return self.qc[result]

    def constants(self) -> None:
        # In the structural M31 fragment the selected minimum radix is 256.
        values = sorted(key for key, _ in self.m31.entries)
        consecutive = 0
        while consecutive < len(values) and values[consecutive] == consecutive:
            consecutive += 1
        base = max(consecutive - 1, 256)
        if self.m31.take(0) != 0 or self.m31.take(1) != 1 or self.qm31.take(key_of(0, 0, 1)) != 2:
            raise ValueError("reserved constant roster differs")
        self.mc.update({0: 0, 1: 1})
        u = 2
        self.qc[key_of(0, 0, 1)] = u
        self.gate("add", 0, 0, 0)
        self.gate("add", 1, 0, 1)
        self.gate("mul", u, 1, u)

        prev = 1
        for value in range(2, base + 1):
            out = self.mvar(self.m31, value)
            self.gate("add", prev, 1, out)
            self.mc[value] = out
            prev = out
        while self.m31:
            self.from_base(self.m31, base, self.m31.first())

        two = self.mc[2]
        i_plus_two = self.basis(key_of(2, 1))
        self.gate("mul", u, u, i_plus_two)
        i_var = self.basis(key_of(0, 1))
        self.gate("sub", i_plus_two, two, i_var)
        i_plus_one = self.basis(key_of(1, 1))
        self.gate("add", i_var, 1, i_plus_one)
        u_plus_iu = self.basis(key_of(0, 0, 1, 1))
        self.gate("mul", i_plus_one, u, u_plus_iu)
        ones = self.basis(key_of(1, 1, 1, 1))
        self.gate("add", i_plus_one, u_plus_iu, ones)

        retained = []
        for key, var in self.qm31.entries:
            a, b, c, d = limbs(key)
            if not (a == b == c == d):
                retained.append((key, var))
                continue
            mvar = self.from_base(self.empty, base, a)
            self.gate("mul", mvar, ones, var)
            self.qc[key] = var
        self.qm31 = Pending(retained)
        while self.qm31:
            key = self.qm31.first()
            a, b, c, d = limbs(key)
            left = self.cm31(base, i_var, a, b)
            if c == d == 0:
                continue
            right = self.cm31(base, i_var, c, d)
            lifted = key_of(0, 0, c, d)
            if lifted not in self.qc:
                out = self.qvar(lifted)
                self.gate("mul", right, u, out)
                self.qc[lifted] = out
            if key not in self.qc:
                out = self.qvar(key)
                self.gate("add", left, self.qc[lifted], out)
                self.qc[key] = out


def check_finalization(graph: dict, raw: dict[str, bytes], inputs: list[dict]) -> dict[str, int]:
    """Compare every finalization arithmetic gate and input self-yield."""
    for path, wanted in PINNED_SOURCES.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != wanted:
            raise ValueError("finalization source changed; review replay: " + path)
    replay = Replay(graph)
    replay.constants()
    generated = replay.next_fresh - graph["n_vars"]
    start_var = graph["n_vars"] - generated
    if start_var <= 2 or any(var["idx"] >= start_var for var in graph["constant_vars"]):
        raise ValueError("constant address created after finalization start")
    for gates in replay.expected.values():
        for gate in gates:
            for field in ("in0", "in1", "out"):
                if gate[field] >= graph["n_vars"]:
                    gate[field] = gate[field] - graph["n_vars"] + start_var

    # Packed private source inputs are their own guess addresses. Public M31
    # scalar guesses are recognized by their self-product constraints, values,
    # and count. They appear in source order among each opcode's gates.
    import json

    public_words: list[int] = []
    input_specs = json.loads(raw["certificate"])["ssa"]["inputs"]
    if len(input_specs) != len(inputs):
        raise ValueError("source input roster differs")
    for item, spec in zip(inputs, input_specs, strict=True):
        if item["name"] != spec["name"] or item["id"] != spec["id"]:
            raise ValueError("source input identity differs")
        if spec["visibility"] == "public":
            public_words.extend(item["words"])
        else:
            source = graph["source_map"][item["id"]]
            packed = graph["node_wires"][source["id"]]["wires"][0]
            replay.gate("add", packed, 0, packed)
    actual_pm = graph["pointwise_mul"]
    public_yields = actual_pm[-len(public_words):] if public_words else []
    if len(public_yields) != len(public_words):
        raise ValueError("public guess yield count differs")
    for word, gate in zip(public_words, public_yields, strict=True):
        if (gate["in0"] != gate["out"] or gate["in1"] != 1 or
                graph["values"][gate["out"]] != [word, 0, 0, 0] or
                gate["out"] in {var["idx"] for var in graph["constant_vars"]}):
            raise ValueError("public M31 guess yield differs")
        replay.expected["pointwise_mul"].append(gate)

    expected_count = sum(map(len, replay.expected.values()))
    span = graph["finalization"]
    if (span["qm31_end"] - span["qm31_start"] != expected_count or
            span["m31_to_u32_start"] != span["m31_to_u32_end"] or
            span["qm31_end"] != sum(len(graph[name]) for name in replay.expected)):
        raise ValueError("finalization row count differs from exact constant and guess roster")
    for name, expected in replay.expected.items():
        actual = graph[name][-len(expected):] if expected else []
        if actual != expected:
            raise ValueError(f"{name} finalization gate order or address differs")
    return {"constant_fresh_vars": generated, "finalization_gates": expected_count}
