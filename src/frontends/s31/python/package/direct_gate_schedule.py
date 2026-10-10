"""Independent exact gate schedule for the bounded four-lane direct profile.

Only add/mul source lets are admitted. They request no constants, so the
builder's constant set is fixed: 0, 1, u, i, iu, and the inverses of i, u,
and iu. This module computes the resulting base-256 derivation and padding
without invoking the Zig compiler or reading its exported gate lists.
"""

from __future__ import annotations

from dataclasses import dataclass, field

P = 2**31 - 1
Q = tuple[int, int, int, int]
ZERO: Q = (0, 0, 0, 0)
ONE: Q = (1, 0, 0, 0)
U: Q = (0, 0, 1, 0)
I: Q = (0, 1, 0, 0)
IU: Q = (0, 0, 0, 1)
INV5 = pow(5, P - 2, P)
INV_I: Q = (0, P - 1, 0, 0)
INV_U: Q = (0, 0, 2 * INV5 % P, -INV5 % P)
INV_IU: Q = (0, 0, -INV5 % P, -2 * INV5 % P)


def gate(left: int, right: int, output: int) -> dict[str, int]:
    return {"in0": left, "in1": right, "out": output}


@dataclass
class _Constants:
    next_address: int
    pending: list[tuple[Q, int]]
    adds: list[dict[str, int]] = field(default_factory=list)
    subs: list[dict[str, int]] = field(default_factory=list)
    muls: list[dict[str, int]] = field(default_factory=list)
    m31: dict[int, int] = field(default_factory=lambda: {0: 0, 1: 1})
    qm31: dict[Q, int] = field(default_factory=dict)

    def fresh(self) -> int:
        address = self.next_address
        self.next_address += 1
        return address

    def qm_var(self, value: Q) -> int:
        # The original constant table removes by swapping its final entry
        # into the removed slot. We model that order explicitly because it
        # determines which pending constant is derived next.
        for index, (pending_value, address) in enumerate(self.pending):
            if pending_value == value:
                self.pending[index] = self.pending[-1]
                self.pending.pop()
                return address
        return self.fresh()

    def m31_var(self, value: int) -> int:
        if value in self.m31:
            return self.m31[value]
        limbs: list[int] = []
        remaining = value
        while remaining:
            limbs.append(remaining % 256)
            remaining //= 256
        acc = limbs.pop()
        acc_var = self.m31[acc]
        while limbs:
            limb = limbs.pop()
            product = acc * 256 % P
            product_var = self.m31.get(product)
            if product_var is None:
                product_var = self.fresh()
                self.muls.append(gate(acc_var, self.m31[256], product_var))
                self.m31[product] = product_var
            total = (product + limb) % P
            total_var = self.m31.get(total)
            if total_var is None:
                total_var = self.fresh()
                self.adds.append(gate(product_var, self.m31[limb], total_var))
                self.m31[total] = total_var
            acc, acc_var = total, total_var
        return self.m31[value]

    def cm31_var(self, a: int, b: int, i_var: int) -> int:
        a_var, b_var = self.m31_var(a), self.m31_var(b)
        if b == 0:
            return a_var
        bi: Q = (0, b, 0, 0)
        bi_var = self.qm31.get(bi)
        if bi_var is None:
            bi_var = self.qm_var(bi)
            self.muls.append(gate(i_var, b_var, bi_var))
            self.qm31[bi] = bi_var
        combined: Q = (a, b, 0, 0)
        combined_var = self.qm31.get(combined)
        if combined_var is None:
            combined_var = self.qm_var(combined)
            self.adds.append(gate(a_var, bi_var, combined_var))
            self.qm31[combined] = combined_var
        return combined_var

    def derive(self) -> None:
        self.adds.extend((gate(0, 0, 0), gate(1, 0, 1)))
        self.muls.append(gate(2, 1, 2))
        self.qm31[U] = self.qm_var(U)
        prev = 1
        for value in range(2, 257):
            address = self.fresh()
            self.adds.append(gate(prev, 1, address))
            self.m31[value] = address
            prev = address

        i_plus_two: Q = (2, 1, 0, 0)
        i_plus_two_var = self.qm_var(i_plus_two)
        self.qm31[i_plus_two] = i_plus_two_var
        self.muls.append(gate(2, 2, i_plus_two_var))
        i_var = self.qm_var(I)
        self.qm31[I] = i_var
        self.subs.append(gate(i_plus_two_var, self.m31[2], i_var))
        i_plus_one: Q = (1, 1, 0, 0)
        i_plus_one_var = self.qm_var(i_plus_one)
        self.qm31[i_plus_one] = i_plus_one_var
        self.adds.append(gate(i_var, 1, i_plus_one_var))
        u_plus_iu: Q = (0, 0, 1, 1)
        u_plus_iu_var = self.qm_var(u_plus_iu)
        self.qm31[u_plus_iu] = u_plus_iu_var
        self.muls.append(gate(i_plus_one_var, 2, u_plus_iu_var))
        ones: Q = (1, 1, 1, 1)
        ones_var = self.qm_var(ones)
        self.qm31[ones] = ones_var
        self.adds.append(gate(i_plus_one_var, u_plus_iu_var, ones_var))

        while self.pending:
            value = self.pending[0][0]
            a, b, c, d = value
            first = self.cm31_var(a, b, i_var)
            if c == 0 and d == 0:
                continue
            second = self.cm31_var(c, d, i_var)
            upper: Q = (0, 0, c, d)
            upper_var = self.qm31.get(upper)
            if upper_var is None:
                upper_var = self.qm_var(upper)
                self.muls.append(gate(second, 2, upper_var))
                self.qm31[upper] = upper_var
            if value not in self.qm31:
                result_var = self.qm_var(value)
                self.adds.append(gate(first, upper_var, result_var))
                self.qm31[value] = result_var


def constant_and_padding(n_nodes: int) -> tuple[dict[str, list[dict[str, int]]], int, int]:
    """Return exact constant gates, padding, final variable count and rows."""
    if not 1 <= n_nodes <= 16:
        raise ValueError("outside bounded direct-gate schedule")
    model = _Constants(
        next_address=33 + n_nodes,
        pending=[(U, 2), (I, 15), (IU, 16),
                 (INV_I, 25 + n_nodes), (INV_U, 28 + n_nodes),
                 (INV_IU, 31 + n_nodes)],
    )
    model.derive()
    constant_rows = len(model.adds) + len(model.subs) + len(model.muls)
    # 6 pack + n source + 4 masks + 3 inverse products + 8 ABI copies +
    # 4 guessed-M31 self-products, then fixed constant derivation.
    raw_rows = 25 + n_nodes + constant_rows
    padded_rows = max(16, 1 << (raw_rows - 1).bit_length())
    for _ in range(padded_rows - raw_rows):
        model.adds.append(gate(1, 1, model.fresh()))
    return {"add": model.adds, "sub": model.subs, "mul": model.muls}, model.next_address, padded_rows
