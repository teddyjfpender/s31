"""Pure source type rules for compiler-owned operations.

These rules emit no relation nodes. The specialization backend separately
checks values, constants, constrained-bit provenance and expansion limits.
The acceptance corpus compares both phases on every shipped example.
"""

from __future__ import annotations

from s31_stdlib import INT_TYPES, P, SELECTABLE_KINDS, Type, TypeErrorS31
from language.builtins import INT_BINARY_CALLS, INT_CAST_CALLS, INT_COMPARE_CALLS, INT_STATIC_SHIFT_CALLS
from language.types import FieldLiteral, SourceType, StaticArray
from language.syntax import TupleType


BIT = Type("bit", 1)
M31_ONE = Type("m31", 1)
U256 = Type("uint256", 16)
BYTES32 = Type("bytes32", 16)
BYTES80 = Type("bytes80", 40)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise TypeErrorS31(message)


def arity(name: str, args: tuple[SourceType, ...], expected: int) -> None:
    require(len(args) == expected, f"{name} expects {expected} arguments")


def circuit(value: SourceType) -> Type:
    require(isinstance(value, Type), "expected a circuit value")
    return value


def group(value: SourceType, name: str, *, maximum: int = 64) -> tuple[SourceType, ...]:
    require(isinstance(value, StaticArray), f"{name} requires a static array")
    require(1 <= len(value.elements) <= maximum,
            f"{name} requires 1..{maximum} terms")
    return value.elements


def m31_group(value: SourceType, name: str, *, maximum: int = 64) -> tuple[Type, ...]:
    terms = group(value, name, maximum=maximum)
    require(all(isinstance(term, Type) and term.kind == "m31" for term in terms),
            f"{name} requires a static array of [m31; N] values")
    first = terms[0]
    require(all(term == first for term in terms),
            f"{name} requires equally shaped [m31; N] terms")
    return terms  # type: ignore[return-value]


def matrix(value: SourceType, name: str) -> tuple[tuple[tuple[Type, ...], ...], int]:
    rows = group(value, name, maximum=16)
    typed_rows = tuple(m31_group(row, name, maximum=16) for row in rows)
    width = len(typed_rows[0])
    require(all(len(row) == width and row[0] == typed_rows[0][0] for row in typed_rows),
            f"{name} requires rectangular static rows with equally shaped [m31; N] terms")
    return typed_rows, width


def static_parameter(name: str, generic: int | None, required: bool = False) -> int | None:
    if required:
        require(generic is not None, f"{name} requires a static parameter")
    else:
        require(generic is None, f"{name} does not accept a static parameter")
    return generic


def infer_builtin(name: str, generic: int | None, args: tuple[SourceType, ...],
                  *, step_mode: bool = False) -> SourceType:
    """Return a source type or reject an invalid builtin application."""
    if name == "splat":
        length = static_parameter(name, generic, required=True)
        arity(name, args, 1)
        require(isinstance(args[0], FieldLiteral), "splat<N>(constant_m31) expected")
        return Type("m31", length)
    if name in INT_STATIC_SHIFT_CALLS:
        static_parameter(name, generic, required=True)
        arity(name, args, 1)
        value = circuit(args[0])
        require(value.kind in INT_TYPES, f"{name} requires a fixed-width scalar")
        require(name != "std::int::shr_arithmetic" or INT_TYPES[value.kind][1],
                "arithmetic right shift requires a signed fixed-width scalar")
        return value
    if name in INT_BINARY_CALLS.keys() | INT_COMPARE_CALLS:
        static_parameter(name, generic)
        arity(name, args, 2)
        lhs, rhs = map(circuit, args)
        require(lhs == rhs and lhs.kind in INT_TYPES,
                "std::int requires two equally typed fixed-width integers")
        return BIT if name in INT_COMPARE_CALLS or name == "std::int::le" else lhs
    if name in {"std::int::div_rem", "std::int::div_checked", "std::int::rem_checked"}:
        static_parameter(name, generic)
        arity(name, args, 2)
        lhs, rhs = map(circuit, args)
        require(lhs == rhs and lhs.kind in INT_TYPES,
                "div_rem requires two equally typed fixed-width integers")
        return TupleType((lhs, lhs)) if name == "std::int::div_rem" else lhs
    if name == "std::int::bit_not":
        static_parameter(name, generic)
        arity(name, args, 1)
        value = circuit(args[0])
        require(value.kind in INT_TYPES, "std::int::bit_not requires a fixed-width scalar")
        return value
    if name == "std::int::limbs":
        static_parameter(name, generic)
        arity(name, args, 1)
        value = circuit(args[0])
        require(value.kind in INT_TYPES, "std::int::limbs requires a fixed-width scalar")
        return Type("u16", value.length)
    if name in INT_CAST_CALLS:
        static_parameter(name, generic)
        arity(name, args, 1)
        source = circuit(args[0])
        suffix = name.rsplit("_", 1)[-1]
        target = Type(f"int_{suffix}", max(1, INT_TYPES[f"int_{suffix}"][0] // 16))
        if "from_limbs_" in name:
            require(source == Type("u16", target.length),
                    f"from_limbs_{suffix} requires [u16; {target.length}]")
        elif "cast_checked_" in name:
            require(source.kind in INT_TYPES,
                    "checked integer cast requires a fixed-width scalar")
        else:
            require(source.kind in INT_TYPES and source.length == target.length and
                    INT_TYPES[source.kind][0] == INT_TYPES[target.kind][0],
                    "integer reinterpret requires equal-width integer types")
        return target

    if name in {"std::array::get", "std::array::take", "std::array::drop", "std::array::reshape"}:
        count = static_parameter(name, generic, required=True)
        arity(name, args, 1)
        value = args[0]
        if name == "std::array::get":
            if isinstance(value, StaticArray):
                require(0 <= count < len(value.elements), "std::array::get index is outside the static array")
                return value.elements[count]
            typ = circuit(value)
            require(typ.kind in {"m31", "u16"} and 0 <= count < typ.length,
                    "std::array::get index is outside the runtime array")
            return Type(typ.kind, 1)
        if name == "std::array::reshape":
            if isinstance(value, StaticArray):
                terms = value.elements
                require(all(isinstance(term, Type) for term in terms),
                        "std::array::reshape requires a flat static array of values")
                require(all(isinstance(term, Type) for term in terms) and
                        1 <= count <= 16 and len(terms) % count == 0 and
                        1 <= len(terms) // count <= 16,
                        "std::array::reshape requires 1..16 rows and columns with exact divisibility")
                width = len(terms) // count
                return StaticArray(tuple(StaticArray(terms[i:i + width])
                                         for i in range(0, len(terms), width)))
            typ = circuit(value)
            require(typ.kind in {"m31", "u16"} and 1 <= count <= 16 and typ.length % count == 0,
                    "std::array::reshape requires 1..16 rows with exact divisibility")
            return StaticArray(tuple(Type(typ.kind, typ.length // count) for _ in range(count)))
        length = len(value.elements) if isinstance(value, StaticArray) else circuit(value).length
        valid = 1 <= count <= length if name.endswith("take") else 0 <= count < length
        require(valid, f"{name} count must leave 1..N elements")
        if isinstance(value, StaticArray):
            return StaticArray(value.elements[:count] if name.endswith("take") else value.elements[count:])
        typ = circuit(value)
        require(typ.kind in {"m31", "u16"}, "runtime slicing requires [m31; N] or [u16; N]")
        return Type(typ.kind, count if name.endswith("take") else typ.length - count)
    if name == "std::array::concat":
        static_parameter(name, generic)
        arity(name, args, 2)
        lhs, rhs = args
        if isinstance(lhs, StaticArray) and isinstance(rhs, StaticArray):
            require(len(lhs.elements) + len(rhs.elements) <= 64,
                    "std::array::concat static result exceeds 64 terms")
            return StaticArray(lhs.elements + rhs.elements)
        left, right = circuit(lhs), circuit(rhs)
        require(left.kind == right.kind and left.kind in {"m31", "u16"},
                "std::array::concat requires arrays with the same m31 or u16 element type")
        return Type(left.kind, left.length + right.length)
    if name == "std::array::flatten":
        static_parameter(name, generic)
        arity(name, args, 1)
        rows = group(args[0], name, maximum=16)
        if all(isinstance(row, Type) for row in rows):
            first = circuit(rows[0])
            require(first.kind in {"m31", "u16"} and all(row == first for row in rows),
                    "std::array::flatten requires equal runtime row shapes")
            return Type(first.kind, first.length * len(rows))
        require(all(isinstance(row, StaticArray) for row in rows),
                "std::array::flatten requires rectangular static rows of values")
        width = len(rows[0].elements)
        require(1 <= width <= 16 and all(len(row.elements) == width and
                all(isinstance(item, Type) for item in row.elements) for row in rows),
                "std::array::flatten requires rectangular static rows of values")
        return StaticArray(tuple(item for row in rows for item in row.elements))

    if name in {"std::math::neg", "std::math::square", "std::math::inv", "std::math::pow",
                "std::math::sum_lanes", "std::math::mix4"}:
        exponent = static_parameter(name, generic, required=name == "std::math::pow")
        arity(name, args, 1)
        value = circuit(args[0])
        require(value.kind == "m31", "std::math requires [m31; N] values")
        if name == "std::math::pow":
            require(0 <= exponent < P, "std::math::pow exponent must be a static integer in 0..p-1")
        if name == "std::math::mix4":
            require(step_mode and value == Type("m31", 4),
                    "std::math::mix4 requires an [m31; 4] iterate state")
        return M31_ONE if name == "std::math::sum_lanes" else value
    if name in {"std::math::sub", "std::math::div", "std::math::dot_lanes"}:
        static_parameter(name, generic)
        arity(name, args, 2)
        lhs, rhs = map(circuit, args)
        require(lhs.kind == "m31" and lhs == rhs,
                f"{name} requires equally shaped [m31; N] values")
        return M31_ONE if name == "std::math::dot_lanes" else lhs
    if name in {"std::math::sum", "std::math::sum_u256", "std::math::sum_u256_checked"}:
        static_parameter(name, generic)
        arity(name, args, 1)
        if name == "std::math::sum":
            return m31_group(args[0], name)[0]
        terms = group(args[0], name, maximum=16)
        require(all(term == U256 for term in terms),
                f"{name} requires 1..16 static UInt256 values")
        return U256
    if name in {"std::math::dot", "std::math::poly_eval"}:
        static_parameter(name, generic)
        arity(name, args, 2)
        if name == "std::math::poly_eval":
            value = circuit(args[0])
            terms = m31_group(args[1], name)
            require(value == terms[0], "std::math::poly_eval coefficients must match x's [m31; N] shape")
            return value
        lhs, rhs = m31_group(args[0], name), m31_group(args[1], name)
        require(len(lhs) == len(rhs) and lhs[0] == rhs[0],
                "std::math::dot requires equal static array lengths and shapes")
        return lhs[0]
    if name == "std::math::matvec":
        static_parameter(name, generic)
        arity(name, args, 2)
        rows, width = matrix(args[0], name)
        vector = m31_group(args[1], name, maximum=16)
        require(width == len(vector) and rows[0][0] == vector[0],
                "std::math::matvec requires rectangular rows matching the vector")
        return StaticArray(tuple(vector[0] for _ in rows))
    if name == "std::math::matmul":
        static_parameter(name, generic)
        arity(name, args, 2)
        lhs, inner = matrix(args[0], name)
        rhs, columns = matrix(args[1], name)
        require(inner == len(rhs) and lhs[0][0] == rhs[0][0],
                "std::math::matmul inner matrix dimensions must agree")
        return StaticArray(tuple(StaticArray(tuple(lhs[0][0] for _ in range(columns))) for _ in lhs))

    u256_arith = {"std::math::add_u256", "std::math::add_u256_checked",
                  "std::math::sub_u256", "std::math::sub_u256_checked",
                  "std::math::min_u256", "std::math::max_u256"}
    u256_compare = {"std::math::le_u256", "std::math::lt_u256", "std::math::gt_u256",
                    "std::math::ge_u256", "std::math::eq_u256", "std::math::ne_u256"}
    if name in u256_arith | u256_compare:
        static_parameter(name, generic)
        arity(name, args, 2)
        require(args == (U256, U256), f"{name} requires two UInt256 values")
        return BIT if name in u256_compare else U256

    simple = {
        "m31_from_u16": (("u16",), lambda x: Type("m31", x.length)),
        "std::bytes::to_u256_le": (("bytes32",), lambda _: U256),
        "std::bytes::from_u256_le": (("uint256",), lambda _: BYTES32),
        "std::bytes::limbs_m31": (("uint256", "bytes32"), lambda x: Type("m31", x.length)),
        "sha256d_header": (("bytes80",), lambda _: BYTES32),
        "block_hash": (("bytes80",), lambda _: Type("blockhash", 16)),
        "hash_bytes": (("blockhash",), lambda _: BYTES32),
        "parent_hash": (("bytes80",), lambda _: Type("blockhash", 16)),
        "target_mainnet": (("bytes80",), lambda _: Type("target", 16)),
        "target_u256": (("target",), lambda _: U256),
        "work_u256": (("work",), lambda _: U256),
        "chainwork_u256": (("chainwork",), lambda _: U256),
        "chainwork_from_work": (("work",), lambda _: Type("chainwork", 16)),
        "block_work": (("target",), lambda _: Type("work", 16)),
        "pow_valid": (("bytes80",), lambda _: BIT),
        "prev_hash": (("bytes80",), lambda _: BYTES32),
        "header_bits": (("bytes80",), lambda _: Type("u16", 2)),
        "header_time": (("bytes80",), lambda _: Type("u16", 2)),
        "is_zero": (("m31",), lambda _: BIT),
        "bool_not": (("bit",), lambda _: BIT),
    }
    if name in simple:
        static_parameter(name, generic)
        arity(name, args, 1)
        source = circuit(args[0])
        allowed, result = simple[name]
        messages = {
            "m31_from_u16": "m31_from_u16 requires a [u16; N] value; use std::bytes::limbs_m31 for wide values",
            "std::bytes::limbs_m31": "limbs_m31 requires UInt256 or Bytes32",
            "sha256d_header": "sha256d_header requires a serialized Bytes80 header",
            "block_hash": "sha256d_header requires a serialized Bytes80 header",
            "parent_hash": "prev_hash requires a serialized Bytes80 header",
            "target_mainnet": "target_mainnet requires a serialized Bytes80 header",
            "block_work": "block_work requires a Target",
            "pow_valid": "pow_valid requires a serialized Bytes80 header",
            "prev_hash": "prev_hash requires a serialized Bytes80 header",
            "header_bits": "header_bits requires a serialized Bytes80 header",
            "header_time": "header_time requires a serialized Bytes80 header",
            "bool_not": "Boolean operation requires a constrained bit",
        }
        nominal_views = {
            "target_u256": ("target", "uint256"),
            "work_u256": ("work", "uint256"),
            "chainwork_u256": ("chainwork", "uint256"),
            "chainwork_from_work": ("work", "chainwork"),
        }
        if name in nominal_views:
            old, new = nominal_views[name]
            messages[name] = f"{old} to {new} conversion requires a {old} value"
        require(source.kind in allowed,
                messages.get(name, f"{name} requires {', '.join(allowed)}"))
        if name == "is_zero":
            require(source == M31_ONE, "is_zero requires one [m31; 1] value")
        return result(source)
    if name in {"poseidon2_leaf", "blake2s_leaf"}:
        static_parameter(name, generic)
        arity(name, args, 1)
        value = circuit(args[0])
        require(value.kind == "m31" and value.length in {4, 8, 12, 16},
                "hash leaf requires 4, 8, 12, or 16 m31 words")
        return Type("digest", 8, "poseidon2" if name.startswith("poseidon2") else "blake2s_reduced")
    if name in {"poseidon2_pair", "blake2s_pair"}:
        static_parameter(name, generic)
        arity(name, args, 2)
        expected = Type("digest", 8, "poseidon2" if name.startswith("poseidon2") else "blake2s_reduced")
        require(args == (expected, expected), "hash pair requires two digests of the same family")
        return expected
    if name in {"genesis_hash_mainnet", "genesis_block_hash_mainnet"}:
        static_parameter(name, generic)
        arity(name, args, 0)
        return BYTES32 if name == "genesis_hash_mainnet" else Type("blockhash", 16)
    if name == "accumulate_chainwork":
        static_parameter(name, generic)
        arity(name, args, 2)
        require(args == (Type("chainwork", 16), Type("work", 16)),
                "accumulate_chainwork requires ChainWork and Work")
        return Type("chainwork", 16)
    if name == "lt_u32":
        static_parameter(name, generic)
        arity(name, args, 2)
        require(args == (Type("u16", 2), Type("u16", 2)),
                "lt_u32 requires two little-endian [u16; 2] values")
        return M31_ONE
    if name == "select":
        static_parameter(name, generic)
        arity(name, args, 3)
        selector, lhs, rhs = args
        require(selector == BIT, "select requires a bit selector")
        require(lhs == rhs and isinstance(lhs, Type) and lhs.kind in SELECTABLE_KINDS,
                "select requires a bit and two equally typed circuit values")
        return lhs
    if name in {"bool_and", "bool_or", "bool_xor", "bool_select"}:
        static_parameter(name, generic)
        arity(name, args, 3 if name == "bool_select" else 2)
        require(all(arg == BIT for arg in args), f"{name} requires bit values")
        return BIT
    if name in {"merkle_path_poseidon2", "merkle_path_blake2s"}:
        static_parameter(name, generic)
        arity(name, args, 3)
        family = "poseidon2" if name.endswith("poseidon2") else "blake2s_reduced"
        digest = Type("digest", 8, family)
        leaf, siblings, directions = args
        sibling_terms = group(siblings, name, maximum=16)
        direction_terms = group(directions, name, maximum=16)
        require(len(sibling_terms) == len(direction_terms) and all(term == digest for term in sibling_terms)
                and all(term == BIT for term in direction_terms),
                "merkle_path requires equal static arrays of same-family digests and bits")
        require(leaf == digest or isinstance(leaf, Type) and leaf.kind == "m31" and
                leaf.length in {4, 8, 12, 16}, "merkle_path leaf has the wrong hash family")
        return digest
    raise TypeErrorS31(f"unknown builtin or wrong arity: {name}")
