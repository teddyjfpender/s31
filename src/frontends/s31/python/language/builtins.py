"""Compiler-owned names and source-language resource limits."""

import re

import s31_mathlib as mathlib
from s31_stdlib import INT_TYPES


INT_SOURCE_TYPES = {kind[4:]: kind for kind in INT_TYPES}
INT_BINARY_CALLS = {
    "std::int::add_checked": "int_add_checked",
    "std::int::add_wrapping": "int_add_wrapping",
    "std::int::sub_checked": "int_sub_checked",
    "std::int::sub_wrapping": "int_sub_wrapping",
    "std::int::mul_wrapping": "int_mul_wrapping",
    "std::int::mul_checked": "int_mul_checked",
    "std::int::le": "int_le",
}
INT_COMPARE_CALLS = {"std::int::lt", "std::int::ge", "std::int::gt", "std::int::eq", "std::int::ne"}
INT_CAST_CALLS = {f"std::int::from_limbs_{kind}" for kind in INT_SOURCE_TYPES} | {
    f"std::int::reinterpret_{kind}" for kind in INT_SOURCE_TYPES
}


TOKEN_RE = re.compile(
    r"(?P<space>\s+)|(?P<comment>//[^\n]*)|(?P<field>[0-9]+_m31\b)|"
    r"(?P<number>[0-9]+)|(?P<ident>[A-Za-z_][A-Za-z_0-9]*)|"
    r"(?P<symbol>->|=>|::|\.\*|==|[\[\]{}();,.:<>+\-=*@])"
)
# Binary operator binding power; unary minus binds tighter than all of them.
BINARY_POWER = {"+": 10, "-": 10, ".*": 20}
UNARY_POWER = 30
MAX_TOKENS = 100_000
MAX_NUMBER_DIGITS = 64
MAX_CALL_DEPTH = 32
MAX_EXPRESSION_DEPTH = 128
MAX_TYPE_DEPTH = 32
BUILTINS = {
    "splat", "iterate", "m31_from_u16", "select", "poseidon2_leaf",
    "std::array::get", "std::array::concat", "std::array::take",
    "std::array::drop", "std::array::reshape", "std::array::flatten",
    "poseidon2_pair", "blake2s_leaf", "blake2s_pair",
    "merkle_path_poseidon2", "merkle_path_blake2s",
    "std::bytes::to_u256_le", "std::bytes::from_u256_le", "std::bytes::limbs_m31",
    "sha256d_header", "is_zero",
    "target_mainnet",
    "target_u256", "work_u256", "chainwork_from_work", "chainwork_u256",
    "accumulate_chainwork",
    "block_work",
    "pow_valid",
    "prev_hash", "header_bits", "header_time", "genesis_hash_mainnet", "lt_u32",
} | mathlib.BUILTINS
STANDARD_ALIASES = {
    "std::field::from_u16": "m31_from_u16",
    "std::field::select": "select",
    "std::field::is_zero": "is_zero",
    "std::bool::not": "bool_not",
    "std::bool::and": "bool_and",
    "std::bool::or": "bool_or",
    "std::bool::xor": "bool_xor",
    "std::bool::select": "bool_select",
    "std::hash::poseidon2_leaf": "poseidon2_leaf",
    "std::hash::poseidon2_pair": "poseidon2_pair",
    "std::hash::blake2s_leaf": "blake2s_leaf",
    "std::hash::blake2s_pair": "blake2s_pair",
    "std::hash::sha256d_header": "sha256d_header",
    "std::bitcoin::block_hash": "block_hash",
    "std::bitcoin::hash_bytes": "hash_bytes",
    "std::bitcoin::parent_hash": "parent_hash",
    "std::bitcoin::genesis_block_hash_mainnet": "genesis_block_hash_mainnet",
    "std::bitcoin::target_mainnet": "target_mainnet",
    "std::bitcoin::target_u256": "target_u256",
    "std::bitcoin::work_u256": "work_u256",
    "std::bitcoin::chainwork_from_work": "chainwork_from_work",
    "std::bitcoin::chainwork_u256": "chainwork_u256",
    "std::bitcoin::accumulate_chainwork": "accumulate_chainwork",
    "std::bitcoin::block_work": "block_work",
    "std::bitcoin::pow_valid": "pow_valid",
    "std::bitcoin::prev_hash": "prev_hash",
    "std::bitcoin::header_bits": "header_bits",
    "std::bitcoin::header_time": "header_time",
    "std::math::lt_u32": "lt_u32",
    "std::bitcoin::genesis_hash_mainnet": "genesis_hash_mainnet",
    "std::merkle::path_poseidon2": "merkle_path_poseidon2",
    "std::merkle::path_blake2s": "merkle_path_blake2s",
}
BUILTINS |= STANDARD_ALIASES.keys()
BUILTINS |= INT_BINARY_CALLS.keys() | INT_COMPARE_CALLS | INT_CAST_CALLS | {"std::int::limbs"}
