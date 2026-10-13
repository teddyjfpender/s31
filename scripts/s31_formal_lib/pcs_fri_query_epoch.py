"""Source-pinned, finite draw-counter audit for the v0.1 raw-query epoch.

This proves a narrow arithmetic fact about the selected native source path:
after absorbing the verified PoW nonce, 70 raw queries consume exactly nine
successive eight-word channel blocks with counters 0 through 8. The pinned
channel now traps before any u32 counter wrap, including during unbounded
pre-query rejection loops. This does not model BLAKE2s as a random oracle.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


ROOT = Path(__file__).resolve().parents[2]
ENGINE = "deps/stwo-zig/src/core"
N_QUERIES = 70
WORDS_PER_HASH = 8
U32_CARDINALITY = 1 << 32
CONFIG_SOURCES = (
    "src/frontends/s31/runtime/mvp_runtime.zig",
    "src/frontends/s31/sha/package/sha_package_runtime.zig",
    "src/frontends/s31/sha/package/sha_shift_package_runtime.zig",
    "src/frontends/s31/sha/package/sha_fused_package_runtime.zig",
)
ENGINE_SOURCES = (
    "pcs/verifier.zig", "fri.zig", "queries.zig",
    "channel/blake2s.zig", "pcs/config_v2.zig", "protocol_revision.zig",
)


def require_once(source: str, anchor: str, label: str) -> None:
    if source.count(anchor) != 1:
        raise ValueError(f"{label}: source anchor changed: {anchor!r}")


def audit_sources(pcs: str, fri: str, queries: str, channel: str,
                  config: str, revision: str,
                  profiles: tuple[str, ...]) -> dict[str, object]:
    if len(profiles) != len(CONFIG_SOURCES):
        raise ValueError("S31 profile source roster changed")
    require_once(channel, "pub const FELTS_PER_HASH: usize = 8;", "channel block width")
    if config.count("n_queries: u32,") != 2:
        raise ValueError("sealed FRI query count source changed")
    require_once(config, ".n_queries = n_queries,", "sealed FRI query count")
    require_once(config, ".n_queries = self.n_queries,", "FRI folding query count")
    require_once(revision, ".proving_5a7c5ed => friLegacyView(config.fri_config),",
                 "S31 protocol revision query bridge")
    require_once(revision, ".fri_config = fri.folding(),",
                 "S31 protocol revision query bridge")
    require_once(pcs, ".config = verifier_revision.legacyView(config),",
                 "native verifier query bridge")
    checked_increment = region(channel, "fn nextDrawCounter(", "pub const Blake2sChannel =")
    require_once(checked_increment,
                 "return std.math.add(u32, current, 1) catch error.DrawCounterExhausted;",
                 "channel checked counter increment")

    reset = region(channel, "pub inline fn updateDigest(", "pub fn mixFelts(")
    require_once(reset, "self.n_draws = 0;", "channel counter reset")
    mix_words = region(channel, "pub fn mixU32s(", "pub fn mixU64(")
    require_once(mix_words, "self.updateDigest(hasher.finalize());", "word absorption reset")
    mix_nonce = region(channel, "pub fn mixU64(", "pub fn drawU32s(")
    require_once(mix_nonce, "self.mixU32s(&[_]u32{", "nonce absorption reset")
    draw = region(channel, "pub fn drawU32s(", "pub fn drawSecureFelt(")
    ordered_once(draw, "u32 query block counter", "const counter = u32ToBytesLe(self.n_draws);",
                 "@memcpy(hash_input[32..36], counter[0..]);",
                 "self.n_draws = nextDrawCounter(self.n_draws) catch @panic(\"BLAKE2s draw counter exhausted\");",
                 "const hash = hashBytes(hash_input[0..]);", "var out: [FELTS_PER_HASH]u32",
                 "return out;")
    if draw.count("self.n_draws") != 3:
        raise ValueError("u32 query block counter gained another mutation or read")
    require_once(draw, "while (i < FELTS_PER_HASH) : (i += 1)", "query block extraction")

    query_loop = region(queries, "pub fn drawQueries(", "pub fn sortedUniquePositions(")
    ordered_once(query_loop, "raw query count", "while (produced < n_queries)",
                 "const words = channel.drawU32s();", "for (words) |word|",
                 "out[produced] =", "produced += 1;",
                 "if (produced == n_queries) break;", "return out;")
    if re.findall(r"channel\.[A-Za-z0-9_]+\(", query_loop) != ["channel.drawU32s("]:
        raise ValueError("raw query loop gained another channel draw or mix")

    pcs_impl = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    require_once(pcs_impl, "self.config.fri_config,\n                proof.fri_proof,",
                 "native FRI query count forwarding")
    require_once(pcs_impl, "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {\n"
                 "                return verifier_types.VerificationError.ProofOfWork;\n"
                 "            }", "verified PoW nonce barrier")
    ordered_once(pcs_impl, "PoW nonce and raw-query epoch",
                 "channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)",
                 "channel.mixU64(proof.proof_of_work);",
                 "fri_verifier.sampleQueryPositionsWithRaw(")
    nonce_end = pcs_impl.index("channel.mixU64(proof.proof_of_work);") + len(
        "channel.mixU64(proof.proof_of_work);")
    query_start = pcs_impl.index("fri_verifier.sampleQueryPositionsWithRaw(")
    if "channel." in pcs_impl[nonce_end:query_start]:
        raise ValueError("unexpected channel operation before raw-query epoch")
    fri_query = region(fri, "pub fn sampleQueryPositionsWithRaw(", "pub fn decommit(")
    ordered_once(fri_query, "FRI configured raw queries", "const raw = try queries_mod.drawQueries(",
                 "self.config.n_queries,", "var new_queries = try queries_mod.Queries.init(")
    if fri_query.count("queries_mod.drawQueries(") != 1:
        raise ValueError("FRI raw-query wrapper gained another sampler")
    if re.findall(r"channel\.[A-Za-z0-9_]+\(", fri_query):
        raise ValueError("FRI raw-query wrapper gained a direct channel operation")

    require_once(profiles[0], "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)",
                 "S31 runtime nominal query count")
    for source in profiles[1:]:
        require_once(source, "FriConfigV2.init(26, 0, 1, 70, 1)",
                     "SHA package nominal query count")

    blocks = (N_QUERIES + WORDS_PER_HASH - 1) // WORDS_PER_HASH
    if not 0 < blocks < U32_CARDINALITY:
        raise ValueError("raw query epoch could wrap the u32 counter")
    return {
        "scope": "verified PoW nonce absorption through v0.1 raw query sampling",
        "raw_queries": N_QUERIES,
        "words_per_hash": WORDS_PER_HASH,
        "hash_draws": blocks,
        "counter_inputs": list(range(blocks)),
        "counter_wrap_in_this_epoch": False,
        "native_blake2s_counter_overflow_fail_closed": True,
        "full_transcript_counter_wrap_proven": False,
        "random_oracle_independence_proven": False,
    }


def audit(root: Path = ROOT) -> dict[str, object]:
    engine = root / ENGINE
    names = tuple(f"{ENGINE}/{path}" for path in ENGINE_SOURCES) + CONFIG_SOURCES
    sources = tuple((root / path).read_text() for path in names)
    report = audit_sources(*sources[:6], sources[6:])
    report["engine_gitlink_commit"] = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True
    ).strip()
    checked_out_engine = subprocess.check_output(
        ["git", "-C", str(engine), "rev-parse", "HEAD"], text=True
    ).strip()
    if checked_out_engine != report["engine_gitlink_commit"]:
        raise ValueError("checked-out native engine differs from pinned gitlink")
    report["source_sha256"] = {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in names
    }
    return report


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
