"""Production PCS mode selected by an independently trusted S31 package key."""

LEGACY = "legacy_postcard"
SEPARATE_SHA_VERIFIERS = frozenset({"sha-joint", "sha-shift", "sha-fused"})


def key_fields_for_lowering(lowering: str) -> dict[str, str]:
    # SHA profiles have separate strict native key parsers; their legacy key
    # bytes remain unchanged until those verifiers acquire a versioned mode.
    return {} if lowering in SEPARATE_SHA_VERIFIERS else {"pcs_mode": LEGACY}


def require_production(key: dict) -> str:
    # Missing means legacy for previously sealed verification keys. A present
    # value must be exact; no artifact or proof supplies a mode selector.
    mode = key.get("pcs_mode", LEGACY)
    if mode != LEGACY:
        raise ValueError("S31 package key selects an unsupported production PCS mode")
    return mode
