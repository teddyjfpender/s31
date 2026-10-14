"""Production PCS mode selected by an independently trusted S31 package key."""

LEGACY = "legacy_postcard"


def require_production(key: dict) -> str:
    # Missing means legacy for previously sealed verification keys. A present
    # value must be exact; no artifact or proof supplies a mode selector.
    mode = key.get("pcs_mode", LEGACY)
    if mode != LEGACY:
        raise ValueError("S31 package key selects an unsupported production PCS mode")
    return mode
