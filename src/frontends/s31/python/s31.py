#!/usr/bin/env python3
"""S31 v0.1 command-line frontend and stable Python API."""

import sys
from pathlib import Path
S31_SOURCE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

import json

from cli.commands import main
from package.build import build, build_json, build_text, package_for
from package.context import (
    AIR_BUNDLE_SHA256, BUILD_FILE, ENGINE_ROOT, LIBRARY_SOURCE_FILES,
    PINNED_ASSETS, PROJECTION_SHA256, ROOT, S31_DIR, TEXT_FRONTEND_SOURCES,
    abi, compiler_fingerprint, file_hash, invoke, load_source, lower_text,
    sha256, standard_library_lock, text_interface, write_json,
)
from package.verify import verify_package
from runtime.folds import audit_fold_chain, replay_state_step
from runtime.trials import (
    assignment_digest, independent_value_check, oracle_provenance,
    prover_stages, trial, tune, visible_fri,
)


def explain(package: Path) -> dict:
    from inspection.reports import explain as inspect_explain

    return inspect_explain(package, verify_package)


def equations(package: Path) -> dict:
    from inspection.reports import equations as inspect_equations

    return inspect_equations(package, verify_package)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, UnicodeError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        print(f"s31: {exc}", file=sys.stderr)
        raise SystemExit(1)
