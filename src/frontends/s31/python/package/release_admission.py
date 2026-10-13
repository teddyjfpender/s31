"""Strict admission of the currently checked direct-gate text fragment.

This is an opt-in release boundary. General S31 packages remain buildable, but
they cannot pass this gate unless the independent source-to-relation checker
accepts them. Callers must supply authentic digests from outside the package
and use the yielded snapshot for all subsequent native proof verification.

The certificate and native preflight do not prove Gate AIR, PCS/FRI, or the
installed verifier implementation sound. The certificate records those
assumptions explicitly; this module must not be described as a full proof of
compiler correspondence.
"""

from __future__ import annotations

import json
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

from package.context import invoke
from package.correspondence import OPTIMIZED_SCHEMA, check_optimized_package, check_package
from package.trust import admitted_snapshot


@contextmanager
def bounded_direct_gate_snapshot(
    package: Path, pins: dict[str, str],
) -> Iterator[tuple[Path, dict, dict]]:
    """Yield a pinned, certified package snapshot and its checked certificate.

    The required external pins cover the relation, key, prover, verifier and
    original text source. The package must use the v2 direct-gate key and
    rooted topology, and the native verifier must reconstruct its sealed key.
    An explicit v3 source marker selects the optimized independent checker.
    Unsupported source syntax fails closed here without restricting the
    ordinary S31 builder or verifier APIs.
    """
    with admitted_snapshot(package, pins) as (snapshot, manifest):
        if (manifest.get("lowering") != "direct-gate" or
                type(manifest.get("text_frontend_version")) is not int or
                manifest["text_frontend_version"] != 1 or
                "source_text_sha256" not in manifest):
            raise ValueError("bounded release admission requires a direct-gate text package")
        artifacts = manifest.get("artifacts")
        if (not isinstance(artifacts, dict) or
                not {"correspondence-certificate.json", "gate-topology.json"}.issubset(artifacts)):
            raise ValueError("bounded release admission requires a correspondence certificate")
        key = json.loads((snapshot / "verification-key.json").read_text())
        if key.get("schema") != "s31-verification-key-direct-manifest-v2":
            raise ValueError("bounded release admission requires a v2 direct-gate key")
        certificate = (check_optimized_package(snapshot)
                       if manifest.get("correspondence_schema") == OPTIMIZED_SCHEMA
                       else check_package(snapshot))
        status = certificate.get("status")
        if (not isinstance(status, dict) or
                status.get("source_to_normalized") != "source-to-normalized-checked" or
                status.get("native_gate_emission") != "native-gate-topology-and-selectors-checked" or
                status.get("native_root_binding") != "native-reported-fixed-root-matches-key" or
                status.get("admission") != "python-package-only"):
            raise ValueError("bounded release admission requires a rooted correspondence certificate")
        verifier = snapshot / "bin" / f"s31-{manifest['name']}-native-verifier"
        invoke(str(verifier), "check-key", str(snapshot / "verification-key.json"))
        yield snapshot, manifest, certificate
