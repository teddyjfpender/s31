"""Durable raw trial observations and externally anchored phase integrity.

This detects later evidence mutation. It cannot establish that the pinned
collector, operating system clock, or resource accounting were honest.
"""

from __future__ import annotations

import json
import os
import platform
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

from design import ROOT, canonical, sha
from protocol import ANCHOR, HEX40, HEX64, require_committed

LEDGER_SCHEMA = "s31-paired-record-v2-ledger-entry-v1"
EVENT_SCHEMA = "s31-paired-record-v2-raw-arm-event-v1"
ROOT_SCHEMA = "s31-paired-record-v2-phase-root-v1"
ANCHOR_SCHEMA = "s31-paired-record-v2-phase-anchor-v1"
GENESIS = "0" * 64


def durable_write(path: Path, content: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(content)
        stream.flush()
        os.fsync(stream.fileno())


def fsync_existing(path: Path) -> None:
    with path.open("r+b") as stream:
        os.fsync(stream.fileno())


def _rss(method: str, raw: str) -> int:
    if method == "darwin-time-max-rss-bytes":
        found = re.search(r"^\s*(\d+)\s+maximum resident set size\s*$", raw, re.M)
        if found is None:
            raise ValueError("Darwin time omitted maximum resident set size")
        value = int(found.group(1))
    elif method == "gnu-time-max-rss-kib":
        found = re.fullmatch(r"\s*(\d+)\s*", raw)
        if found is None:
            raise ValueError("GNU time omitted maximum resident set size")
        value = int(found.group(1)) * 1024
    else:
        raise ValueError("paired study requires supported raw /usr/bin/time RSS evidence")
    if value <= 0:
        raise ValueError("nonpositive measured peak RSS")
    return value


def observed_invoke(argv: list[str], directory: Path, label: str) -> dict:
    """Run one native process and durably save the exact measurement evidence."""
    resource_path = directory / f"{label}.resource"
    time_tool = Path("/usr/bin/time")
    system = platform.system()
    if not time_tool.is_file():
        raise ValueError("paired study requires /usr/bin/time")
    if system == "Darwin":
        command = [str(time_tool), "-l", "-o", str(resource_path), *argv]
        method = "darwin-time-max-rss-bytes"
    elif system == "Linux":
        command = [str(time_tool), "-f", "%M", "-o", str(resource_path), *argv]
        method = "gnu-time-max-rss-kib"
    else:
        raise ValueError("paired study requires supported OS process resource accounting")
    start_ns = time.perf_counter_ns()
    result = subprocess.run(command, cwd=ROOT, capture_output=True, check=False)
    end_ns = time.perf_counter_ns()
    if result.returncode != 0:
        raise RuntimeError(f"native {label} failed ({result.returncode}): {argv!r}\n"
                           + result.stdout.decode("utf-8", "replace")
                           + result.stderr.decode("utf-8", "replace"))
    fsync_existing(resource_path)
    raw_resource = resource_path.read_bytes()
    raw_text = raw_resource.decode("utf-8")
    peak = _rss(method, raw_text)
    durable_write(directory / f"{label}.stdout", result.stdout)
    durable_write(directory / f"{label}.stderr", result.stderr)
    durable_write(directory / f"{label}.log", result.stdout + result.stderr)
    return {
        "argv": argv,
        "start_monotonic_ns": start_ns,
        "end_monotonic_ns": end_ns,
        "exit_code": result.returncode,
        "rss_method": method,
        "raw_resource_text": raw_text,
        "raw_resource_sha256": sha(raw_resource),
        "peak_rss_bytes": peak,
        "stdout_sha256": sha(result.stdout),
        "stderr_sha256": sha(result.stderr),
        "log_sha256": sha(result.stdout + result.stderr),
    }


def replay_process(observation: dict, directory: Path, label: str,
                   expected_argv: list[str]) -> tuple[float, int, str]:
    """Derive wall/RSS from pinned raw evidence; reject edited observations."""
    if (set(observation) != {"argv", "start_monotonic_ns", "end_monotonic_ns",
                             "exit_code", "rss_method", "raw_resource_text",
                             "raw_resource_sha256", "peak_rss_bytes",
                             "stdout_sha256", "stderr_sha256", "log_sha256"} or
            observation["argv"] != expected_argv or
            type(observation["start_monotonic_ns"]) is not int or
            type(observation["end_monotonic_ns"]) is not int or
            observation["start_monotonic_ns"] < 0 or
            observation["end_monotonic_ns"] <= observation["start_monotonic_ns"] or
            observation["exit_code"] != 0):
        raise ValueError(f"{label}: raw process identity, clock, or exit changed")
    stdout = (directory / f"{label}.stdout").read_bytes()
    stderr = (directory / f"{label}.stderr").read_bytes()
    log = (directory / f"{label}.log").read_bytes()
    raw_resource = (directory / f"{label}.resource").read_bytes()
    if (sha(stdout) != observation["stdout_sha256"] or
            sha(stderr) != observation["stderr_sha256"] or
            log != stdout + stderr or sha(log) != observation["log_sha256"] or
            sha(raw_resource) != observation["raw_resource_sha256"] or
            raw_resource.decode("utf-8") != observation["raw_resource_text"]):
        raise ValueError(f"{label}: raw process output or RSS evidence changed")
    peak = _rss(observation["rss_method"], observation["raw_resource_text"])
    if peak != observation["peak_rss_bytes"]:
        raise ValueError(f"{label}: parsed RSS differs from raw /usr/bin/time evidence")
    wall = (observation["end_monotonic_ns"] - observation["start_monotonic_ns"]) / 1e9
    return wall, peak, log.decode("utf-8", "replace")


def append_event(path: Path, event: dict, sequence: int, previous: str) -> str:
    if event.get("schema") != EVENT_SCHEMA or not HEX64.fullmatch(previous):
        raise ValueError("invalid raw arm event or previous ledger digest")
    body = {"schema": LEDGER_SCHEMA, "sequence": sequence,
            "previous_sha256": previous, "event": event}
    digest = sha(canonical(body))
    line = canonical({**body, "entry_sha256": digest})
    flags = os.O_WRONLY | os.O_APPEND | os.O_CREAT
    descriptor = os.open(path, flags, 0o600)
    try:
        if os.write(descriptor, line) != len(line):
            raise OSError("short ledger append")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    return digest


def read_ledger(path: Path) -> tuple[list[dict], str]:
    raw = path.read_bytes()
    if not raw or not raw.endswith(b"\n"):
        raise ValueError("paired phase ledger is empty or truncated")
    previous = GENESIS
    events: list[dict] = []
    for sequence, line in enumerate(raw.splitlines(keepends=True)):
        entry = json.loads(line)
        if canonical(entry) != line or set(entry) != {
                "schema", "sequence", "previous_sha256", "event", "entry_sha256"}:
            raise ValueError("noncanonical or incomplete paired phase ledger entry")
        body = {field: entry[field] for field in (
            "schema", "sequence", "previous_sha256", "event")}
        if (entry["schema"] != LEDGER_SCHEMA or
                entry["sequence"] != sequence or
                entry["previous_sha256"] != previous or
                entry["event"].get("schema") != EVENT_SCHEMA or
                entry["entry_sha256"] != sha(canonical(body))):
            raise ValueError("paired phase ledger chain or sequence changed")
        previous = entry["entry_sha256"]
        events.append(entry["event"])
    return events, previous


def phase_root(directory: Path, split: str, protocol_sha256: str,
               protocol_anchor_commit: str, expected_events: int) -> dict:
    events, final = read_ledger(directory / "phase-ledger.ndjson")
    if len(events) != expected_events:
        raise ValueError("paired phase ledger does not cover the frozen roster")
    return {
        "schema": ROOT_SCHEMA,
        "split": split,
        "protocol_sha256": protocol_sha256,
        "protocol_anchor_commit": protocol_anchor_commit,
        "events": len(events),
        "final_chain_sha256": final,
        "ledger_sha256": sha((directory / "phase-ledger.ndjson").read_bytes()),
        "corpus_sha256": sha((directory / "corpus.json").read_bytes()),
    }


def check_phase_anchor(directory: Path, split: str, protocol_sha256: str,
                       protocol_anchor_commit: str, expected_events: int,
                       expected_root_sha256: str, anchor_commit: str) -> list[dict]:
    if not HEX64.fullmatch(expected_root_sha256 or "") or \
            not HEX40.fullmatch(anchor_commit or ""):
        raise ValueError("full externally recorded phase-root SHA and phase anchor commit required")
    anchor_path = ROOT / f"design/s31/measurements/language/paired-record-v2-{split}-phase-anchor.json"
    require_committed(anchor_path, anchor_commit)
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       anchor_commit, "HEAD"], check=False).returncode or \
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            protocol_anchor_commit, anchor_commit], check=False).returncode:
        raise ValueError("phase anchor is not committed after the protocol freeze")
    anchor = json.loads(anchor_path.read_bytes())
    try:
        timestamp = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
        protocol_timestamp = datetime.fromisoformat(
            json.loads(ANCHOR.read_bytes())["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("phase anchor needs a UTC timestamp") from exc
    if (anchor.get("schema") != ANCHOR_SCHEMA or anchor.get("split") != split or
            anchor.get("phase_root_sha256") != expected_root_sha256 or
            anchor.get("protocol_sha256") != protocol_sha256 or
            timestamp.utcoffset() is None or timestamp.utcoffset().total_seconds() != 0 or
            timestamp < protocol_timestamp or
            timestamp > datetime.now(timezone.utc)):
        raise ValueError("phase anchor differs from external UTC timestamp or phase root")
    root_path = directory / "phase-root.json"
    if sha(root_path.read_bytes()) != expected_root_sha256:
        raise ValueError("paired phase root differs from externally recorded digest")
    saved = json.loads(root_path.read_bytes())
    if root_path.read_bytes() != canonical(saved) or \
            saved != phase_root(directory, split, protocol_sha256,
                           protocol_anchor_commit, expected_events):
        raise ValueError("paired phase root differs from chained raw evidence or corpus")
    events, _ = read_ledger(directory / "phase-ledger.ndjson")
    return events
