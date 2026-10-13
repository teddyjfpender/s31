"""Lightweight diagnostics: imports here must not require engine assets."""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
ROOT = S31.parents[2]
ZIG_VERSION = "0.15.2"
SOURCE = """circuit doctor_smoke(private x: [m31; 1]) -> public [m31; 1] {
    let result = x + splat<1>(7_m31);
    result
}
"""
ASSIGNMENT = {"public_inputs": {}, "private_inputs": {"x": [3]},
              "public_outputs": {"result": [10]}}


def positive_seconds(value):
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("timeout must be a positive integer")
    return parsed


def add_arguments(parser):
    parser.add_argument("--native", action="store_true", help="build, prove, verify, and reject a changed claim")
    parser.add_argument("--json", action="store_true", help="emit a structured report only")
    parser.add_argument("--timeout", type=positive_seconds, default=300,
                        help="timeout per identity or native subprocess in seconds (default: 300)")
    parser.add_argument("--keep-artifacts", action="store_true", help="retain native temporary files and print their path")


def run(command, cwd, timeout):
    """Bound command duration and display; never retry a proof operation."""
    with subprocess.Popen(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, errors="replace", start_new_session=os.name == "posix") as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except BaseException as exc:
            try:
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
            except ProcessLookupError:
                pass
            try:
                process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                # A detached descendant may still hold a pipe open.
                process.stdout.close()
                process.stderr.close()
                process.wait(timeout=5)
            if isinstance(exc, subprocess.TimeoutExpired):
                raise RuntimeError(f"Command timed out after {timeout}s: {command}") from exc
            raise
        code = process.returncode
    output = (stdout + stderr).strip()
    if len(output) > 8000:
        output = output[:4000] + "\n[output truncated]\n" + output[-4000:]
    return code, output


def require(command, cwd, timeout):
    code, output = run(command, cwd, timeout)
    if code:
        raise RuntimeError(f"Command failed ({code}): {command}\n{output}")
    return output


def diagnose(root=ROOT, s31=S31, native=False, timeout=300, keep_artifacts=False):
    root, s31 = Path(root), Path(s31)
    checks = []
    report = {"schema": "s31-doctor-v1", "native_requested": native, "checks": checks,
              "native_artifacts": None}

    def check(identifier, action, remediation, depends=(), warning=False):
        started = time.monotonic()
        row = {"id": identifier, "status": "skip", "detail": "", "remediation": None}
        checks.append(row)
        blocked = [name for name in depends
                   if not any(item["id"] == name and item["status"] == "pass" for item in checks)]
        if blocked:
            row["detail"] = "Requires passing checks: " + ", ".join(blocked)
        else:
            try:
                row["detail"] = action()
                row["status"] = "pass"
            except (OSError, ValueError, RuntimeError, ImportError) as exc:
                row.update(status="warn" if warning else "fail", detail=str(exc), remediation=remediation)
        row["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return row["status"] == "pass"

    quick = min(timeout, 15)
    python = [sys.executable, "-B", "-c"]

    def child(code, limit=quick):
        return require([*python, "import sys; sys.path.insert(0, " + repr(str(s31 / "python")) + "); " + code], root, limit)

    def layout():
        paths = [s31 / name for name in ("build.zig", "build.zig.zon", "python/s31.py", "python/text_frontend.py")]
        paths += [root / "deps/stwo-zig" / name for name in
                  ("src", "src/integrations/circuit_cpu/build.zig", "vectors/circuit/official/compiled_air_constraints_v1.bin",
                   "vectors/circuit/official/circuit_air.air_programs_v1.bin")]
        missing = [str(path.relative_to(root)) for path in paths if not path.exists()]
        if missing:
            raise RuntimeError("Missing required paths: " + ", ".join(missing))
        return "Required compiler and engine paths exist"

    check("python", lambda: f"Python {platform.python_version()}: {sys.executable}",
          "Use a Python runtime capable of importing the current frontend; no supported version range is declared.")
    check("source-layout", layout, "For a Git clone, run git submodule update --init --recursive; for an archive, extract the complete source-with-engine bundle.")

    def identity():
        engine = root / "deps/stwo-zig"
        if (engine / ".git").exists():
            modified = require(["git", "-C", str(engine), "status", "--porcelain", "--untracked-files=no"], root, quick)
            if modified:
                raise RuntimeError("Tracked engine modifications:\n" + modified)
        # The helper checks tracked engine changes and hashes portable bundles.
        commit = child("from package.source_identity import pinned_engine_commit; from pathlib import Path; "
                       f"print(pinned_engine_commit(Path({str(root)!r}), Path({str(root / 'deps/stwo-zig')!r})))", timeout)
        if (root / ".git").exists():
            tree = require(["git", "-C", str(root), "ls-tree", "HEAD", "deps/stwo-zig"], root, quick).split()
            if len(tree) < 3 or tree[0] != "160000":
                raise RuntimeError("HEAD has no engine submodule pin")
            if commit != tree[2]:
                raise RuntimeError(f"Engine is {commit}; HEAD pins {tree[2]}")
        return "Engine identity validated: " + commit

    check("engine-identity", identity, "Inspect engine changes and the committed pin; preserve local work before restoring the pinned checkout. Archives must match SOURCE-BUNDLE.json.", ("source-layout",))

    def zig():
        executable = shutil.which("zig")
        if not executable:
            raise RuntimeError("zig was not found on PATH")
        version = require([executable, "version"], root, quick)
        if version != ZIG_VERSION:
            raise RuntimeError(f"Expected Zig {ZIG_VERSION}, found {version}; executable: {executable}")
        return f"Zig {version}: {executable}"

    check("zig", zig, "Put Zig 0.15.2 on PATH, then rerun doctor.")

    def sdk():
        developer = require(["xcode-select", "-p"], root, quick)
        path = require(["xcrun", "--sdk", "macosx", "--show-sdk-path"], root, quick)
        if not Path(path).is_dir():
            raise RuntimeError("Selected SDK directory is missing: " + path)
        return f"Developer directory: {developer}; SDK: {path}; machine: {platform.machine()}. Native smoke determines link compatibility."

    if platform.system() == "Darwin":
        check("platform-sdk", sdk, "Inspect xcode-select and xcrun SDK selection; use developer tools compatible with Zig 0.15.2.", warning=True)
    else:
        check("platform-sdk", lambda: f"{platform.system()} / {platform.machine()}; native smoke checks build capability", "Inspect native toolchain dependencies.")

    check("frontend-oracle", lambda: child("from text_frontend import compile_text; from oracle import evaluate_relation; "
          f"relation, _ = compile_text({SOURCE!r}); "
          f"computed = evaluate_relation(relation, {ASSIGNMENT!r}); "
          "\nif computed != {'result': [10]}: raise RuntimeError('Oracle smoke produced an unexpected result')"
          "\nprint('Frontend and independent oracle agree: 3 + 7 = 10')"),
          "Inspect the frontend/oracle diagnostic and restore missing source or engine assets.", ("source-layout",))
    check("compiler-identity", lambda: child("from package.context import compiler_fingerprint; print('Compiler fingerprint: ' + compiler_fingerprint())", timeout),
          "Check source-bundle identity and compiler assets using the supported Zig version.", ("engine-identity", "zig", "frontend-oracle"))

    def measurement():
        tool = Path("/usr/bin/time")
        system = platform.system()
        if not tool.is_file() or system not in ("Darwin", "Linux"):
            raise RuntimeError("Peak RSS measurement is unavailable on this host")
        options = ["-l"] if system == "Darwin" else ["-f", "%M"]
        require([str(tool), *options, sys.executable, "-B", "-c", "pass"], root, quick)
        return "Resource measurement wrapper runs successfully (optional)"

    check("resource-measurement", measurement, "Proof checks do not require RSS measurement; profiling tools may need additional host permissions.", warning=True)

    if native:
        directory = None

        def build():
            nonlocal directory
            directory = Path(tempfile.mkdtemp(prefix="s31-doctor-"))
            if keep_artifacts:
                report["native_artifacts"] = str(directory)
            (directory / "smoke.s31").write_text(SOURCE)
            (directory / "assignment.json").write_text(json.dumps(ASSIGNMENT))
            require([sys.executable, "-B", str(s31 / "python/s31.py"), "build", str(directory / "smoke.s31"),
                     "--lowering", "direct-gate", "--out", str(directory / "package")], root, timeout)
            return "Built source-bound direct-gate package"

        dependencies = ("compiler-identity",)
        try:
            check("native-build", build, "Inspect the linker/compiler error and SDK selection. Doctor does not install or patch toolchains.", dependencies)

            def prove():
                require([str(directory / "package/bin/s31-doctor_smoke-prover"), "prove",
                         str(directory / "assignment.json"), str(directory / "proof.bin")], root, timeout)
                return "Created an honest proof"

            check("native-prove", prove, "Inspect the prover diagnostic.", ("native-build",))

            def verify(changed=False):
                statement = {"public_inputs": {}, "public_outputs": {"result": [11 if changed else 10]}}
                path = directory / ("changed-statement.json" if changed else "statement.json")
                path.write_text(json.dumps(statement))
                command = [str(directory / "package/bin/s31-doctor_smoke-native-verifier"), str(directory / "proof.bin"),
                           str(path), str(directory / "package/verification-key.json")]
                if changed:
                    code, output = run(command, root, timeout)
                    # This fixture changes only a canonical public field word.
                    # Recognize its transcript/public-binding failures, not I/O,
                    # allocation errors, arbitrary exit codes, or crashes.
                    errors = re.findall(r"^error: (\w+)\s*$", output, re.M)
                    expected = {"InvalidInteractionNonce", "InvalidLookupSum", "InvalidPublicStatement"}
                    if code != 1 or len(errors) != 1 or errors[0] not in expected:
                        raise RuntimeError(f"Changed-claim check did not report a recognized statement rejection ({code}): {output}")
                    return "Verifier rejected changed public result (10 -> 11)"
                require(command, root, timeout)
                return "Native verifier accepted the honest proof"

            check("native-verify", verify, "Inspect verifier and package diagnostics.", ("native-prove",))
            check("native-changed-claim", lambda: verify(True), "Inspect public-statement binding and verifier diagnostics.", ("native-verify",))
        finally:
            if directory and not keep_artifacts:
                def cleanup():
                    shutil.rmtree(directory)
                    return "Removed native temporary artifacts"

                if not check("native-cleanup", cleanup,
                             "Remove the reported temporary directory after inspecting its permissions."):
                    report["native_artifacts"] = str(directory)

    failed = any(row["status"] == "fail" for row in checks)
    native_passed = native and any(row["id"] == "native-changed-claim" and row["status"] == "pass" for row in checks)
    report.update(passed=not failed, native_passed=native_passed,
                  summary="Diagnostics failed" if failed else "Native smoke passed" if native_passed else "Preflight passed; native verification not run")
    return report


def execute(args):
    if args.keep_artifacts and not args.native:
        raise ValueError("--keep-artifacts requires --native")
    report = diagnose(native=args.native, timeout=args.timeout, keep_artifacts=args.keep_artifacts)
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        for row in report["checks"]:
            print(f"{row['status'].upper():4}  {row['id']}: {row['detail']}")
            if row["remediation"]:
                print("      " + row["remediation"])
        print(report["summary"])
        if report["native_artifacts"]:
            print("Artifacts: " + report["native_artifacts"])
    return 0 if report["passed"] else 1


def main(argv=None):
    parser = argparse.ArgumentParser(prog="s31 doctor", description="Check S31 source, toolchain, and optional native proof readiness.")
    add_arguments(parser)
    args = parser.parse_args(argv)
    if args.keep_artifacts and not args.native:
        parser.error("--keep-artifacts requires --native")
    return execute(args)
