"""Fast source diagnostics using the same text-to-relation path as builds.

This command is intentionally source-only. A valid result is evidence that
parsing, static checks, specialization, and relation construction succeeded;
native package construction and proof verification have separate commands.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

from language.syntax import SourceError
from package.context import lower_text


def _diagnostic(error: str, source: Path) -> dict:
    """Extract a compiler location without losing older path-only errors."""
    prefix = f"{source}:"
    rest = error[len(prefix):] if error.startswith(prefix) else error
    parts = rest.split(":", 2)
    if len(parts) == 3 and parts[0].isdigit() and parts[1].isdigit():
        line, column = int(parts[0]), int(parts[1])
        message = parts[2].lstrip()
    else:
        line = column = None
        message = rest.lstrip() if error.startswith(prefix) else error
    return {"message": message, "line": line, "column": column}


def check_source(source: Path) -> dict:
    """Check one text program and return a stable single-result protocol."""
    source = source.resolve()
    result = {"schema": "s31-source-check-v1", "source": str(source)}
    if source.suffix != ".s31":
        return {**result, "status": "invalid", "diagnostic": {
            "message": "check-source expects a .s31 text file", "line": None,
            "column": None,
        }}
    try:
        relation, encoded, _ = lower_text(source)
    except (SourceError, OSError, UnicodeError) as exc:
        return {**result, "status": "invalid", "diagnostic": _diagnostic(str(exc), source)}
    return {**result, "status": "valid", "program": relation["name"],
            "relation_sha256": hashlib.sha256(encoded).hexdigest(),
            "relation_nodes": len(relation["nodes"])}


def render_source_check(result: dict) -> str:
    """Render a bounded source excerpt only for a located error."""
    source = result["source"]
    if result["status"] == "valid":
        return (f"{source}: valid {result['program']} "
                f"({result['relation_nodes']} relation nodes, "
                f"SHA-256 {result['relation_sha256']})")
    diagnostic = result["diagnostic"]
    line, column = diagnostic["line"], diagnostic["column"]
    location = f"{source}:{line}:{column}" if line is not None else source
    rendered = f"{location}: {diagnostic['message']}"
    if line is None or column is None or line < 1 or column < 1:
        return rendered
    try:
        lines = Path(source).read_text().splitlines()
    except (OSError, UnicodeError):
        return rendered
    if line > len(lines):
        return rendered
    excerpt = lines[line - 1]
    # Avoid producing an unbounded terminal diagnostic from a very long line.
    window_start = max(0, column - 81)
    visible = excerpt[window_start:window_start + 160]
    caret = min(column - window_start - 1, len(visible))
    return f"{rendered}\n  {visible}\n  {' ' * max(caret, 0)}^"
