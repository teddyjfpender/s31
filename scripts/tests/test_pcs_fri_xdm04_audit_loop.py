"""Hostile source-order controls for the XDM04 audit-to-recurrence seam."""

from __future__ import annotations

import unittest

from scripts.release.pcs_fri_xdm04_audit_loop import AUDIT_SOURCE, check_audit_source


class Xdm04AuditLoopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source = AUDIT_SOURCE.read_bytes()

    def test_reviewed_source(self) -> None:
        check_audit_source(self.source)

    def test_any_source_change_requires_review(self) -> None:
        with self.assertRaisesRegex(ValueError, "source changed"):
            check_audit_source(self.source + b"\n")

    def test_required_loop_checks_cannot_be_skipped(self) -> None:
        for old, new in (
            (b"sameHash(self.replay(), self.root)", b"true"),
            (b"if (!opening.check()) return error.InvalidXdm04Certificate;",
             b"if (false) return error.InvalidXdm04Certificate;"),
            (b"const left = if (position & 1 == 0) current else step.sibling;",
             b"const left = current;"),
            (b"position >>= 1;", b"position += 1;"),
            (b"if (!sameHash(current, self.nodes.get(key(at_level, at_index))",
             b"if (false)"),
            (b"for (0..2) |j| try self.auditAt(height, query, j);",
             b"for (0..0) |j| try self.auditAt(height, query, j);"),
            (b"var opened = try xdm.verifyAndCollect(",
             b"var opened = try skippedNativeVerifier("),
            (b"try capture.auditAll();", b"// try capture.auditAll();"),
        ):
            with self.subTest(old=old):
                changed = self.source.replace(old, new)
                self.assertNotEqual(changed, self.source)
                with self.assertRaises(ValueError):
                    check_audit_source(changed, require_digest=False)


if __name__ == "__main__":
    unittest.main()
