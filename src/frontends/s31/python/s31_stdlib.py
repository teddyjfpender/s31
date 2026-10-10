"""Compatibility import for the compiler-owned standard library.

Implementation lives in ``library.stdlib``. Keep this module so existing
build scripts, examples and external integrations retain their import path.
"""

from library.stdlib import *  # noqa: F401,F403
