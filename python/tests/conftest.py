"""Shared fixtures: canonical stubs of the optional ``review`` packages.

``openai`` and ``lean_explore`` ship only in the ``review`` dependency
group, which the test environment does not install, yet
``lean_pool.review`` and ``lean_pool.prior_art`` import them. Register
one stub each — with the
attributes the code under test actually inspects, such as ``openai``'s
exception hierarchy and its ``status_code`` — before any test module
imports those modules. Individual test files must not register competing
stubs: whichever loaded first would win, starving the others of
attributes it lacks.

Both use ``setdefault``, so a developer who has run ``uv sync --group
review`` exercises the real packages instead. That difference is why
``lean_explore`` is stubbed here at all: it was missing from this file
once, the suite passed locally against the real install, and CI caught
the import at ``prior_art._search_all``.
"""

from __future__ import annotations

import sys
import types


class _APIStatusError(Exception):
    """Stub mirroring ``openai.APIStatusError``'s ``status_code``."""

    status_code = 500


class _RateLimitError(_APIStatusError):
    """Stub mirroring ``openai.RateLimitError`` (HTTP 429)."""

    status_code = 429


class _BadRequestError(_APIStatusError):
    """Stub mirroring ``openai.BadRequestError`` (HTTP 400)."""

    status_code = 400


openai_stub = types.ModuleType("openai")
openai_stub.APIStatusError = _APIStatusError
openai_stub.BadRequestError = _BadRequestError
openai_stub.OpenAI = object
openai_stub.RateLimitError = _RateLimitError
sys.modules.setdefault("openai", openai_stub)


class _ApiClient:
    """Stub of ``lean_explore.api.ApiClient``.

    Constructs without credentials and never reaches the network; tests
    that need results patch ``prior_art._search_one``.
    """

    def __init__(self, api_key: str | None = None, timeout: float = 10.0) -> None:
        """Accept the real client's arguments and ignore them."""
        self.api_key = api_key
        self.timeout = timeout

    async def search(self, **kwargs):
        """Return no results, as an unconfigured backend would."""
        return types.SimpleNamespace(results=[])


lean_explore_stub = types.ModuleType("lean_explore")
lean_explore_api_stub = types.ModuleType("lean_explore.api")
lean_explore_api_stub.ApiClient = _ApiClient
lean_explore_stub.api = lean_explore_api_stub
sys.modules.setdefault("lean_explore", lean_explore_stub)
sys.modules.setdefault("lean_explore.api", lean_explore_api_stub)
