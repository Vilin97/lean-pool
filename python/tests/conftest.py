"""Shared fixtures: a canonical stub of the optional ``openai`` package.

``openai`` ships only in the ``review`` dependency group, which the test
environment does not install, yet ``lean_pool.review`` and
``lean_pool.aggregator.triage`` import it at module load. Register one
stub — with the real package's exception hierarchy, including the
``status_code`` attributes the code under test inspects — before any
test module imports those modules. Individual test files must not
register competing stubs: whichever loaded first would win, starving
the others of attributes it lacks.
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
