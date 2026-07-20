"""Tests for LLM triage of discovered Lean repositories."""

from __future__ import annotations

import json
import sys
import types
from pathlib import Path

import yaml

# `openai` ships only in the `review` dependency group, which the test
# environment does not install. Stub it before importing the triage module
# (which imports it at module load), exactly as the review tests do.
openai_stub = types.ModuleType("openai")
openai_stub.APIStatusError = Exception
openai_stub.OpenAI = object
openai_stub.RateLimitError = Exception
sys.modules.setdefault("openai", openai_stub)

from lean_pool.aggregator.discovery import _github_queries  # noqa: E402
from lean_pool.aggregator.triage import (  # noqa: E402
    repository_context,
    triage_discovered_file,
)


class _FakeMessage:
    def __init__(self, content: str) -> None:
        self.content = content


class _FakeChoice:
    def __init__(self, content: str) -> None:
        self.message = _FakeMessage(content)


class _FakeUsage:
    def __init__(self, prompt_tokens: int, completion_tokens: int) -> None:
        self.prompt_tokens = prompt_tokens
        self.completion_tokens = completion_tokens


class _FakeResponse:
    def __init__(self, content: str) -> None:
        self.choices = [_FakeChoice(content)]
        self.usage = _FakeUsage(11, 7)


class _FakeCompletions:
    def __init__(self, responder) -> None:
        self._responder = responder
        self.calls: list[dict] = []

    def create(self, **kwargs):
        self.calls.append(kwargs)
        return self._responder(kwargs)


class _FakeChat:
    def __init__(self, responder) -> None:
        self.completions = _FakeCompletions(responder)


class _FakeClient:
    """Stand-in for the OpenAI client with a scripted responder."""

    def __init__(self, responder) -> None:
        self.chat = _FakeChat(responder)


def _by_full_name(content_for: dict[str, str]):
    """Return a responder that keys off the repo full_name in the prompt."""

    def responder(kwargs: dict) -> _FakeResponse:
        user = kwargs["messages"][-1]["content"]
        payload = json.loads(user)
        return _FakeResponse(content_for[payload["full_name"]])

    return responder


def _write_discovered(path: Path, github: dict) -> None:
    path.write_text(yaml.safe_dump({"version": 1, "github": github, "arxiv": {}}))


def test_queries_filter_on_created_only() -> None:
    """No `pushed:` query, so established repos do not re-surface."""
    queries = _github_queries(__import__("datetime").date(2026, 1, 1))
    assert queries, "expected at least one query"
    assert all("pushed:" not in query for query in queries)
    assert all("created:>=2026-01-01" in query for query in queries)


def test_triage_records_keep_and_skip_verdicts(tmp_path: Path) -> None:
    """Each untriaged repo gets a keep/skip verdict written back."""
    path = tmp_path / "discovered.yml"
    _write_discovered(
        path,
        {
            "real/project": {
                "full_name": "real/project",
                "description": "Formalization of the Yoneda lemma in Lean 4.",
            },
            "crank/toe": {
                "full_name": "crank/toe",
                "description": "The holy grail of physics is found.",
            },
        },
    )
    client = _FakeClient(
        _by_full_name(
            {
                "real/project": '{"verdict": "keep", "reason": "genuine formal math"}',
                "crank/toe": '{"verdict": "skip", "reason": "physics crank manifesto"}',
            }
        )
    )

    update = triage_discovered_file(path, model="gpt-5.4-nano", client=client)

    assert (update.triaged, update.kept, update.skipped) == (2, 1, 1)
    data = yaml.safe_load(path.read_text())["github"]
    assert data["real/project"]["triage"]["verdict"] == "keep"
    assert data["crank/toe"]["triage"]["verdict"] == "skip"
    assert data["crank/toe"]["triage"]["model"] == "gpt-5.4-nano"


def test_triage_is_idempotent(tmp_path: Path) -> None:
    """A second pass triages nothing and makes no further model calls."""
    path = tmp_path / "discovered.yml"
    _write_discovered(
        path, {"a/b": {"full_name": "a/b", "description": "real analysis in Lean"}}
    )
    client = _FakeClient(_by_full_name({"a/b": '{"verdict": "keep", "reason": "ok"}'}))

    first = triage_discovered_file(path, model="m", client=client)
    second = triage_discovered_file(path, model="m", client=client)

    assert first.triaged == 1
    assert second.triaged == 0
    assert len(client.chat.completions.calls) == 1


def test_malformed_response_defaults_to_keep(tmp_path: Path) -> None:
    """An unparseable model reply never silently drops a repo."""
    path = tmp_path / "discovered.yml"
    _write_discovered(path, {"a/b": {"full_name": "a/b", "description": "x"}})
    client = _FakeClient(_by_full_name({"a/b": "not json at all"}))

    update = triage_discovered_file(path, model="m", client=client)

    assert (update.triaged, update.kept, update.skipped) == (1, 1, 0)
    data = yaml.safe_load(path.read_text())["github"]
    assert data["a/b"]["triage"]["verdict"] == "keep"


def test_repository_context_is_compact() -> None:
    """Context trims long descriptions and drops heavy fields."""
    record = {
        "full_name": "o/n",
        "description": "z" * 400,
        "topics": [f"t{i}" for i in range(30)],
        "license": "MIT",
        "estimated_lean_loc": 1234,
        "lean_file_count": 9,
        "stars": 3,
        "reasons": ["irrelevant heavy field"],
        "readme_excerpt": "should not be forwarded",
    }
    context = repository_context(record)
    assert len(context["description"]) <= 280
    assert len(context["topics"]) == 10
    assert "reasons" not in context
    assert "readme_excerpt" not in context
    assert context["estimated_lean_loc"] == 1234
