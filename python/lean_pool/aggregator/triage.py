"""LLM triage of freshly discovered Lean repositories.

The deterministic discovery scout (:mod:`lean_pool.aggregator.discovery`)
scores repos purely by keyword and project shape, so crank "theory of
everything" manifestos and AI-generated filler that happen to ship a
lakefile and the word "proof" land with a high signal. This module adds a
cheap second pass: it asks a small OpenAI model to look at each newly
discovered repo and decide *keep* (plausibly a genuine, non-trivial formal
project) or *skip* (obvious nonsense), recording the verdict back into
``candidates/discovered.yml``.

It mirrors :mod:`lean_pool.review`: OpenAI client, ``flex`` service tier
with a fallback to ``auto`` when flex is unavailable, and a strict JSON
response. The model is deliberately tiny and the context per repo is
deliberately small — a high false-positive (keep) rate is acceptable; the
goal is only to drop the obvious junk.

Triage is idempotent: a record that already carries a ``triage`` block is
left untouched, so the daily run only spends tokens on genuinely new
entries.

Environment variables:
    OPENAI_API_KEY: OpenAI credentials (required).
    TRIAGE_MODEL:   Model name; defaults to :data:`DEFAULT_MODEL`.

Run:
    uv run python -m lean_pool.aggregator triage
"""

from __future__ import annotations

import json
import logging
from dataclasses import dataclass
from pathlib import Path
from textwrap import dedent
from typing import Any, Protocol

from openai import APIStatusError, OpenAI, RateLimitError

from lean_pool.aggregator.discovery import (
    _dump_discovered_file,
    _load_discovered_file,
)

logger = logging.getLogger(__name__)

DEFAULT_MODEL = "gpt-5.4-nano"
REQUEST_TIMEOUT_SECONDS = 600.0
_DESCRIPTION_LIMIT = 280
_TOPIC_LIMIT = 10
_REASON_LIMIT = 200

SYSTEM_PROMPT = dedent(
    """\
    You triage newly created public Lean 4 repositories for Lean Pool, a
    curated pool of serious formal-mathematics and related formal-CS
    projects. For each repo, decide "keep" or "skip".

    Skip only when the repo is clearly not a candidate:
    - crank / grand-unified "theory of everything" / physics-salvation
      manifestos ("holy grail of physics", 万物理论, etc.);
    - AI-generated filler with no real mathematical content, often huge
      line counts, zero stars, and a vague or absent description;
    - personal learning, exercises, homework, tutorials, course or book
      scaffolding, competition-solution dumps;
    - near-empty, template, or plainly off-topic repos.

    Keep everything else. A high false-positive (keep) rate is acceptable
    — only skip what is obviously nonsense. When unsure, keep.

    Respond with a single JSON object and nothing else:
    {"verdict": "keep" | "skip", "reason": "<= 15 words"}.
    """
)


class _ChatClient(Protocol):
    """Minimal structural type for the OpenAI client used here."""

    chat: Any


@dataclass(frozen=True)
class TriageVerdict:
    """One model decision about a repository."""

    verdict: str
    reason: str
    prompt_tokens: int = 0
    completion_tokens: int = 0


@dataclass(frozen=True)
class TriageUpdate:
    """Counts from one triage pass over the discovered file."""

    triaged: int
    kept: int
    skipped: int
    prompt_tokens: int
    completion_tokens: int


def make_client() -> OpenAI:
    """Return an OpenAI client configured with the shared timeout."""
    return OpenAI(timeout=REQUEST_TIMEOUT_SECONDS)


def repository_context(record: dict[str, Any]) -> dict[str, Any]:
    """Build the compact, low-token context handed to the model.

    Args:
        record: One repository record from ``discovered.yml``.

    Returns:
        A small JSON-serialisable dict with only the fields that help a
        keep/skip judgment.
    """
    description = (record.get("description") or "").strip()
    if len(description) > _DESCRIPTION_LIMIT:
        description = description[: _DESCRIPTION_LIMIT - 1].rstrip() + "…"
    topics = [str(topic) for topic in (record.get("topics") or [])][:_TOPIC_LIMIT]
    return {
        "full_name": record.get("full_name") or "",
        "description": description,
        "topics": topics,
        "license": record.get("license"),
        "estimated_lean_loc": record.get("estimated_lean_loc", 0),
        "lean_file_count": record.get("lean_file_count", 0),
        "stars": record.get("stars", 0),
    }


def triage_repository(
    record: dict[str, Any], *, model: str, client: _ChatClient
) -> TriageVerdict:
    """Ask the model whether one repository is worth keeping.

    Tries the ``flex`` service tier first and falls back to ``auto`` when
    flex is out of capacity or unsupported, exactly as the PR reviewer
    does. Any malformed response is treated as ``keep`` so that a flaky
    model never silently drops a real project.

    Args:
        record: One repository record from ``discovered.yml``.
        model: OpenAI model name.
        client: An OpenAI-compatible chat client.

    Returns:
        The parsed verdict plus token usage.
    """
    context = repository_context(record)
    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": json.dumps(context, ensure_ascii=False)},
    ]
    response = _create_with_fallback(client, model=model, messages=messages)
    content = response.choices[0].message.content or "{}"
    verdict, reason = _parse_verdict(content)
    usage = response.usage
    return TriageVerdict(
        verdict=verdict,
        reason=reason,
        prompt_tokens=getattr(usage, "prompt_tokens", 0) or 0,
        completion_tokens=getattr(usage, "completion_tokens", 0) or 0,
    )


def _create_with_fallback(
    client: _ChatClient, *, model: str, messages: list[dict[str, str]]
) -> Any:
    try:
        return client.chat.completions.create(
            model=model,
            messages=messages,
            response_format={"type": "json_object"},
            service_tier="flex",
        )
    except (RateLimitError, APIStatusError) as exc:
        status = getattr(exc, "status_code", None)
        if isinstance(exc, RateLimitError) or (status is not None and 500 <= status):
            return client.chat.completions.create(
                model=model,
                messages=messages,
                response_format={"type": "json_object"},
                service_tier="auto",
            )
        raise


def _parse_verdict(content: str) -> tuple[str, str]:
    try:
        payload = json.loads(content)
    except (json.JSONDecodeError, TypeError):
        return "keep", "unparseable model response; kept by default"
    verdict = str(payload.get("verdict") or "").strip().lower()
    if verdict not in {"keep", "skip"}:
        verdict = "keep"
    reason = str(payload.get("reason") or "").strip()[:_REASON_LIMIT]
    return verdict, reason


def triage_discovered_file(
    path: Path,
    *,
    model: str,
    client: _ChatClient | None = None,
    limit: int | None = None,
    retriage: bool = False,
) -> TriageUpdate:
    """Triage untriaged GitHub records in ``discovered.yml`` in place.

    Args:
        path: The ``discovered.yml`` file to update.
        model: OpenAI model name.
        client: OpenAI-compatible client; created on demand when omitted.
        limit: Optional cap on how many records to triage this run.
        retriage: Re-triage records that already carry a verdict.

    Returns:
        Counts and token usage for the pass.
    """
    data = _load_discovered_file(path)
    github = data["github"]
    pending = [
        (key, record)
        for key, record in github.items()
        if retriage or not isinstance(record.get("triage"), dict)
    ]
    if limit is not None:
        pending = pending[:limit]
    if not pending:
        return TriageUpdate(0, 0, 0, 0, 0)

    if client is None:
        client = make_client()

    triaged = kept = skipped = prompt_tokens = completion_tokens = 0
    for key, record in pending:
        try:
            decision = triage_repository(record, model=model, client=client)
        except Exception as exc:  # noqa: BLE001 - one bad repo must not abort the run
            logger.warning("triage failed for %s: %s", key, exc)
            continue
        record["triage"] = {
            "verdict": decision.verdict,
            "reason": decision.reason,
            "model": model,
        }
        triaged += 1
        kept += decision.verdict == "keep"
        skipped += decision.verdict == "skip"
        prompt_tokens += decision.prompt_tokens
        completion_tokens += decision.completion_tokens

    if triaged:
        path.write_text(_dump_discovered_file(data))
    return TriageUpdate(
        triaged=triaged,
        kept=kept,
        skipped=skipped,
        prompt_tokens=prompt_tokens,
        completion_tokens=completion_tokens,
    )
