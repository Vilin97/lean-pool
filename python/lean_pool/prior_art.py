"""Prior-art evidence assembled for the LLM review.

``REVIEW_RULES.md`` asks whether a contribution's headline is already
proved in Mathlib or already in the pool. Until now the reviewer had no
way to find out: it saw the rules, the PR description, and the diff, and
nothing else. The first production run under the audited rules answered
the question with "unverifiable from the supplied diff", which is honest
and useless — while PR #275 had been approved and then closed by hand for
duplicating ``SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom``.

This module answers it before the model is asked, in two ways:

- **Mathlib** — each headline the PR claims is put to LeanExplore's
  hybrid (name + meaning) search over Mathlib, and the hits are handed to
  the reviewer as evidence. Searching the de Bruijn-Erdos claim returns
  the declaration #275 duplicated; searching a genuinely new result
  returns unrelated lemmas, so the evidence reads in both directions.
- **The pool** — every pooled project's slug, title, and tags, which is
  small enough (~4k tokens for 141 projects) to include whole. No
  similarity heuristic can beat handing over the complete list.

Evidence is *pre-computed* rather than exposed as a tool the model calls:
the search is deterministic, testable, and costs one round trip whether
or not the model would have thought to look.

The results are our own machine output, not contributor-written text, so
they are presented outside the fenced untrusted span (see
``review.UNTRUSTED_INPUT_RULE``) — but a search hit is still only a
candidate, and the rules say so.

Environment variables:
    LEANEXPLORE_API_KEY: LeanExplore credentials. Absent, the Mathlib
        search is skipped and the reviewer is told it did not run.
"""

from __future__ import annotations

import asyncio
import os
from dataclasses import dataclass
from typing import Any

import yaml

# Headlines searched per PR. Cards list a handful of main results; this
# caps the pathological case without truncating a normal project.
MAX_CLAIMS = 8
# Hits shown per claim. Enough to include a correct match that does not
# rank first — the #275 duplicate came back fifth.
MATHLIB_HITS_PER_CLAIM = 6


@dataclass(frozen=True)
class Claim:
    """One headline the PR asserts, as its card states it.

    Attributes:
        declaration: Fully qualified Lean name of the main result.
        informal: The card's English statement of it, which is what a
            meaning-based search can actually match on.
    """

    declaration: str
    informal: str

    @property
    def query(self) -> str:
        """Search text: the prose if there is any, else the name."""
        return self.informal.strip() or self.declaration


@dataclass(frozen=True)
class MathlibHit:
    """One Mathlib declaration LeanExplore offered for a claim.

    Attributes:
        name: Fully qualified declaration name.
        module: Mathlib module it lives in, so the reviewer can cite it.
        description: What the declaration says, in words —
            LeanExplore's ``informalization``, or its docstring when
            there is no informalization.
    """

    name: str
    module: str
    description: str


def _field(result: Any, field: str) -> Any:
    """Read one field off a LeanExplore hit, dict or object."""
    if isinstance(result, dict):
        return result.get(field)
    return getattr(result, field, None)


def _entries(text: str, key: str) -> list[dict]:
    """Return the registry list under ``key``, tolerating junk."""
    try:
        loaded = yaml.safe_load(text) or {}
    except yaml.YAMLError:
        return []
    entries = loaded.get(key) if isinstance(loaded, dict) else loaded
    if not isinstance(entries, list):
        return []
    return [entry for entry in entries if isinstance(entry, dict)]


def _claims_of(entry: dict, results_key: str) -> list[Claim]:
    """Pull the (declaration, informal) pairs out of one registry entry."""
    claims: list[Claim] = []
    for result in entry.get(results_key) or []:
        if not isinstance(result, dict):
            continue
        declaration = str(result.get("declaration") or "").strip()
        if declaration:
            claims.append(Claim(declaration, str(result.get("informal") or "").strip()))
    return claims


def new_claims(head_text: str, base_text: str, kind: str) -> list[Claim]:
    """Return the headlines this PR adds that were not there before.

    Only *new* entries are searched. A refactor or a bump touches cards
    whose prior art was settled when they merged, and re-searching them
    would spend tokens to re-litigate a closed question.

    Args:
        head_text: The registry file as of the PR head.
        base_text: The same file on the base branch.
        kind: ``"project"`` (``projects.yml``) or ``"challenge"``
            (``challenges.yml``), which differ only in their keys.

    Returns:
        Up to :data:`MAX_CLAIMS` claims, in registry order.
    """
    list_key, results_key = (
        ("projects", "main_results")
        if kind == "project"
        else ("challenges", "statements")
    )
    known = {
        claim.declaration
        for entry in _entries(base_text, list_key)
        for claim in _claims_of(entry, results_key)
    }
    claims: list[Claim] = []
    for entry in _entries(head_text, list_key):
        for claim in _claims_of(entry, results_key):
            if claim.declaration not in known:
                claims.append(claim)
    return claims[:MAX_CLAIMS]


def pool_index(projects_text: str) -> str:
    """Render every pooled project as one ``slug: title [tags]`` line.

    Handing over the whole list beats any similarity heuristic: it is
    complete, it needs no search, and at ~4k tokens for 141 projects it
    is cheaper than being wrong about what to omit.
    """
    lines = []
    for entry in _entries(projects_text, "projects"):
        slug = str(entry.get("slug") or "").strip()
        if not slug:
            continue
        title = str(entry.get("title") or "").strip()
        tags = [str(tag) for tag in (entry.get("tags") or [])][:4]
        suffix = f" [{', '.join(tags)}]" if tags else ""
        lines.append(f"{slug}: {title}{suffix}")
    return "\n".join(lines)


async def _search_one(client: Any, claim: Claim) -> list[MathlibHit]:
    """Run one LeanExplore query, returning its hits."""
    response = await client.search(
        query=claim.query,
        limit=MATHLIB_HITS_PER_CLAIM,
        packages=["Mathlib"],
    )
    hits = []
    for result in getattr(response, "results", []) or []:
        name = str(_field(result, "name") or "").strip()
        if not name:
            continue
        # `SearchResult` carries no `description`: the prose lives in
        # `informalization`, with the docstring as the fallback.
        described = _field(result, "informalization") or _field(result, "docstring")
        hits.append(
            MathlibHit(
                name=name,
                module=str(_field(result, "module") or "").strip(),
                description=" ".join(str(described or "").split())[:300],
            )
        )
    return hits


async def _search_all(claims: list[Claim]) -> dict[str, list[MathlibHit]]:
    """Search every claim concurrently against Mathlib."""
    from lean_explore.api import ApiClient

    client = ApiClient()
    results = await asyncio.gather(
        *(_search_one(client, claim) for claim in claims), return_exceptions=True
    )
    return {
        claim.declaration: hits
        for claim, hits in zip(claims, results, strict=True)
        if not isinstance(hits, BaseException)
    }


def search_mathlib(
    claims: list[Claim],
) -> tuple[dict[str, list[MathlibHit]], str | None]:
    """Search Mathlib for each claim.

    Returns:
        ``(hits_by_declaration, unavailable_reason)``. A search that
        cannot run is never fatal — the reviewer is told it did not
        happen so it can say `unverifiable` honestly rather than
        mistaking silence for an absence of prior art.
    """
    if not claims:
        return {}, None
    if not os.environ.get("LEANEXPLORE_API_KEY"):
        return {}, "LEANEXPLORE_API_KEY is not set"
    try:
        return asyncio.run(_search_all(claims)), None
    except Exception as error:  # noqa: BLE001 - never fail a review over search
        return {}, f"the search failed ({type(error).__name__}: {error})"


def render(
    claims: list[Claim],
    hits: dict[str, list[MathlibHit]],
    projects_text: str,
    unavailable: str | None,
) -> str | None:
    """Render the prior-art section of the review prompt, or ``None``.

    Returns ``None`` when there is nothing to say — no new headline and
    no pool to compare against — so an unrelated PR pays nothing.
    """
    index = pool_index(projects_text)
    if not claims and not index:
        return None

    sections: list[str] = [
        "Searches run for you before this review, so that "
        "`already_formalized` can be answered rather than guessed. A hit "
        "is a *candidate*, not a verdict: read the statement before "
        "calling anything a duplicate, and ignore hits that merely share "
        "vocabulary."
    ]

    if claims:
        lines = ["", "### Mathlib search, per headline this PR adds", ""]
        for claim in claims:
            lines.append(f"**{claim.declaration}**")
            if claim.informal:
                lines.append(f"> {claim.informal}")
            found = hits.get(claim.declaration)
            if unavailable is not None:
                lines.append(f"- _Not searched: {unavailable}._")
            elif found:
                for hit in found:
                    where = f" ({hit.module})" if hit.module else ""
                    says = f" — {hit.description}" if hit.description else ""
                    lines.append(f"- `{hit.name}`{where}{says}")
            else:
                lines.append("- _No Mathlib declaration matched this statement._")
            lines.append("")
        sections.append("\n".join(lines))
    elif unavailable is None:
        sections.append(
            "\nThis PR adds no new headline to a registry, so no Mathlib "
            "search was run."
        )

    if index:
        sections.append(
            "### Every project already in the pool\n\n"
            "Compare against this list before saying a contribution is new; "
            "prior art in the pool counts the same as prior art in Mathlib.\n\n"
            f"```\n{index}\n```"
        )
    return "\n".join(sections)
