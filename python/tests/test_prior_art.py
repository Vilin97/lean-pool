"""Tests for the prior-art evidence handed to the LLM reviewer."""

from __future__ import annotations

PROJECTS_BASE = """
projects:
  - slug: incompleteness
    title: Godel's Incompleteness Theorems
    tags: [logic, proof-theory]
    main_results:
      - declaration: LeanPool.Incompleteness.goedel_first
        informal: No consistent recursive theory proves its own consistency.
"""

PROJECTS_HEAD = (
    PROJECTS_BASE
    + """
  - slug: debruijn-erdos
    title: de Bruijn-Erdos compactness for graph coloring
    tags: [graph-theory, combinatorics]
    main_results:
      - declaration: LeanPool.DeBruijnErdos.colorable_of_forall_finite
        informal: A graph is k-colorable if every finite subgraph is k-colorable.
"""
)


def test_new_claims_only_covers_what_the_pr_adds() -> None:
    """A card already on main is settled; only new headlines are searched."""
    from lean_pool.prior_art import new_claims

    claims = new_claims(PROJECTS_HEAD, PROJECTS_BASE, "project")

    assert [claim.declaration for claim in claims] == [
        "LeanPool.DeBruijnErdos.colorable_of_forall_finite"
    ]
    assert "finite subgraph" in claims[0].informal


def test_new_claims_reads_the_challenge_registry_too() -> None:
    """Challenges carry the same pairs under different keys."""
    from lean_pool.prior_art import new_claims

    head = """
challenges:
  - slug: twin-primes
    statements:
      - declaration: Challenge.TwinPrimes.infinite
        informal: There are infinitely many twin primes.
"""

    claims = new_claims(head, "challenges: []\n", "challenge")

    assert claims[0].declaration == "Challenge.TwinPrimes.infinite"
    assert claims[0].query == "There are infinitely many twin primes."


def test_claim_query_falls_back_to_the_declaration_name() -> None:
    """A card with no informal text is still searchable by name."""
    from lean_pool.prior_art import Claim

    assert Claim("LeanPool.Foo.bar_baz", "  ").query == "LeanPool.Foo.bar_baz"


def test_new_claims_survives_a_malformed_registry() -> None:
    """Unparseable YAML costs the search, never the review."""
    from lean_pool.prior_art import new_claims

    assert new_claims("projects: [oops", PROJECTS_BASE, "project") == []
    assert new_claims("", "", "project") == []


def test_pool_index_lists_every_project() -> None:
    """The whole pool goes in; no similarity heuristic decides for us."""
    from lean_pool.prior_art import pool_index

    index = pool_index(PROJECTS_HEAD)

    expected = "incompleteness: Godel's Incompleteness Theorems [logic, proof-theory]"
    assert expected in index
    assert "debruijn-erdos:" in index
    assert len(index.splitlines()) == 2


def test_render_surfaces_a_duplicate_as_a_candidate_not_a_verdict() -> None:
    """The #275 miss: the real duplicate reaches the reviewer, hedged.

    PR #275 was approved with zero findings and then closed by hand for
    duplicating `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`.
    The reviewer now sees that declaration — but told it is a candidate,
    since a shared vocabulary is not a duplicate.
    """
    from lean_pool.prior_art import MathlibHit, new_claims, render

    claims = new_claims(PROJECTS_HEAD, PROJECTS_BASE, "project")
    hits = {
        claims[0].declaration: [
            MathlibHit(
                "SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom",
                "Mathlib.Combinatorics.SimpleGraph.Finsubgraph",
                "The De Bruijn-Erdos Theorem for Graph Homomorphisms.",
            )
        ]
    }

    section = render(claims, hits, PROJECTS_HEAD, None)

    assert section is not None
    assert "SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom" in section
    assert "candidate" in section
    # The module goes with it, so the reviewer can cite where it lives.
    assert "Mathlib.Combinatorics.SimpleGraph.Finsubgraph" in section
    # The pool goes along too — #225 was subsumed by a pooled project.
    assert "incompleteness:" in section


def test_render_says_plainly_when_nothing_matched() -> None:
    """An empty result is evidence of novelty and must read as such."""
    from lean_pool.prior_art import new_claims, render

    claims = new_claims(PROJECTS_HEAD, PROJECTS_BASE, "project")

    section = render(claims, {claims[0].declaration: []}, PROJECTS_HEAD, None)

    assert section is not None
    assert "No Mathlib declaration matched" in section


def test_render_distinguishes_a_failed_search_from_a_clean_one() -> None:
    """Silence must never be mistaken for an absence of prior art."""
    from lean_pool.prior_art import new_claims, render

    claims = new_claims(PROJECTS_HEAD, PROJECTS_BASE, "project")

    section = render(claims, {}, PROJECTS_HEAD, "LEANEXPLORE_API_KEY is not set")

    assert section is not None
    assert "Not searched" in section
    assert "No Mathlib declaration matched" not in section


def test_search_mathlib_without_a_key_reports_why(monkeypatch) -> None:
    """A missing key is a stated reason, not an exception."""
    from lean_pool.prior_art import Claim, search_mathlib

    monkeypatch.delenv("LEANEXPLORE_API_KEY", raising=False)

    hits, unavailable = search_mathlib([Claim("A.b", "something")])

    assert hits == {}
    assert unavailable is not None and "LEANEXPLORE_API_KEY" in unavailable


def test_search_mathlib_swallows_a_backend_failure(monkeypatch) -> None:
    """LeanExplore being down must not fail the review."""
    from lean_pool import prior_art

    monkeypatch.setenv("LEANEXPLORE_API_KEY", "x")

    async def _boom(_claims):
        raise RuntimeError("connection reset")

    monkeypatch.setattr(prior_art, "_search_all", _boom)

    hits, unavailable = prior_art.search_mathlib([prior_art.Claim("A.b", "q")])

    assert hits == {}
    assert unavailable is not None and "connection reset" in unavailable


def test_no_claims_means_no_search_and_no_failure_note() -> None:
    """A PR that adds no headline is not a search that went wrong."""
    from lean_pool.prior_art import search_mathlib

    assert search_mathlib([]) == ({}, None)


def test_zero_claims_from_a_failure_never_reads_as_nothing_new() -> None:
    """An unreadable registry must not render as "adds no new headline".

    Both produce zero claims, and only one of them means prior art went
    unchecked. Conflating them is how a broken search reports success.
    """
    from lean_pool.prior_art import render

    broken = render([], {}, PROJECTS_BASE, "projects.yml could not be read")
    empty = render([], {}, PROJECTS_BASE, None)

    assert broken is not None and empty is not None
    assert "did not run" in broken
    assert "adds no new headline" not in broken
    assert "adds no new headline" in empty
    assert "did not run" not in empty
