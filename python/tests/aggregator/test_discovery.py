"""Tests for daily private candidate discovery."""

from __future__ import annotations

import json
from datetime import UTC, date, datetime
from pathlib import Path

import yaml

from lean_pool.aggregator.discovery import (
    ArxivPaper,
    DiscoveryResult,
    GitHubRepository,
    _HttpClient,
    _score_repository,
    load_known_repository_keys,
    parse_arxiv_feed,
    render_discovery_report,
    update_discovered_file,
)


def _package(full_name: str) -> dict:
    """Build a minimal Reservoir-shaped package fixture."""
    return {
        "fullName": full_name,
        "sources": [
            {
                "repoUrl": f"https://github.com/{full_name}",
                "gitUrl": f"https://github.com/{full_name}.git",
            }
        ],
    }


def test_load_known_repository_keys_collects_all_local_sources(tmp_path: Path) -> None:
    """Reservoir, manual, cached manual metadata, and projects.yml all count."""
    manifest_path = tmp_path / "manifest.json"
    manual_list_path = tmp_path / "manual.txt"
    manual_data_path = tmp_path / "manual_packages.json"
    projects_yml_path = tmp_path / "projects.yml"

    manifest_path.write_text(json.dumps({"packages": [_package("Acme/Reservoir")]}))
    manual_list_path.write_text("https://github.com/acme/manual\n")
    manual_data_path.write_text(json.dumps([_package("acme/Cached.lean")]))
    projects_yml_path.write_text(
        "projects:\n  - slug: merged\n    source:\n      github_repo: Acme/Merged\n"
    )

    known = load_known_repository_keys(
        manifest_path=manifest_path,
        manual_list_path=manual_list_path,
        manual_data_path=manual_data_path,
        projects_yml_path=projects_yml_path,
    )

    assert known["acme/reservoir"] == "Reservoir manifest"
    assert known["acme/manual"] == "manual list"
    assert known["acme/cached"] == "manual metadata"
    assert known["acme/merged"] == "LeanPool/projects.yml"


def test_parse_arxiv_feed_extracts_papers_and_github_links() -> None:
    """The arXiv Atom parser should preserve basic paper metadata."""
    feed = """\
    <feed xmlns="http://www.w3.org/2005/Atom">
      <entry>
        <id>http://arxiv.org/abs/2601.00001v1</id>
        <title>A Lean formalization</title>
        <summary>Code: https://github.com/Acme/Formalization.</summary>
        <published>2026-01-02T03:04:05Z</published>
        <updated>2026-01-03T03:04:05Z</updated>
        <author><name>A. Author</name></author>
      </entry>
    </feed>
    """

    papers = parse_arxiv_feed(feed)

    assert len(papers) == 1
    assert papers[0].identifier == "2601.00001v1"
    assert papers[0].title == "A Lean formalization"
    assert papers[0].authors == ("A. Author",)
    assert papers[0].github_urls == ("https://github.com/Acme/Formalization",)


def test_render_discovery_report_splits_candidate_and_low_signal_repos() -> None:
    """High/medium signal repositories should be separated from low-signal ones."""
    candidate = GitHubRepository(
        key="acme/candidate",
        full_name="acme/candidate",
        html_url="https://github.com/acme/candidate",
        description="candidate",
        stars=4,
        license_spdx="MIT",
        topics=(),
        language="Lean",
        created_at="2026-01-01T00:00:00Z",
        updated_at="2026-01-02T00:00:00Z",
        pushed_at="2026-01-02T00:00:00Z",
        default_branch="main",
        query_matches=(),
        lean_file_count=8,
        lean_bytes=12000,
        score=7,
        signal="high",
        reasons=("Lake/Lean project files", "domain terms: theorem"),
    )
    low_signal = GitHubRepository(
        key="acme/scratch",
        full_name="acme/scratch",
        html_url="https://github.com/acme/scratch",
        description="scratch",
        stars=0,
        license_spdx=None,
        topics=(),
        language="Lean",
        created_at="2026-01-01T00:00:00Z",
        updated_at="2026-01-02T00:00:00Z",
        pushed_at="2026-01-02T00:00:00Z",
        default_branch="main",
        query_matches=(),
        signal="low",
        reasons=("personal terms: scratch",),
    )
    result = DiscoveryResult(
        generated_at=datetime(2026, 1, 3, tzinfo=UTC),
        start_date=date(2026, 1, 1),
        end_date=date(2026, 1, 3),
        github_repositories=(candidate, low_signal),
        arxiv_papers=(
            ArxivPaper(
                identifier="2601.00001",
                title="A Lean paper",
                url="https://arxiv.org/abs/2601.00001",
                published="2026-01-02T00:00:00Z",
                updated="2026-01-02T00:00:00Z",
                authors=("A. Author",),
                summary="summary",
            ),
        ),
        known_repositories_skipped=2,
        github_queries=("language:Lean created:>=2026-01-01 fork:false",),
    )

    report = render_discovery_report(result)

    assert "Found 1 Lean Pool candidate repos" in report
    assert "## Lean Pool candidates" in report
    assert "[acme/candidate](https://github.com/acme/candidate)" in report
    assert "## Other new Lean repositories" in report
    assert "[acme/scratch](https://github.com/acme/scratch)" in report
    assert "[A Lean paper](https://arxiv.org/abs/2601.00001)" in report


def test_update_discovered_file_records_urls_without_duplicates(tmp_path: Path) -> None:
    """Discovered YAML is keyed, so a second write does not duplicate entries."""
    repository = GitHubRepository(
        key="acme/candidate",
        full_name="acme/candidate",
        html_url="https://github.com/acme/candidate",
        description="candidate",
        stars=0,
        license_spdx="MIT",
        topics=("lean4",),
        language="Lean",
        created_at="2026-01-01T00:00:00Z",
        updated_at="2026-01-02T00:00:00Z",
        pushed_at="2026-01-02T00:00:00Z",
        default_branch="main",
        query_matches=("language:Lean created:>=2026-01-01",),
        lean_file_count=8,
        lean_bytes=12000,
        score=7,
        signal="high",
        reasons=("Lake/Lean project files", "domain terms: theorem"),
    )
    paper = ArxivPaper(
        identifier="2601.00001v1",
        title="A Lean paper",
        url="https://arxiv.org/abs/2601.00001v1",
        published="2026-01-02T00:00:00Z",
        updated="2026-01-02T00:00:00Z",
        authors=("A. Author",),
        summary="summary",
        github_urls=("https://github.com/acme/candidate",),
    )
    result = DiscoveryResult(
        generated_at=datetime(2026, 1, 3, tzinfo=UTC),
        start_date=date(2026, 1, 1),
        end_date=date(2026, 1, 3),
        github_repositories=(repository,),
        arxiv_papers=(paper,),
        known_repositories_skipped=0,
    )
    discovered_path = tmp_path / "discovered.yml"

    first_update = update_discovered_file(result, discovered_path)
    second_update = update_discovered_file(result, discovered_path)
    data = yaml.safe_load(discovered_path.read_text())

    assert first_update.added_github == 1
    assert first_update.added_arxiv == 1
    assert second_update.added_github == 0
    assert second_update.added_arxiv == 0
    assert list(data["github"]) == ["acme/candidate"]
    assert data["github"]["acme/candidate"]["url"] == repository.html_url
    assert list(data["arxiv"]) == ["2601.00001v1"]
    assert data["arxiv"]["2601.00001v1"]["url"] == paper.url
    assert data["arxiv"]["2601.00001v1"]["github_urls"] == [
        "https://github.com/acme/candidate"
    ]


def test_repository_score_does_not_depend_on_star_count() -> None:
    """Zero-star and starred projects with the same metadata get the same score."""
    base = GitHubRepository(
        key="acme/candidate",
        full_name="acme/candidate",
        html_url="https://github.com/acme/candidate",
        description="A theorem formalization in Lean.",
        stars=0,
        license_spdx="MIT",
        topics=("lean4",),
        language="Lean",
        created_at="2026-01-01T00:00:00Z",
        updated_at="2026-01-02T00:00:00Z",
        pushed_at="2026-01-02T00:00:00Z",
        default_branch="main",
        query_matches=(),
        has_lakefile=True,
        lean_file_count=8,
        lean_bytes=12000,
    )
    starred = GitHubRepository(**{**base.__dict__, "stars": 10})

    zero_score = _score_repository(base)
    starred_score = _score_repository(starred)

    assert zero_score.score == starred_score.score
    assert zero_score.reasons == starred_score.reasons


def test_http_client_only_attaches_token_to_github_requests() -> None:
    """The GitHub token must not be sent to arXiv."""
    client = _HttpClient("ghs_secret")

    github_request = client._request("https://api.github.com/search/repositories")
    arxiv_request = client._request("https://export.arxiv.org/api/query")

    assert github_request.get_header("Authorization") == "Bearer ghs_secret"
    assert arxiv_request.get_header("Authorization") is None
