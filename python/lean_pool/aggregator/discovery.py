"""Daily discovery of new Lean repositories and arXiv papers.

The existing aggregator tracks Reservoir plus a hand-curated manual
list. This module is a lighter-weight scout for newly created or
recently updated public Lean projects that have not yet reached either
source. It uses the GitHub and arXiv APIs rather than cloning repos, so
it is cheap enough for a scheduled GitHub Actions job.
"""

from __future__ import annotations

import base64
import json
import logging
import os
import re
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import UTC, date, datetime, timedelta
from pathlib import Path
from typing import Any

import yaml

from lean_pool.aggregator.manual import parse_manual_list
from lean_pool.aggregator.render import canonical_key, load_pool_repos, package_key

logger = logging.getLogger(__name__)

GITHUB_API_ROOT = "https://api.github.com"
ARXIV_API_URL = "https://export.arxiv.org/api/query"
DEFAULT_LOOKBACK_DAYS = 1
DEFAULT_MAX_GITHUB_RESULTS_PER_QUERY = 100
DEFAULT_HTTP_TIMEOUT_SECONDS = 30

_LEAN_FILE_EXCLUDE_PARTS = frozenset({".git", ".lake", "build", "lake-packages"})
_PERMISSIVE_LICENSES = frozenset({"Apache-2.0", "MIT"})
_README_NAMES = frozenset({"readme", "readme.md", "readme.txt", "readme.org"})
_LAKEFILE_NAMES = frozenset({"lakefile.lean", "lakefile.toml"})
_GITHUB_URL_RE = re.compile(
    r"https?://github\.com/(?P<owner>[\w.-]+)/(?P<name>[\w.-]+?)(?:\.git)?"
    r"(?:[/?#\s]|$)",
    re.IGNORECASE,
)

_DOMAIN_KEYWORDS = (
    "algebra",
    "analysis",
    "automata",
    "category",
    "combinatorics",
    "compiler",
    "concurrency",
    "crypto",
    "data structure",
    "distributed",
    "elliptic",
    "field theory",
    "formalisation",
    "formalization",
    "geometry",
    "graph",
    "hardware",
    "logic",
    "mathlib",
    "mechanics",
    "modular",
    "number theory",
    "parser",
    "physics",
    "probability",
    "proof",
    "protocol",
    "quantum",
    "ramsey",
    "relativity",
    "semantics",
    "set theory",
    "sieve",
    "theorem",
    "topology",
    "type theory",
    "verification",
    "verified",
)
_TOOL_KEYWORDS = (
    "autograder",
    "automation",
    "doc gen",
    "documentation generator",
    "editor",
    "formatter",
    "lake plugin",
    "linter",
    "lsp",
    "plugin",
    "repl",
    "search",
    "tactic",
)
_EDUCATIONAL_KEYWORDS = (
    "book",
    "course",
    "exercise",
    "game",
    "homework",
    "lecture",
    "solutions",
    "template",
    "tutorial",
    "workshop",
)
_PERSONAL_KEYWORDS = (
    "advent of code",
    "aoc",
    "bug repro",
    "learning lean",
    "mwe",
    "playground",
    "project euler",
    "scratch",
    "sandbox",
)


@dataclass(frozen=True)
class GitHubRepository:
    """Metadata and cheap repository-shape signals from GitHub."""

    key: str
    full_name: str
    html_url: str
    description: str
    stars: int
    license_spdx: str | None
    topics: tuple[str, ...]
    language: str | None
    created_at: str
    updated_at: str
    pushed_at: str
    default_branch: str
    query_matches: tuple[str, ...]
    has_lakefile: bool = False
    has_toolchain: bool = False
    has_manifest: bool = False
    has_readme: bool = False
    lean_file_count: int = 0
    lean_bytes: int = 0
    tree_truncated: bool = False
    readme_excerpt: str = ""
    score: int = 0
    signal: str = "low"
    reasons: tuple[str, ...] = ()


@dataclass(frozen=True)
class ArxivPaper:
    """A recent arXiv entry matching Lean-related search terms."""

    identifier: str
    title: str
    url: str
    published: str
    updated: str
    authors: tuple[str, ...]
    summary: str
    github_urls: tuple[str, ...] = ()


@dataclass(frozen=True)
class DiscoveryResult:
    """Combined result of one discovery run."""

    generated_at: datetime
    start_date: date
    end_date: date
    github_repositories: tuple[GitHubRepository, ...]
    arxiv_papers: tuple[ArxivPaper, ...]
    known_repositories_skipped: int
    github_errors: tuple[str, ...] = ()
    arxiv_errors: tuple[str, ...] = ()
    github_queries: tuple[str, ...] = ()


@dataclass(frozen=True)
class DiscoveryUpdate:
    """Counts from writing newly discovered records to YAML."""

    added_github: int
    added_arxiv: int


@dataclass
class _HttpClient:
    token: str | None
    timeout: float = DEFAULT_HTTP_TIMEOUT_SECONDS

    def json(self, url: str, parameters: dict[str, str] | None = None) -> Any:
        request = self._request(url, parameters)
        with urllib.request.urlopen(request, timeout=self.timeout) as response:
            body = response.read()
        return json.loads(body)

    def text(self, url: str, parameters: dict[str, str] | None = None) -> str:
        request = self._request(url, parameters)
        with urllib.request.urlopen(request, timeout=self.timeout) as response:
            return response.read().decode("utf-8", errors="replace")

    def _request(
        self, url: str, parameters: dict[str, str] | None = None
    ) -> urllib.request.Request:
        if parameters:
            separator = "&" if "?" in url else "?"
            url = f"{url}{separator}{urllib.parse.urlencode(parameters)}"
        headers = {"User-Agent": "lean-pool-discovery"}
        if url.startswith(GITHUB_API_ROOT):
            headers["Accept"] = "application/vnd.github+json"
            headers["X-GitHub-Api-Version"] = "2022-11-28"
            if self.token:
                headers["Authorization"] = f"Bearer {self.token}"
        return urllib.request.Request(url, headers=headers)


def discover(
    *,
    lookback_days: int,
    known_repositories: set[str],
    github_token: str | None,
    include_known: bool = False,
    max_github_results_per_query: int = DEFAULT_MAX_GITHUB_RESULTS_PER_QUERY,
    now: datetime | None = None,
) -> DiscoveryResult:
    """Run GitHub and arXiv discovery for the requested lookback window.

    Args:
        lookback_days: Number of days to scan, counting back from ``now``.
        known_repositories: Canonical GitHub keys already tracked locally.
        github_token: Token for authenticated GitHub API calls. ``None``
            works at lower rate limits.
        include_known: Keep already-tracked repositories in the report.
        max_github_results_per_query: Repository-search cap per query.
        now: Optional clock override for tests.

    Returns:
        The combined discovery result.
    """
    if lookback_days < 1:
        raise ValueError("lookback_days must be at least 1")
    generated_at = now or datetime.now(UTC)
    start_date = (generated_at - timedelta(days=lookback_days)).date()
    end_date = generated_at.date()
    client = _HttpClient(github_token)

    repositories, skipped, github_errors, queries = _discover_github(
        client=client,
        start_date=start_date,
        known_repositories=known_repositories,
        include_known=include_known,
        max_results_per_query=max_github_results_per_query,
    )
    papers, arxiv_errors = _discover_arxiv(
        client=client, start_date=start_date, end_date=end_date
    )

    return DiscoveryResult(
        generated_at=generated_at,
        start_date=start_date,
        end_date=end_date,
        github_repositories=tuple(repositories),
        arxiv_papers=tuple(papers),
        known_repositories_skipped=skipped,
        github_errors=tuple(github_errors),
        arxiv_errors=tuple(arxiv_errors),
        github_queries=tuple(queries),
    )


def load_known_repository_keys(
    *,
    manifest_path: Path,
    manual_list_path: Path,
    manual_data_path: Path,
    projects_yml_path: Path,
) -> dict[str, str]:
    """Load locally tracked GitHub repository keys and their source labels.

    Args:
        manifest_path: Reservoir manifest JSON path.
        manual_list_path: Hand-maintained GitHub URL list.
        manual_data_path: Cached manual package metadata.
        projects_yml_path: Lean Pool project registry.

    Returns:
        Mapping from canonical ``owner/name`` key to a short source label.
    """
    known: dict[str, str] = {}
    _load_manifest_keys(manifest_path, known)
    _load_manual_list_keys(manual_list_path, known)
    _load_manual_data_keys(manual_data_path, known)
    for key in load_pool_repos(projects_yml_path):
        known.setdefault(key, "LeanPool/projects.yml")
    return known


def parse_arxiv_feed(feed_text: str) -> list[ArxivPaper]:
    """Parse an arXiv Atom feed into Lean-related paper records.

    Args:
        feed_text: Raw Atom XML returned by the arXiv API.

    Returns:
        A list of arXiv paper records in feed order.
    """
    root = ET.fromstring(feed_text)
    namespace = {"atom": "http://www.w3.org/2005/Atom"}
    papers: list[ArxivPaper] = []
    for entry in root.findall("atom:entry", namespace):
        url = _xml_text(entry, "atom:id", namespace)
        title = _collapse_whitespace(_xml_text(entry, "atom:title", namespace))
        summary = _collapse_whitespace(_xml_text(entry, "atom:summary", namespace))
        authors = tuple(
            _collapse_whitespace(_xml_text(author, "atom:name", namespace))
            for author in entry.findall("atom:author", namespace)
        )
        papers.append(
            ArxivPaper(
                identifier=url.rsplit("/", 1)[-1],
                title=title,
                url=url,
                published=_xml_text(entry, "atom:published", namespace),
                updated=_xml_text(entry, "atom:updated", namespace),
                authors=authors,
                summary=summary,
                github_urls=tuple(_extract_github_urls(f"{title} {summary}")),
            )
        )
    return papers


def render_discovery_report(result: DiscoveryResult) -> str:
    """Render one discovery result as a compact private report.

    Args:
        result: The discovery data to render.

    Returns:
        Markdown suitable for an email body.
    """
    lines = [
        "# Daily Lean project discovery",
        "",
        f"Generated: {result.generated_at.isoformat(timespec='seconds')}",
        f"Window: {result.start_date.isoformat()} through "
        f"{result.end_date.isoformat()} UTC",
        "",
        _summary_line(result),
        "",
        "## Lean Pool candidates",
        "",
    ]
    candidates = [repo for repo in result.github_repositories if repo.signal != "low"]
    lines.extend(_repository_table(candidates, limit=30))
    lines.extend(["", "## Other new Lean repositories", ""])
    other_repos = [repo for repo in result.github_repositories if repo.signal == "low"]
    lines.extend(_repository_table(other_repos, limit=40))
    lines.extend(["", "## arXiv matches", ""])
    lines.extend(_arxiv_table(result.arxiv_papers, limit=30))
    lines.extend(["", "## GitHub search queries", ""])
    lines.extend(f"- `{query}`" for query in result.github_queries)
    if result.github_errors or result.arxiv_errors:
        lines.extend(["", "## API warnings", ""])
        lines.extend(f"- GitHub: {error}" for error in result.github_errors)
        lines.extend(f"- arXiv: {error}" for error in result.arxiv_errors)
    lines.append("")
    return "\n".join(lines)


def save_discovery_report(report: str, path: Path) -> None:
    """Write a discovery report, creating parent directories as needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(report)


def update_discovered_file(result: DiscoveryResult, path: Path) -> DiscoveryUpdate:
    """Add newly discovered GitHub and arXiv records to a YAML index.

    The YAML file is keyed by stable identifiers rather than append-only
    rows, so repeated daily runs do not create duplicate entries or churn
    existing records. Existing records are left unchanged.

    Args:
        result: Discovery data from one run.
        path: YAML file to update.

    Returns:
        Counts of newly added GitHub repositories and arXiv papers.
    """
    data = _load_discovered_file(path)
    github = data["github"]
    arxiv = data["arxiv"]
    seen_at = result.generated_at.isoformat(timespec="seconds")

    added_github = 0
    for repository in result.github_repositories:
        if repository.key in github:
            continue
        github[repository.key] = _repository_record(repository, seen_at)
        added_github += 1

    added_arxiv = 0
    for paper in result.arxiv_papers:
        if paper.identifier in arxiv:
            continue
        arxiv[paper.identifier] = _arxiv_record(paper, seen_at)
        added_arxiv += 1

    if added_github or added_arxiv or not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(_dump_discovered_file(data))
    return DiscoveryUpdate(added_github=added_github, added_arxiv=added_arxiv)


def _load_discovered_file(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"version": 1, "github": {}, "arxiv": {}}
    loaded = yaml.safe_load(path.read_text()) or {}
    if not isinstance(loaded, dict):
        raise ValueError(f"{path} must contain a YAML mapping")
    github = loaded.setdefault("github", {})
    arxiv = loaded.setdefault("arxiv", {})
    loaded.setdefault("version", 1)
    if not isinstance(github, dict):
        raise ValueError(f"{path}: `github` must be a mapping")
    if not isinstance(arxiv, dict):
        raise ValueError(f"{path}: `arxiv` must be a mapping")
    return loaded


def _dump_discovered_file(data: dict[str, Any]) -> str:
    normalized = {
        "version": data.get("version", 1),
        "github": dict(sorted((data.get("github") or {}).items())),
        "arxiv": dict(sorted((data.get("arxiv") or {}).items())),
    }
    return yaml.safe_dump(
        normalized,
        allow_unicode=False,
        sort_keys=False,
        width=88,
    )


def _repository_record(repository: GitHubRepository, seen_at: str) -> dict[str, Any]:
    return {
        "url": repository.html_url,
        "first_seen_at": seen_at,
        "full_name": repository.full_name,
        "description": repository.description,
        "signal": repository.signal,
        "score": repository.score,
        "reasons": list(repository.reasons),
        "stars": repository.stars,
        "license": repository.license_spdx,
        "topics": list(repository.topics),
        "language": repository.language,
        "created_at": repository.created_at,
        "updated_at": repository.updated_at,
        "pushed_at": repository.pushed_at,
        "default_branch": repository.default_branch,
        "has_lakefile": repository.has_lakefile,
        "has_toolchain": repository.has_toolchain,
        "has_manifest": repository.has_manifest,
        "has_readme": repository.has_readme,
        "lean_file_count": repository.lean_file_count,
        "estimated_lean_loc": _estimated_loc(repository.lean_bytes),
        "tree_truncated": repository.tree_truncated,
        "query_matches": list(repository.query_matches),
    }


def _arxiv_record(paper: ArxivPaper, seen_at: str) -> dict[str, Any]:
    return {
        "url": paper.url,
        "first_seen_at": seen_at,
        "title": paper.title,
        "authors": list(paper.authors),
        "published": paper.published,
        "updated": paper.updated,
        "summary": paper.summary,
        "github_urls": list(paper.github_urls),
    }


def _discover_github(
    *,
    client: _HttpClient,
    start_date: date,
    known_repositories: set[str],
    include_known: bool,
    max_results_per_query: int,
) -> tuple[list[GitHubRepository], int, list[str], list[str]]:
    queries = _github_queries(start_date)
    items_by_key: dict[str, tuple[dict, set[str]]] = {}
    errors: list[str] = []
    for query in queries:
        for item in _search_github_repositories(
            client, query, max_results=max_results_per_query, errors=errors
        ):
            key = _key_from_repository_item(item)
            if key is None:
                continue
            existing = items_by_key.setdefault(key, (item, set()))
            existing[1].add(query)

    repositories: list[GitHubRepository] = []
    skipped = 0
    for key, (item, matched_queries) in items_by_key.items():
        if key in known_repositories and not include_known:
            skipped += 1
            continue
        repository = _repository_from_item(item, key, tuple(sorted(matched_queries)))
        repository = _enrich_repository(client, repository, errors)
        repositories.append(_score_repository(repository))

    repositories.sort(
        key=lambda repo: (
            repo.score,
            repo.stars,
            repo.pushed_at,
            repo.full_name.lower(),
        ),
        reverse=True,
    )
    return repositories, skipped, errors, queries


def _github_queries(start_date: date) -> list[str]:
    since = start_date.isoformat()
    # Filter on `created:` only. A `pushed:` filter would re-surface old,
    # already-established repos every time they receive a single commit
    # (e.g. mathlib, teorth/pfr), which is noise: we only want repos that
    # are genuinely new within the lookback window.
    return [
        f"language:Lean created:>={since} fork:false archived:false",
        f"topic:lean4 created:>={since} fork:false archived:false",
        f"topic:lean created:>={since} fork:false archived:false",
        f'"Lean 4" created:>={since} fork:false archived:false',
        f"mathlib created:>={since} fork:false archived:false",
    ]


def _search_github_repositories(
    client: _HttpClient,
    query: str,
    *,
    max_results: int,
    errors: list[str],
) -> list[dict]:
    items: list[dict] = []
    page = 1
    per_page = min(100, max_results)
    while len(items) < max_results:
        try:
            payload = client.json(
                f"{GITHUB_API_ROOT}/search/repositories",
                {
                    "q": query,
                    "sort": "updated",
                    "order": "desc",
                    "per_page": str(per_page),
                    "page": str(page),
                },
            )
        except (OSError, urllib.error.HTTPError, json.JSONDecodeError) as exc:
            errors.append(f"{query}: {exc}")
            break
        page_items = payload.get("items") or []
        items.extend(page_items[: max_results - len(items)])
        if len(page_items) < per_page:
            break
        page += 1
    return items


def _repository_from_item(
    item: dict[str, Any], key: str, query_matches: tuple[str, ...]
) -> GitHubRepository:
    license_block = item.get("license") or {}
    owner, _, name = item.get("full_name", key).partition("/")
    return GitHubRepository(
        key=key,
        full_name=item.get("full_name") or f"{owner}/{name}",
        html_url=item.get("html_url") or f"https://github.com/{owner}/{name}",
        description=item.get("description") or "",
        stars=int(item.get("stargazers_count") or 0),
        license_spdx=license_block.get("spdx_id"),
        topics=tuple(item.get("topics") or []),
        language=item.get("language"),
        created_at=item.get("created_at") or "",
        updated_at=item.get("updated_at") or "",
        pushed_at=item.get("pushed_at") or "",
        default_branch=item.get("default_branch") or "main",
        query_matches=query_matches,
    )


def _enrich_repository(
    client: _HttpClient, repository: GitHubRepository, errors: list[str]
) -> GitHubRepository:
    owner, _, name = repository.full_name.partition("/")
    tree_url = (
        f"{GITHUB_API_ROOT}/repos/{urllib.parse.quote(owner, safe='')}/"
        f"{urllib.parse.quote(name, safe='')}/git/trees/"
        f"{urllib.parse.quote(repository.default_branch, safe='')}"
    )
    try:
        tree = client.json(tree_url, {"recursive": "1"})
    except (OSError, urllib.error.HTTPError, json.JSONDecodeError) as exc:
        errors.append(f"{repository.full_name}: tree fetch failed: {exc}")
        return repository

    paths = tree.get("tree") or []
    lean_file_count, lean_bytes = _lean_tree_size(paths)
    root_names = {
        str(entry.get("path", "")).lower()
        for entry in paths
        if "/" not in str(entry.get("path", ""))
    }
    has_readme = bool(root_names & _README_NAMES)
    readme_excerpt = _fetch_readme_excerpt(client, repository) if has_readme else ""
    return GitHubRepository(
        **{
            **repository.__dict__,
            "has_lakefile": bool(root_names & _LAKEFILE_NAMES),
            "has_toolchain": "lean-toolchain" in root_names,
            "has_manifest": "lake-manifest.json" in root_names,
            "has_readme": has_readme,
            "lean_file_count": lean_file_count,
            "lean_bytes": lean_bytes,
            "tree_truncated": bool(tree.get("truncated")),
            "readme_excerpt": readme_excerpt,
        }
    )


def _fetch_readme_excerpt(client: _HttpClient, repository: GitHubRepository) -> str:
    owner, _, name = repository.full_name.partition("/")
    url = (
        f"{GITHUB_API_ROOT}/repos/{urllib.parse.quote(owner, safe='')}/"
        f"{urllib.parse.quote(name, safe='')}/readme"
    )
    try:
        payload = client.json(url)
    except (OSError, urllib.error.HTTPError, json.JSONDecodeError):
        return ""
    if not isinstance(payload, dict):
        return ""
    content = payload.get("content")
    if not isinstance(content, str):
        return ""
    try:
        decoded = base64.b64decode(content).decode("utf-8", errors="replace")
    except ValueError:
        return ""
    return _collapse_whitespace(decoded[:6000])


def _lean_tree_size(paths: list[dict]) -> tuple[int, int]:
    count = 0
    total_bytes = 0
    for entry in paths:
        path = str(entry.get("path") or "")
        if not path.endswith(".lean"):
            continue
        if any(part in _LEAN_FILE_EXCLUDE_PARTS for part in path.split("/")):
            continue
        count += 1
        total_bytes += int(entry.get("size") or 0)
    return count, total_bytes


def _score_repository(repository: GitHubRepository) -> GitHubRepository:
    text = " ".join(
        [
            repository.full_name,
            repository.description,
            " ".join(repository.topics),
            repository.readme_excerpt[:2000],
        ]
    ).lower()
    score = 0
    reasons: list[str] = []

    score += _project_shape_score(repository, reasons)
    score += _license_score(repository, reasons)
    score += _domain_score(text, reasons)
    score += _exclusion_score(text, reasons)

    if score >= 6:
        signal = "high"
    elif score >= 3:
        signal = "medium"
    else:
        signal = "low"
    return GitHubRepository(
        **{
            **repository.__dict__,
            "score": score,
            "signal": signal,
            "reasons": tuple(reasons),
        }
    )


def _project_shape_score(repository: GitHubRepository, reasons: list[str]) -> int:
    score = 0
    if repository.has_lakefile or repository.has_toolchain:
        score += 2
        reasons.append("Lake/Lean project files")
    if repository.lean_file_count:
        score += 1
        reasons.append(f"{repository.lean_file_count} Lean files")
    estimated_loc = _estimated_loc(repository.lean_bytes)
    if estimated_loc >= 250:
        score += 2
        reasons.append(f"about {estimated_loc} Lean LOC")
    elif estimated_loc >= 100:
        score += 1
        reasons.append(f"about {estimated_loc} Lean LOC")
    if repository.has_manifest:
        score += 1
        reasons.append("Lake manifest")
    if repository.tree_truncated:
        reasons.append("large tree")
    return score


def _license_score(repository: GitHubRepository, reasons: list[str]) -> int:
    if repository.license_spdx in _PERMISSIVE_LICENSES:
        reasons.append(repository.license_spdx or "")
        return 1
    if repository.license_spdx:
        reasons.append(f"license {repository.license_spdx}")
        return -1
    reasons.append("license unknown")
    return 0


def _domain_score(text: str, reasons: list[str]) -> int:
    matches = _keyword_matches(text, _DOMAIN_KEYWORDS)
    if not matches:
        return 0
    reasons.append("domain terms: " + ", ".join(matches[:3]))
    return 2


def _exclusion_score(text: str, reasons: list[str]) -> int:
    penalty = 0
    for label, keywords in (
        ("tool", _TOOL_KEYWORDS),
        ("educational", _EDUCATIONAL_KEYWORDS),
        ("personal", _PERSONAL_KEYWORDS),
    ):
        matches = _keyword_matches(text, keywords)
        if matches:
            reasons.append(f"{label} terms: {', '.join(matches[:2])}")
            penalty -= 3
    return penalty


def _keyword_matches(text: str, keywords: tuple[str, ...]) -> list[str]:
    return [keyword for keyword in keywords if keyword in text]


def _estimated_loc(lean_bytes: int) -> int:
    if lean_bytes <= 0:
        return 0
    return max(1, round(lean_bytes / 36))


def _discover_arxiv(
    *, client: _HttpClient, start_date: date, end_date: date
) -> tuple[list[ArxivPaper], list[str]]:
    search_query = _arxiv_query(start_date, end_date)
    try:
        feed = client.text(
            ARXIV_API_URL,
            {
                "search_query": search_query,
                "sortBy": "submittedDate",
                "sortOrder": "descending",
                "start": "0",
                "max_results": "50",
            },
        )
    except (OSError, urllib.error.HTTPError) as exc:
        return [], [str(exc)]
    try:
        return parse_arxiv_feed(feed), []
    except ET.ParseError as exc:
        return [], [f"could not parse arXiv response: {exc}"]


def _arxiv_query(start_date: date, end_date: date) -> str:
    start = start_date.strftime("%Y%m%d") + "0000"
    end = end_date.strftime("%Y%m%d") + "2359"
    lean_terms = (
        'all:"Lean 4"',
        'all:"Lean theorem prover"',
        'all:"formalized in Lean"',
        'all:"formalised in Lean"',
        'all:"formalization in Lean"',
        'all:"formalisation in Lean"',
        "all:mathlib",
    )
    return f"({' OR '.join(lean_terms)}) AND submittedDate:[{start} TO {end}]"


def _load_manifest_keys(path: Path, known: dict[str, str]) -> None:
    if not path.is_file():
        return
    try:
        manifest = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        logger.warning("%s: invalid JSON: %s", path, exc)
        return
    for package in manifest.get("packages") or []:
        key = package_key(package)
        if key:
            known.setdefault(key, "Reservoir manifest")


def _load_manual_list_keys(path: Path, known: dict[str, str]) -> None:
    if not path.is_file():
        return
    try:
        entries = parse_manual_list(path)
    except ValueError as exc:
        logger.warning("%s", exc)
        return
    for owner, name in entries:
        known.setdefault(canonical_key(owner, name), "manual list")


def _load_manual_data_keys(path: Path, known: dict[str, str]) -> None:
    if not path.is_file():
        return
    try:
        packages = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        logger.warning("%s: invalid JSON: %s", path, exc)
        return
    for package in packages:
        key = package_key(package)
        if key:
            known.setdefault(key, "manual metadata")


def _key_from_repository_item(item: dict[str, Any]) -> str | None:
    full_name = item.get("full_name")
    if not isinstance(full_name, str) or "/" not in full_name:
        return None
    owner, _, name = full_name.partition("/")
    return canonical_key(owner, name)


def _extract_github_urls(text: str) -> list[str]:
    urls: list[str] = []
    seen: set[str] = set()
    for match in _GITHUB_URL_RE.finditer(text):
        owner = match["owner"]
        name = match["name"].rstrip(".,;:)]}")
        key = canonical_key(owner, name)
        if key in seen:
            continue
        seen.add(key)
        urls.append(f"https://github.com/{owner}/{name}")
    return urls


def _xml_text(element: ET.Element, path: str, namespace: dict[str, str]) -> str:
    child = element.find(path, namespace)
    return child.text.strip() if child is not None and child.text else ""


def _collapse_whitespace(text: str) -> str:
    return " ".join(text.split())


def _summary_line(result: DiscoveryResult) -> str:
    candidates = sum(1 for repo in result.github_repositories if repo.signal != "low")
    return (
        f"Found {candidates} Lean Pool candidate repos, "
        f"{len(result.github_repositories)} untracked GitHub repos total, "
        f"{len(result.arxiv_papers)} arXiv matches, and skipped "
        f"{result.known_repositories_skipped} already-tracked repos."
    )


def _repository_table(repositories: list[GitHubRepository], *, limit: int) -> list[str]:
    if not repositories:
        return ["No matches."]
    rows = [
        "| Signal | Repo | Stars | License | Lean size | Created | Pushed | Reasons |",
        "| --- | --- | ---: | --- | ---: | --- | --- | --- |",
    ]
    for repository in repositories[:limit]:
        rows.append(_repository_row(repository))
    if len(repositories) > limit:
        rows.append(
            f"|  | _{len(repositories) - limit} more omitted_ |  |  |  |  |  |  |"
        )
    return rows


def _repository_row(repository: GitHubRepository) -> str:
    license_name = repository.license_spdx or ""
    estimated_loc = _estimated_loc(repository.lean_bytes)
    lean_size = f"{repository.lean_file_count} files / ~{estimated_loc} LOC"
    reasons = _truncate("; ".join(repository.reasons), 220)
    return (
        f"| {repository.signal} | [{_escape_cell(repository.full_name)}]"
        f"({repository.html_url}) | {repository.stars} | {_escape_cell(license_name)}"
        f" | {_escape_cell(lean_size)} | {_date_cell(repository.created_at)}"
        f" | {_date_cell(repository.pushed_at)} | {_escape_cell(reasons)} |"
    )


def _arxiv_table(papers: tuple[ArxivPaper, ...], *, limit: int) -> list[str]:
    if not papers:
        return ["No matches."]
    rows = [
        "| Paper | Authors | Published | GitHub links |",
        "| --- | --- | --- | --- |",
    ]
    for paper in papers[:limit]:
        authors = ", ".join(paper.authors[:3])
        if len(paper.authors) > 3:
            authors += " et al."
        github_links = "<br>".join(paper.github_urls) if paper.github_urls else ""
        rows.append(
            f"| [{_escape_cell(_truncate(paper.title, 100))}]({paper.url})"
            f" | {_escape_cell(authors)} | {_date_cell(paper.published)}"
            f" | {_escape_cell(github_links)} |"
        )
    if len(papers) > limit:
        rows.append(f"| _{len(papers) - limit} more omitted_ |  |  |  |")
    return rows


def _escape_cell(value: str) -> str:
    return value.replace("|", r"\|").replace("\n", " ")


def _truncate(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    return text[: limit - 1].rstrip() + "."


def _date_cell(value: str) -> str:
    return value[:10] if value else ""


def github_token_from_environment() -> str | None:
    """Return the GitHub token exposed by Actions or local shells."""
    return os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
