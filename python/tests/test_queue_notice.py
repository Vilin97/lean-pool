"""Queued content and generated attribution retain separate source checks."""

import subprocess

import pytest
import yaml

from lean_pool import notice, queue_notice


def test_bad_submitted_attribution_is_rejected(tmp_path):
    """Regeneration cannot conceal an incorrect NOTICE submitted by a PR."""
    (tmp_path / "LeanPool").mkdir()
    (tmp_path / "LeanPool/projects.yml").write_text(
        yaml.safe_dump({"projects": [_card("a")]})
    )
    (tmp_path / "NOTICE.extra.yml").write_text("{}\n")
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.name", "Test")
    _git(tmp_path, "config", "user.email", "test@example.org")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "base")
    with pytest.raises(ValueError, match="does not match"):
        queue_notice.validate_snapshot(tmp_path, "HEAD", "Missing attribution\n")


def _card(name):
    return {
        "slug": name,
        "entry_module": f"LeanPool.{name.upper()}",
        "license": "MIT",
        "source": {"github_repo": f"example/{name}"},
    }


def _git(root, *arguments):
    return subprocess.check_output(["git", *arguments], cwd=root, text=True).strip()


def test_combined_queue_checks_submitted_snapshot_then_all_new_projects(
    tmp_path, monkeypatch
):
    """A correct metadata PR remains valid when independent content precedes it."""
    (tmp_path / "LeanPool").mkdir()
    registry = tmp_path / "LeanPool/projects.yml"
    registry.write_text(yaml.safe_dump({"projects": [_card("a")]}))
    extra = tmp_path / "NOTICE.extra.yml"
    extra.write_text("{}\n")
    path = tmp_path / "NOTICE"
    path.write_text(notice.build(tmp_path))
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.name", "Test")
    _git(tmp_path, "config", "user.email", "test@example.org")
    _git(tmp_path, "remote", "add", "origin", str(tmp_path))
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "base")
    base = _git(tmp_path, "rev-parse", "HEAD")
    extra.write_text("A:\n  note: Additional upstream attribution\n")
    path.write_text(notice.build(tmp_path))
    submitted = path.read_text()
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "Refresh attribution")
    submitted_head = _git(tmp_path, "rev-parse", "HEAD")
    _git(tmp_path, "checkout", "-b", "queue", base)
    registry.write_text(yaml.safe_dump({"projects": [_card("a"), _card("b")]}))
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "Add project (#2)")
    extra.write_text("A:\n  note: Additional upstream attribution\n")
    path.write_text(submitted)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "Refresh attribution (#1)")
    head = _git(tmp_path, "rev-parse", "HEAD")
    monkeypatch.setattr(
        queue_notice,
        "github_json",
        lambda _: {
            "head": {"sha": submitted_head},
            "base": {"repo": {"full_name": "owner/repo"}, "ref": "main"},
        },
    )
    queue_notice.prepare(tmp_path, "owner/repo", base, head)
    assert path.read_text() == notice.build(tmp_path)
    assert "https://github.com/example/b" in path.read_text()
    assert "Additional upstream attribution" in path.read_text()


@pytest.mark.parametrize("authored", ["inherited", "valid", "invalid"])
@pytest.mark.parametrize("event", ["pull_request", "main_push"])
def test_ordinary_pr_preparation_preserves_the_attribution_gate(
    tmp_path, authored, event, monkeypatch
):
    """An inherited stale NOTICE does not block Python, but a bad edit still fails."""
    (tmp_path / "LeanPool").mkdir()
    registry = tmp_path / "LeanPool/projects.yml"
    registry.write_text(yaml.safe_dump({"projects": [_card("a")]}))
    extra = tmp_path / "NOTICE.extra.yml"
    extra.write_text("{}\n")
    path = tmp_path / "NOTICE"
    path.write_text(notice.build(tmp_path))
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.name", "Test")
    _git(tmp_path, "config", "user.email", "test@example.org")
    _git(tmp_path, "remote", "add", "origin", str(tmp_path))
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "base")
    base = _git(tmp_path, "rev-parse", "HEAD")
    (tmp_path / "tool.py").write_text("print('update')\n")
    if authored == "valid":
        extra.write_text("A:\n  note: Additional upstream attribution\n")
        path.write_text(notice.build(tmp_path))
    elif authored == "invalid":
        path.write_text("Missing attribution\n")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "Python or metadata PR")
    submitted = _git(tmp_path, "rev-parse", "HEAD")
    _git(tmp_path, "checkout", "-b", "main-view", base)
    registry.write_text(yaml.safe_dump({"projects": [_card("a"), _card("b")]}))
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "Accept independent project")
    current_main = _git(tmp_path, "rev-parse", "HEAD")
    _git(tmp_path, "merge", "--no-edit", submitted)
    before = path.read_text()
    assert before != notice.build(tmp_path)
    monkeypatch.setattr(
        queue_notice,
        "github_json",
        lambda _: [
            {
                "merged_at": "now",
                "merge_commit_sha": _git(tmp_path, "rev-parse", "HEAD"),
                "head": {"sha": submitted},
                "base": {"ref": "main", "repo": {"full_name": "owner/repo"}},
            }
        ],
    )

    def prepare():
        if event == "pull_request":
            queue_notice.prepare_pull_request(tmp_path, current_main, submitted)
        else:
            queue_notice.prepare_main_push(
                tmp_path,
                "owner/repo",
                current_main,
                _git(tmp_path, "rev-parse", "HEAD"),
            )

    if authored == "invalid":
        with pytest.raises(ValueError, match="does not match"):
            prepare()
        assert path.read_text() == before
    else:
        prepare()
        assert path.read_text() == notice.build(tmp_path)
        assert "https://github.com/example/b" in path.read_text()
        assert _git(tmp_path, "show", "HEAD:NOTICE") + "\n" == before


@pytest.mark.parametrize("valid", [True, False])
def test_main_push_checks_ordinary_commit_without_pr_title(
    tmp_path, monkeypatch, valid
):
    """A direct main commit needs no PR lookup, but must preserve attribution."""
    (tmp_path / "LeanPool").mkdir()
    registry = tmp_path / "LeanPool/projects.yml"
    registry.write_text(yaml.safe_dump({"projects": [_card("a")]}))
    (tmp_path / "NOTICE.extra.yml").write_text("{}\n")
    path = tmp_path / "NOTICE"
    path.write_text(notice.build(tmp_path))
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.name", "Test")
    _git(tmp_path, "config", "user.email", "test@example.org")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "base")
    base = _git(tmp_path, "rev-parse", "HEAD")
    registry.write_text(yaml.safe_dump({"projects": [_card("a"), _card("b")]}))
    path.write_text(notice.build(tmp_path) if valid else "Missing attribution\n")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "Add project and attribution")
    calls = []

    def associated_pulls(endpoint):
        calls.append(endpoint)
        return []

    monkeypatch.setattr(queue_notice, "github_json", associated_pulls)
    if valid:
        queue_notice.prepare_main_push(tmp_path, "owner/repo", base, "HEAD")
        assert not calls
        assert path.read_text() == notice.build(tmp_path)
    else:
        with pytest.raises(ValueError, match="does not match"):
            queue_notice.prepare_main_push(tmp_path, "owner/repo", base, "HEAD")
        assert path.read_text() == "Missing attribution\n"
