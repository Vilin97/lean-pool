"""Tests for deterministic repository quality checks."""

from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

from lean_pool.quality import (
    _axiom_audit_missing,
    _axiom_audit_resolved,
    _Declaration,
    _parse_declarations,
    _strip_lean_comments,
    run_checks,
)

HEADER = """/-
Copyright (c) 2026 Test Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Test Author
-/
"""


def _write_minimal_repo(root: Path, basic_body: str = 'def hello := "world"\n') -> None:
    """Create the smallest LeanPool tree accepted by static checks."""
    (root / "LeanPool").mkdir()
    (root / "LeanPool.lean").write_text("import LeanPool.Basic\n")
    (root / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{basic_body}")
    (root / "LeanPool" / "projects.yml").write_text("projects: []\n")
    (root / "lakefile.toml").write_text(
        'name = "lean-pool"\nversion = "0.1.0"\ndefaultTargets = ["LeanPool"]\n'
    )


def _write_project_yaml(root: Path, projects: list[dict[str, str]]) -> None:
    """Write a `projects.yml` containing the given project entries.

    Each entry uses an `arxiv` source and the `[test]` tag set by default.
    """
    lines = ["projects:"]
    for project in projects:
        lines.extend(
            [
                f"  - slug: {project['slug']}",
                f"    title: {project.get('title', 'Test Project')}",
                f"    entry_module: {project['entry_module']}",
                "    authors: [Test Author]",
                "    source:",
                f'      arxiv: "{project.get("arxiv", "1234.5678")}"',
                f"    status: {project.get('status', 'verified')}",
                "    main_declarations: [hello]",
                "    tags: [test]",
            ]
        )
    (root / "LeanPool" / "projects.yml").write_text("\n".join(lines) + "\n")


def test_strip_lean_comments_preserves_code_not_comments() -> None:
    """Forbidden tokens in comments and strings are ignored."""
    stripped = _strip_lean_comments(
        "-- set_option maxHeartbeats 0\n"
        'def label := "sorry"\n'
        "/- admit -/\n"
        "def safe := 1\n"
    )

    assert "set_option" not in stripped
    assert "sorry" not in stripped
    assert "admit" not in stripped
    assert "def safe := 1" in stripped


def test_minimal_repo_passes_static_quality_checks(tmp_path: Path) -> None:
    """A compliant minimal repo passes without invoking Lean."""
    _write_minimal_repo(tmp_path)

    assert run_checks(tmp_path, skip_lean_axioms=True) == []


def test_quality_check_rejects_set_option(tmp_path: Path) -> None:
    """Lean files may not override options locally."""
    _write_minimal_repo(tmp_path, "set_option maxHeartbeats 0\n\ndef hello := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("set_option is forbidden" in error.message for error in errors)


def test_quality_check_rejects_unreachable_lean_file(tmp_path: Path) -> None:
    """Every Lean file under LeanPool must be imported by LeanPool.lean."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "Extra.lean").write_text(f"{HEADER}\ndef extra := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("not reachable" in error.message for error in errors)


def test_quality_check_rejects_missing_project_metadata(tmp_path: Path) -> None:
    """Project metadata is required even before there are projects."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "projects.yml").unlink()

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("missing LeanPool/projects.yml" in error.message for error in errors)


def test_quality_check_finds_prefixed_declarations(tmp_path: Path) -> None:
    """The axiom audit declaration parser handles common Lean prefixes."""
    _write_minimal_repo(
        tmp_path,
        "@[simp] theorem decorated_identity (n : Nat) : n = n := rfl\n",
    )

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "decorated_identity" for declaration in declarations)


def test_quality_check_parses_declaration_with_prime_suffix(tmp_path: Path) -> None:
    r"""Trailing primes must survive declaration parsing.

    Regression: the original regex used `\b` after `[A-Za-z_][A-Za-z0-9_'.]*`,
    but `\b` does not treat `'` as a word character, so `lemma foo'` was
    parsed as `foo` and the subsequent `#print axioms` audit failed with
    `unknown constant`.
    """
    _write_minimal_repo(tmp_path, "theorem foo' (n : Nat) : n = n := rfl\n")

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "foo'" for declaration in declarations)
    assert not any(declaration.name == "foo" for declaration in declarations)


def test_quality_check_parses_unicode_declaration_name(tmp_path: Path) -> None:
    """Unicode in declaration names (subscripts, Greek) must not be truncated.

    Regression: an ASCII-only `[A-Za-z0-9_'.]` name pattern parsed `c₀_pos`
    as `c`, so the `#print axioms` audit then failed with `unknown constant`.
    """
    _write_minimal_repo(tmp_path, "theorem c₀_pos (n : Nat) : n = n := rfl\n")

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "c₀_pos" for declaration in declarations)
    assert not any(declaration.name == "c" for declaration in declarations)


def test_quality_check_strips_root_escape_from_declaration_name(tmp_path: Path) -> None:
    """`theorem _root_.Foo.bar` is recorded as `Foo.bar`, not the escaped form.

    Regression: the escape prefix was kept, so the audit emitted
    `#print axioms _root_._root_.Foo.bar` and failed.
    """
    _write_minimal_repo(
        tmp_path,
        "namespace Ns\ntheorem _root_.Foo.bar : True := trivial\nend Ns\n",
    )

    names = {declaration.name for declaration in _parse_declarations(tmp_path)}

    assert "Foo.bar" in names
    assert "_root_.Foo.bar" not in names
    assert "Ns.Foo.bar" not in names


def test_quality_check_rejects_oversized_file(tmp_path: Path) -> None:
    """Files over the 10000-line cap fail; there is no waiver."""
    _write_minimal_repo(tmp_path)
    body = "def x := 0\n" * 10001
    (tmp_path / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{body}")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("limit is 10000" in error.message for error in errors)


def test_quality_check_does_not_honor_size_marker(tmp_path: Path) -> None:
    """The old `-- size-limit-ok:` waiver is gone: the marker has no effect."""
    _write_minimal_repo(tmp_path)
    body = "-- size-limit-ok: should be ignored\n" + "def x := 0\n" * 10001
    (tmp_path / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{body}")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("limit is 10000" in error.message for error in errors)


def test_quality_check_accepts_project_card_after_imports(tmp_path: Path) -> None:
    """Regression test for e161b8c: project card may follow imports.

    Mathlib convention places imports between the file header and the module
    docstring. The earlier check required the docstring at byte offset 0 of the
    body and rejected this layout.
    """
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
    )
    card = (
        "/-!\n"
        "# Test Project\n"
        "\n"
        "Source: arxiv:1234.5678\n"
        "Authors: Test Author\n"
        "Status: verified\n"
        "Main declarations: `hello`\n"
        "Tags: test\n"
        "-/\n"
    )
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.Basic\n\n{card}\ndef hello : Nat := 1\n"
    )
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj"}])

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    # The project-card position check must accept this layout. (lake env lean
    # for the declarations check fails in the test sandbox; that's unrelated.)
    assert not any("project card for p is out of date" in e.message for e in errors)


def test_quality_check_falls_back_when_lake_missing(tmp_path: Path) -> None:
    """A missing `lake` binary yields a single advisory error, not a crash.

    The python_ci job runs without a Lean toolchain, so the subprocess
    that invokes ``lake env lean`` raises ``FileNotFoundError``. The
    quality module must catch that and emit a clear "skipped" message
    rather than aborting the whole run.
    """
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
    )
    card = (
        "/-!\n"
        "# Test Project\n"
        "\n"
        "Source: arxiv:1234.5678\n"
        "Authors: Test Author\n"
        "Status: verified\n"
        "Main declarations: `hello`\n"
        "Tags: test\n"
        "-/\n"
    )
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.Basic\n\n{card}\ndef hello : Nat := 1\n"
    )
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj"}])

    with patch(
        "lean_pool.quality.subprocess.run",
        side_effect=FileNotFoundError("[Errno 2] No such file or directory: 'lake'"),
    ):
        errors = run_checks(tmp_path)

    messages = [error.message for error in errors]
    assert any("`lake` not found" in message for message in messages)


def test_quality_check_rejects_non_verified_status(tmp_path: Path) -> None:
    """Only `status: verified` projects may merge; `draft` is not accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "status": "draft"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid status" in error.message for error in errors)


def test_axiom_audit_resolved_parses_success_lines() -> None:
    """`#print axioms` success lines populate the resolved set; _root_ stripped.

    Both output forms must be recognized — the with-axioms list and the
    axiom-free message that pure `def`s produce.
    """
    stdout = (
        "'_root_.Foo.bar' depends on axioms: [Classical.choice, propext]\n"
        "'baz' depends on axioms: []\n"
        "'_root_.hello' does not depend on any axioms\n"
        # Names ending in `'` are echoed by Lean as `'foo'' ...`; the parser
        # must capture the prime, not stop at the embedded quote.
        "'_root_.Ns.neg_one_pow_ne_zero'' does not depend on any axioms\n"
        "'_root_.Ns.exp_poly_sub_prod'' depends on axioms: [propext]\n"
    )

    assert _axiom_audit_resolved(stdout) == {
        "Foo.bar",
        "baz",
        "hello",
        "Ns.neg_one_pow_ne_zero'",
        "Ns.exp_poly_sub_prod'",
    }


def test_axiom_audit_missing_attributes_stderr_to_each_declaration(
    tmp_path: Path,
) -> None:
    """Per-declaration errors quote the matching stderr line."""
    decl_a = _Declaration(name="foo'", path=tmp_path / "A.lean", line=12, kind="lemma")
    decl_b = _Declaration(name="bar", path=tmp_path / "B.lean", line=34, kind="lemma")
    stderr = "/tmp/x.lean:5:0: error: unknown constant '_root_.foo''\n"

    errors = _axiom_audit_missing([decl_a, decl_b], stderr)

    assert len(errors) == 2
    assert errors[0].path == tmp_path / "A.lean" and errors[0].line == 12
    assert "unknown constant" in errors[0].message
    assert errors[1].path == tmp_path / "B.lean" and errors[1].line == 34
    assert "produced no result" in errors[1].message


def test_quality_check_rejects_duplicate_slug(tmp_path: Path) -> None:
    """Two projects sharing a slug must be rejected."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [
            {"slug": "p", "entry_module": "LeanPool.Basic"},
            {"slug": "p", "entry_module": "LeanPool.Other"},
        ],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "duplicate `slug`" in error.message and "'p'" in error.message
        for error in errors
    )


def test_quality_check_rejects_duplicate_entry_module(tmp_path: Path) -> None:
    """Two projects sharing an entry_module must be rejected."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [
            {"slug": "a", "entry_module": "LeanPool.Basic"},
            {"slug": "b", "entry_module": "LeanPool.Basic"},
        ],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("duplicate `entry_module`" in error.message for error in errors)


def test_quality_check_rejects_out_of_order_header(tmp_path: Path) -> None:
    """The Copyright/License/Authors lines must appear in the documented order."""
    _write_minimal_repo(tmp_path)
    out_of_order = (
        "/-\n"
        "Authors: Test Author\n"
        "Copyright (c) 2026 Test Author. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "-/\n"
    )
    (tmp_path / "LeanPool" / "Basic.lean").write_text(
        f"{out_of_order}\ndef hello := 1\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("malformed file header" in error.message for error in errors)


def test_quality_check_rejects_adhoc_metadata_in_header(tmp_path: Path) -> None:
    """Source/MSC/Tags/Status belong in projects.yml, not in file headers."""
    _write_minimal_repo(tmp_path)
    bad_header = (
        "/-\n"
        "Copyright (c) 2026 Test Author. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Test Author\n"
        "Source: arxiv:1234.5678\n"
        "-/\n"
    )
    (tmp_path / "LeanPool" / "Basic.lean").write_text(f"{bad_header}\ndef hello := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("malformed file header" in error.message for error in errors)


def test_quality_check_rejects_extra_axiom_status(tmp_path: Path) -> None:
    """`extra-axiom` status was previously valid; only `verified` is now accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "status": "extra-axiom"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid status" in error.message for error in errors)
