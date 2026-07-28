"""Tests for challenge mode: registry, cards, comparator configuration, and gates."""

from __future__ import annotations

from pathlib import Path

from lean_pool import challenge
from lean_pool.quality import (
    _Declaration,
    _parse_axiom_output,
    _parse_option_audit_output,
    run_checks,
)

HEADER = """/-
Copyright (c) 2026 Test Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Test Author
-/
"""

STATEMENT_BODY = """
namespace Challenge.Widget

/-- A test challenge. -/
theorem widget_exists : True := sorry

end Challenge.Widget
"""

CHALLENGE_ENTRY = {
    "slug": "widget",
    "title": "Widget conjecture",
    "summary": "Prove that a widget exists.",
    "branch": "test mathematics",
    "entry_module": "Challenge.Widget",
    "proposers": ["Test Author"],
    "source": {"url": "https://example.invalid/widget"},
    "license": "Apache-2.0",
    "provenance": "human",
    "status": "open",
    "statements": [
        {
            "declaration": "Challenge.Widget.widget_exists",
            "informal": "A widget exists.",
        }
    ],
    "tags": ["test"],
    "msc": ["00A35"],
}


def _write_minimal_repo(root: Path) -> None:
    """Create the smallest LeanPool tree accepted by static checks."""
    (root / "LeanPool").mkdir()
    (root / "LeanPool.lean").write_text("import LeanPool.Basic\n")
    (root / "LeanPool" / "Basic.lean").write_text(f'{HEADER}\ndef hello := "world"\n')
    (root / "LeanPool" / "projects.yml").write_text("projects: []\n")
    (root / "lakefile.toml").write_text(
        'name = "lean-pool"\nversion = "0.1.0"\ndefaultTargets = ["LeanPool"]\n'
    )


def _write_challenge(
    root: Path,
    *,
    body: str = STATEMENT_BODY,
    registry: str | None = None,
    write_card: bool = True,
    entry: dict[str, object] | None = None,
) -> None:
    """Add a one-challenge library to a minimal repo."""
    (root / "Challenge").mkdir(exist_ok=True)
    (root / "Challenge.lean").write_text("import Challenge.Widget\n")
    card = (
        f"{challenge.challenge_card(entry or CHALLENGE_ENTRY)}\n" if write_card else ""
    )
    (root / "Challenge" / "Widget.lean").write_text(f"{HEADER}\n{card}{body}")
    (root / "Challenge" / "challenges.yml").write_text(
        registry if registry is not None else _registry_text()
    )


def _registry_text(**overrides: object) -> str:
    """Render `challenges.yml` for the fixture entry, with overrides."""
    entry = {**CHALLENGE_ENTRY, **overrides}
    statements = "\n".join(
        f"      - declaration: {item['declaration']}\n"
        f"        informal: {item['informal']}"
        for item in entry["statements"]
    )
    return (
        "challenges:\n"
        f"  - slug: {entry['slug']}\n"
        f"    title: {entry['title']}\n"
        f"    summary: {entry['summary']}\n"
        f"    branch: {entry['branch']}\n"
        f"    entry_module: {entry['entry_module']}\n"
        f"    proposers: [{', '.join(entry['proposers'])}]\n"
        "    source:\n"
        f"      url: {entry['source']['url']}\n"
        f"    license: {entry['license']}\n"
        f"    provenance: {entry['provenance']}\n"
        f"    status: {entry['status']}\n"
        "    statements:\n"
        f"{statements}\n"
        f"    tags: [{', '.join(entry['tags'])}]\n"
        f"    msc: ['{entry['msc'][0]}']\n"
    )


def test_comparator_config_lists_statements_and_axioms() -> None:
    """The generated configuration is what `leanprover/comparator` consumes."""
    configuration = challenge.comparator_configuration(
        CHALLENGE_ENTRY, "LeanPool.Solution"
    )

    assert configuration == {
        "challenge_module": "Challenge.Widget",
        "solution_module": "LeanPool.Solution",
        "theorem_names": ["Challenge.Widget.widget_exists"],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": False,
    }


def test_comparator_config_declares_definition_holes() -> None:
    """Definition holes are passed through as `definition_names`."""
    entry = {
        **CHALLENGE_ENTRY,
        "definitions": [
            {"declaration": "Challenge.Widget.answer", "informal": "The answer."}
        ],
    }

    configuration = challenge.comparator_configuration(
        entry, "Solution", enable_nanoda=True
    )

    assert configuration["definition_names"] == ["Challenge.Widget.answer"]
    assert configuration["enable_nanoda"] is True


def test_challenge_card_wraps_and_carries_the_informal_statement() -> None:
    """The card pairs each open declaration with the prose it must match."""
    entry = {
        **CHALLENGE_ENTRY,
        "statements": [
            {
                "declaration": "Challenge.Widget.widget_exists",
                "informal": "A widget exists " + "and is very interesting " * 8,
            }
        ],
    }

    card = challenge.challenge_card(entry)

    assert card.startswith("/-!\n# Widget conjecture\n")
    assert "Source: url:https://example.invalid/widget" in card
    assert "Open declarations: `Challenge.Widget.widget_exists`" in card
    assert "Informal statement:" in card
    assert all(len(line) <= challenge.CARD_WIDTH for line in card.splitlines())


def test_challenge_repo_passes_static_quality_checks(tmp_path: Path) -> None:
    """A well-formed challenge library passes without invoking Lean."""
    _write_minimal_repo(tmp_path)
    _write_challenge(tmp_path)

    assert run_checks(tmp_path, skip_lean_axioms=True) == []


def test_sorry_is_rejected_outside_the_challenge_library(tmp_path: Path) -> None:
    """`sorry` in pooled content stays forbidden."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "Basic.lean").write_text(
        f"{HEADER}\ntheorem hello : True := sorry\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("sorry is forbidden outside Challenge/" in e.message for e in errors)


def test_partial_sorry_is_rejected_inside_the_challenge_library(
    tmp_path: Path,
) -> None:
    """A `sorry` buried in a term leaves a challenge quietly half-open."""
    _write_minimal_repo(tmp_path)
    _write_challenge(
        tmp_path,
        body=(
            "\nnamespace Challenge.Widget\n\n"
            "/-- A test challenge. -/\n"
            "theorem widget_exists : True ∧ True := ⟨sorry, trivial⟩\n\n"
            "end Challenge.Widget\n"
        ),
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("must be the whole proof body" in e.message for e in errors)


def test_admit_is_rejected_inside_the_challenge_library(tmp_path: Path) -> None:
    """Challenge mode allows exactly one spelling of an open proof."""
    _write_minimal_repo(tmp_path)
    _write_challenge(
        tmp_path,
        body=(
            "\nnamespace Challenge.Widget\n\n"
            "/-- A test challenge. -/\n"
            "theorem widget_exists : True := by admit\n\n"
            "end Challenge.Widget\n"
        ),
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("admit is forbidden" in e.message for e in errors)


def test_unregistered_sorry_is_rejected_without_lean(tmp_path: Path) -> None:
    """A second `sorry` nobody registered is caught by the static gate too."""
    _write_minimal_repo(tmp_path)
    _write_challenge(
        tmp_path,
        body=(
            "\nnamespace Challenge.Widget\n\n"
            "/-- A test challenge. -/\n"
            "theorem widget_exists : True := sorry\n\n"
            "/-- Scaffolding nobody declared open. -/\n"
            "private theorem scaffolding : True := sorry\n\n"
            "end Challenge.Widget\n"
        ),
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "sorry belongs to Challenge.Widget.scaffolding" in e.message for e in errors
    )
    assert not any("widget_exists" in e.message for e in errors)


def test_challenge_imports_are_restricted_to_mathlib(tmp_path: Path) -> None:
    """A statement resting on pool code is not a stable contract."""
    _write_minimal_repo(tmp_path)
    _write_challenge(tmp_path)
    path = tmp_path / "Challenge" / "Widget.lean"
    path.write_text(
        path.read_text().replace(HEADER, f"{HEADER}import LeanPool.Basic\n")
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "may import only Mathlib modules" in e.message and "LeanPool.Basic" in e.message
        for e in errors
    )


def test_unregistered_challenge_module_is_rejected(tmp_path: Path) -> None:
    """Every statement file has to be on the board."""
    _write_minimal_repo(tmp_path)
    _write_challenge(tmp_path)
    (tmp_path / "Challenge" / "Stray.lean").write_text(
        f"{HEADER}\n/-! # Stray\n\nSource: url:https://example.invalid\n-/\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("Challenge.Stray missing from" in e.message for e in errors)


def test_registry_declaration_must_exist_in_the_module(tmp_path: Path) -> None:
    """A registry naming a declaration the file lacks is caught statically."""
    _write_minimal_repo(tmp_path)
    _write_challenge(
        tmp_path,
        registry=_registry_text(
            statements=[
                {
                    "declaration": "Challenge.Widget.missing",
                    "informal": "Nothing declares this.",
                }
            ]
        ),
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("which is not declared in Challenge.Widget" in e.message for e in errors)


def test_open_challenge_may_not_claim_a_solution(tmp_path: Path) -> None:
    """`status` and the `solution` block have to agree."""
    _write_minimal_repo(tmp_path)
    _write_challenge(
        tmp_path,
        registry=_registry_text()
        + "    solution:\n      url: https://example.invalid\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("carries a `solution` block" in e.message for e in errors)


def test_solved_challenge_needs_a_solution_pointer(tmp_path: Path) -> None:
    """A solved challenge records where the proof lives."""
    _write_minimal_repo(tmp_path)
    _write_challenge(tmp_path, registry=_registry_text(status="solved"))

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("has no `solution` mapping" in e.message for e in errors)


def test_stale_challenge_card_is_rejected(tmp_path: Path) -> None:
    """The card is generated, so drift from the registry is an error."""
    _write_minimal_repo(tmp_path)
    _write_challenge(tmp_path, write_card=False)

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("challenge card for widget is out of date" in e.message for e in errors)


def _declaration(name: str) -> _Declaration:
    """Build a declaration record pointing at a throwaway path."""
    return _Declaration(
        name=name, path=Path("Challenge/Widget.lean"), line=7, kind="theorem"
    )


def test_axiom_audit_allows_sorry_only_for_registered_declarations() -> None:
    """Registered statements may rest on `sorryAx`; their neighbours may not."""
    declarations = [
        _declaration("Challenge.Widget.widget_exists"),
        _declaration("Challenge.Widget.helper"),
    ]
    output = (
        "'Challenge.Widget.widget_exists' depends on axioms: [propext, sorryAx]\n"
        "'Challenge.Widget.helper' depends on axioms: [sorryAx]\n"
    )

    errors = _parse_axiom_output(
        Path("/repo"), declarations, output, {"Challenge.Widget.widget_exists"}
    )

    assert len(errors) == 1
    assert "Challenge.Widget.helper depends on `sorryAx`" in errors[0].message


def test_axiom_audit_requires_registered_statements_to_stay_open() -> None:
    """A statement proved in place is no longer the contract solvers took on."""
    declarations = [_declaration("Challenge.Widget.widget_exists")]
    output = "'Challenge.Widget.widget_exists' does not depend on any axioms\n"

    errors = _parse_axiom_output(
        Path("/repo"), declarations, output, {"Challenge.Widget.widget_exists"}
    )

    assert len(errors) == 1
    assert "does not depend on `sorryAx`" in errors[0].message


def test_axiom_audit_catches_a_statement_proved_classically() -> None:
    """A proof that uses only permitted axioms still closes the statement.

    The axiom set is inside the allowlist, so the extra-axiom check has
    nothing to say and the declaration *is* reported by `#print axioms` —
    the gap is closed by demanding `sorryAx` outright.
    """
    declarations = [_declaration("Challenge.Widget.widget_exists")]
    output = (
        "'Challenge.Widget.widget_exists' depends on axioms: [propext, "
        "Classical.choice]\n"
    )

    errors = _parse_axiom_output(
        Path("/repo"), declarations, output, {"Challenge.Widget.widget_exists"}
    )

    assert len(errors) == 1
    assert "does not depend on `sorryAx`" in errors[0].message


def test_option_audit_tolerates_sorry_in_registered_declarations(
    tmp_path: Path,
) -> None:
    """A definition hole surfaces in the environment audit; that is expected."""
    stdout = (
        "LEANPOOL_OPTION_AUDIT|Challenge.Widget|Challenge.Widget.answer|"
        "references forbidden axiom-injecting constants: sorryAx\n"
        "LEANPOOL_OPTION_AUDIT|Challenge.Widget|Challenge.Widget.answer.eq_def|"
        "references forbidden axiom-injecting constants: sorryAx\n"
        "LEANPOOL_OPTION_AUDIT_COMPLETE\n"
    )

    errors = _parse_option_audit_output(
        tmp_path, stdout, "", open_declarations={"Challenge.Widget.answer"}
    )

    assert errors == []


def test_option_audit_still_reports_unregistered_sorry(tmp_path: Path) -> None:
    """The tolerance is scoped to declarations the registry lists."""
    stdout = (
        "LEANPOOL_OPTION_AUDIT|Challenge.Widget|Challenge.Widget.sneaky|"
        "references forbidden axiom-injecting constants: sorryAx\n"
        "LEANPOOL_OPTION_AUDIT_COMPLETE\n"
    )

    errors = _parse_option_audit_output(
        tmp_path, stdout, "", open_declarations={"Challenge.Widget.answer"}
    )

    assert len(errors) == 1
    assert "Challenge.Widget.sneaky" in errors[0].message


SOLVED_REGISTRY_SUFFIX = (
    "    solution:\n"
    "      module: Solution.Widget\n"
    "      authors: [Test Author]\n"
    '      verified: "2026-07-26"\n'
)

SOLUTION_BODY = """
namespace Challenge.Widget

/-- A test challenge. -/
theorem widget_exists : True := trivial

end Challenge.Widget
"""


def _solved_entry() -> dict[str, object]:
    """The fixture entry, marked solved by an in-repo module."""
    return {
        **CHALLENGE_ENTRY,
        "status": "solved",
        "solution": {
            "module": "Solution.Widget",
            "authors": ["Test Author"],
            "verified": "2026-07-26",
        },
    }


def _write_solution(root: Path, *, body: str = SOLUTION_BODY) -> None:
    """Add a solution library answering the fixture challenge."""
    (root / "Solution").mkdir(exist_ok=True)
    (root / "Solution.lean").write_text("import Solution.Widget\n")
    card = challenge.solution_card(_solved_entry())
    (root / "Solution" / "Widget.lean").write_text(f"{HEADER}\n{card}\n{body}")


def _write_solved_challenge(root: Path, **solution_kwargs: str) -> None:
    """Write a solved challenge plus its in-repo solution."""
    _write_challenge(
        root,
        registry=_registry_text(status="solved") + SOLVED_REGISTRY_SUFFIX,
        entry=_solved_entry(),
    )
    _write_solution(root, **solution_kwargs)


def test_solved_challenge_with_solution_passes_static_checks(tmp_path: Path) -> None:
    """The whole solved-challenge shape is accepted without invoking Lean."""
    _write_minimal_repo(tmp_path)
    _write_solved_challenge(tmp_path)

    assert run_checks(tmp_path, skip_lean_axioms=True) == []


def test_solution_may_not_import_the_challenge(tmp_path: Path) -> None:
    """Importing the challenge would inherit the statement, not restate it."""
    _write_minimal_repo(tmp_path)
    _write_solved_challenge(tmp_path)
    path = tmp_path / "Solution" / "Widget.lean"
    path.write_text(
        path.read_text().replace(HEADER, f"{HEADER}import Challenge.Widget\n")
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("may not import the challenge module" in e.message for e in errors)


def test_solution_must_declare_the_challenge_statement(tmp_path: Path) -> None:
    """Comparator matches by name, so the name has to be there."""
    _write_minimal_repo(tmp_path)
    _write_solved_challenge(
        tmp_path,
        body=(
            "\nnamespace Challenge.Widget\n\n"
            "/-- Something else entirely. -/\n"
            "theorem widget_exists' : True := trivial\n\n"
            "end Challenge.Widget\n"
        ),
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "does not declare Challenge.Widget.widget_exists" in e.message for e in errors
    )


def test_sorry_is_rejected_in_a_solution(tmp_path: Path) -> None:
    """A solution is a proof; the challenge library's licence stops here."""
    _write_minimal_repo(tmp_path)
    _write_solved_challenge(
        tmp_path,
        body=(
            "\nnamespace Challenge.Widget\n\n"
            "/-- A test challenge. -/\n"
            "theorem widget_exists : True := sorry\n\n"
            "end Challenge.Widget\n"
        ),
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("sorry is forbidden outside Challenge/" in e.message for e in errors)


def test_unregistered_solution_module_is_rejected(tmp_path: Path) -> None:
    """Every file under Solution/ answers a registered challenge."""
    _write_minimal_repo(tmp_path)
    _write_solved_challenge(tmp_path)
    (tmp_path / "Solution" / "Stray.lean").write_text(
        f"{HEADER}\n/-! # Stray\n\nChallenge: none\n-/\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "solution module Solution.Stray is not the recorded solution" in e.message
        for e in errors
    )


def test_solution_module_must_live_in_the_solution_library(tmp_path: Path) -> None:
    """A `module:` pointing outside `Solution/` is a registry error."""
    _write_minimal_repo(tmp_path)
    _write_challenge(
        tmp_path,
        registry=_registry_text(status="solved")
        + "    solution:\n      module: LeanPool.Basic\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("must live in the Solution library" in e.message for e in errors)


def test_solution_card_records_the_challenge_it_answers() -> None:
    """The card tells a reader what the restated statement is for."""
    card = challenge.solution_card(_solved_entry())

    assert card.startswith("/-!\n# Solution: Widget conjecture\n")
    assert "Challenge: `widget` (`Challenge.Widget`)" in card
    assert "Verified with comparator: 2026-07-26" in card
    assert "must not import" in card
    assert all(len(line) <= challenge.CARD_WIDTH for line in card.splitlines())


def test_option_audit_still_reports_combined_findings(tmp_path: Path) -> None:
    """`sorryAx` plus anything else is never tolerated."""
    stdout = (
        "LEANPOOL_OPTION_AUDIT|Challenge.Widget|Challenge.Widget.answer|"
        "references forbidden axiom-injecting constants: sorryAx; declares an axiom\n"
        "LEANPOOL_OPTION_AUDIT_COMPLETE\n"
    )

    errors = _parse_option_audit_output(
        tmp_path, stdout, "", open_declarations={"Challenge.Widget.answer"}
    )

    assert len(errors) == 1
    assert "declares an axiom" in errors[0].message
