"""Render a bump report for humans, or one project's diagnostics for an agent.

Used twice by `.github/workflows/mathlib-bump.yml`:

    python3 scripts/ci/bump-summary.py bump-report.json
        Markdown breakage table for the run's step summary.

    python3 scripts/ci/bump-summary.py bump-report.json --project Polytopes
        That project's build errors, written to `diagnostics.txt` for the
        repair agent to start from.

Only stdlib is used: this runs from a bare checkout, before any Python
dependency install.
"""

import argparse
import json
import sys


def render_summary(report: dict) -> str:
    """Render the whole-run breakage table."""
    broken = report.get("broken", [])
    warned = report.get("warned", [])
    lines = [
        f"### Probe: {len(broken)} project(s) failing, "
        f"{len(warned)} with warnings",
        "",
    ]
    if not broken and not warned:
        lines.append("The pool builds clean against this release.")
        return "\n".join(lines) + "\n"
    if broken:
        lines += ["| Project | Errors |", "|---|---|"]
        lines += [
            f"| **{entry['project']}** | {entry['error_count']} |" for entry in broken
        ]
        lines.append("")
    if warned:
        lines += ["| Project (warnings only) | Warnings |", "|---|---|"]
        lines += [
            f"| {entry['project']} | {entry['warning_count']} |" for entry in warned
        ]
    return "\n".join(lines) + "\n"


def render_project(report: dict, project: str) -> str:
    """Render one project's diagnostics for its repair agent."""
    for entry in report.get("broken", []):
        if entry["project"] == project:
            shown, total = len(entry["errors"]), entry["error_count"]
            header = f"{total} error(s) building LeanPool.{project}"
            if shown < total:
                header += f" (first {shown} lines shown)"
            return header + ":\n\n" + "\n".join(entry["errors"]) + "\n"
    return f"No recorded errors for LeanPool.{project}.\n"


def main(argv: list[str] | None = None) -> int:
    """Print the requested rendering of a bump report."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("report", help="path to bump-report.json")
    parser.add_argument("--project", help="render only this project's errors")
    args = parser.parse_args(argv)

    with open(args.report, encoding="utf-8") as handle:
        report = json.load(handle)

    if args.project:
        sys.stdout.write(render_project(report, args.project))
    else:
        sys.stdout.write(render_summary(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
