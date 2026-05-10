.PHONY: build setup lint lint-fix check test update agent-docs

# Build the Lean project.
build:
	lake build LeanPool

# First-time setup: pull the Mathlib oleans cache, build the Lean
# library at the pinned version, and install Python tooling.
setup:
	lake exe cache get
	lake build LeanPool
	cd python && uv sync

# Run all CI-equivalent linters (Lean and Python).
lint:
	lake exe runLinter LeanPool
	cd python && uv run ruff check
	cd python && uv run ruff format --check

# Auto-fix Python lint and formatting issues.
lint-fix:
	cd python && uv run ruff check --fix
	cd python && uv run ruff format

# Verify LeanPool.lean imports the full file set (CI gate).
check:
	lake exe mk_all --check

# Run the Python test suite.
test:
	cd python && uv run --group test pytest

# Update Lean and Python dependencies. Refreshes lake-manifest.json,
# pulls the matching Mathlib oleans cache, and re-syncs the Python
# environment with all dependency groups.
update:
	lake update
	lake exe cache get
	cd python && uv sync --all-groups

# Generate CLAUDE.md and AGENTS.md from README.md and CONTRIBUTING.md.
# Run this whenever README.md or CONTRIBUTING.md changes so agents pick
# up the latest contributor guidance.
agent-docs:
	@echo "This file is a concatenation of README.md and CONTRIBUTING.md." > CLAUDE.md
	@echo "" >> CLAUDE.md
	@cat README.md >> CLAUDE.md
	@echo "" >> CLAUDE.md
	@cat CONTRIBUTING.md >> CLAUDE.md
	@cp CLAUDE.md AGENTS.md
	@echo "Generated CLAUDE.md and AGENTS.md"
