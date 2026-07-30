.PHONY: build build-project build-challenges setup lint lint-fix check test docs \
	update agent-docs challenges comparator verify-challenge

# Where `make comparator` keeps its checkouts.
COMPARATOR_CACHE ?= $(HOME)/.cache/lean-pool

# Build the Lean project.
build:
	lake build LeanPool
	lake build Challenge Solution

# Build only the challenge board and its solutions (seconds, not hours).
build-challenges:
	lake build Challenge Solution

# Build a single project against the Mathlib cache, e.g.
# `make build-project P=Rupert`. Projects are independent, so this needs
# only `lake exe cache get`, not the whole pool — minutes instead of ~1.5h.
build-project:
	@test -n "$(P)" || { echo "usage: make build-project P=YourProject"; exit 1; }
	lake build LeanPool.$(P)

# First-time setup: pull the Mathlib oleans cache, build the Lean
# library at the pinned version, and install Python tooling.
setup:
	lake exe cache get
	lake build LeanPool
	cd python && uv sync

# Run all CI-equivalent linters (Lean and Python).
lint:
	lake exe runLinter LeanPool
	lake exe runLinter Challenge
	lake exe runLinter Solution
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

# Build doc-gen4 documentation.
docs:
	cd docbuild && lake build LeanPool:docs

# List the registered challenges (open statements awaiting a proof).
challenges:
	cd python && uv run python -m lean_pool.challenge --repo .. list

# Fetch and build the third-party judge used to verify challenge solutions:
# leanprover/comparator, plus a lean4export built at this project's toolchain
# (comparator pins its own, newer one, which cannot read our oleans).
comparator:
	@mkdir -p $(COMPARATOR_CACHE)
	@test -d $(COMPARATOR_CACHE)/comparator || \
		git clone https://github.com/leanprover/comparator $(COMPARATOR_CACHE)/comparator
	cd $(COMPARATOR_CACHE)/comparator && git fetch --quiet origin && \
		git checkout --quiet $$(. $(CURDIR)/scripts/challenge/pins.env && echo $$COMPARATOR_COMMIT) && \
		lake build comparator
	@test -d $(COMPARATOR_CACHE)/lean4export || \
		git clone https://github.com/leanprover/lean4export $(COMPARATOR_CACHE)/lean4export
	cd $(COMPARATOR_CACHE)/lean4export && git fetch --quiet origin && \
		git checkout --quiet $$(. $(CURDIR)/scripts/challenge/pins.env && echo $$LEAN4EXPORT_COMMIT) && \
		lake build lean4export
	@echo
	@echo "comparator:  $(COMPARATOR_CACHE)/comparator/.lake/build/bin/comparator"
	@echo "lean4export: $(COMPARATOR_CACHE)/lean4export/.lake/build/bin/lean4export"
	@echo "Export COMPARATOR_LEAN4EXPORT to the latter, or pass --lean4export."

# Verify a solution against its challenge statement with comparator, e.g.
# `make verify-challenge C=two-plus-two`. SOLUTION defaults to the module the
# registry records; pass it to check one that is not registered yet.
verify-challenge:
	@test -n "$(C)" || \
		{ echo "usage: make verify-challenge C=<slug> [SOLUTION=<module>]"; exit 1; }
	scripts/challenge/verify-solution.sh $(C) $(SOLUTION)

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
