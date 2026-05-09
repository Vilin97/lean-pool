.PHONY: agent-docs

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
