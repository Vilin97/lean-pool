# lean-pool python tooling

Scripts that fetch data from [Reservoir](https://reservoir.lean-lang.org)
and decide which Lean projects belong in `lean-pool`.

Managed with [uv](https://docs.astral.sh/uv/).

LLM pull request reviews run through GPT-6-Astra on the Azure VM's Codex account
pool. See [Azure review operations](azure-review.md) for deployment and diagnostics.

## Setup

```bash
cd python
uv sync
```

## Layout

- `lean_pool/` — package modules
- `tests/` — pytest tests
- `pyproject.toml` — dependencies, ruff and pytest config
- `.python-version` — Python version pin (read by `uv`)

## Common commands

```bash
uv run pytest       # run tests
uv run ruff check   # lint
uv run ruff format  # format
uv run python -m lean_pool.quality --repo ..  # repository quality gates
```
