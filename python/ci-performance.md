# Lean and documentation CI performance

The September 17 investigation found two recurring costs: exposition extraction
ran for 137–146 minutes on every run, and evicted documentation checkpoints added
about 88 minutes for Mathlib and 94–101 minutes for pool documentation data.
Two per-commit Lean caches were about 5 GiB each against a 10 GB cache limit.
HTML rendering itself took about four minutes.

Examples: [warm main run](https://github.com/Vilin97/lean-pool/actions/runs/35231792853),
[cold main run](https://github.com/Vilin97/lean-pool/actions/runs/35253856245),
[project PR run](https://github.com/Vilin97/lean-pool/actions/runs/35263858983).

## Cache ownership

Lean CI saves the toolchain and pinned dependencies under `LeanDependencies-v1`,
keyed by OS, toolchain, and dependency manifest. The separate `LeanPoolBuild-v1`
cache contains only `.lake/build`, with the build configuration and commit in
its key. All consumers use the same paths and compatibility keys. Preflight and
Mathlib documentation restore only dependencies. Existing `Lake-` caches expire
normally; the first run after this migration must seed the new namespaces.

Documentation retains its separate, integrity-checked SQLite checkpoints. They
still depend on available cache capacity; this change reduces duplicate data
instead of changing the repository's paid storage limit.

## Reusing the current CI build

After compilation, both single and sharded CI publish one `lean-pool-build`
artifact with one-day retention. Docs look up the Lean CI run for their exact
event and head SHA, wait up to two hours for its compiled output, and verify a
manifest containing the Git tree and build-input hashes before installing it.
The tree comparison also distinguishes different PR merge bases.

No matching run, missing/expired artifacts, API failures, or a mismatched tree
fall back to the regular Lake build. Documentation still invokes Lake, which
checks traces and builds any missing targets. Exposition can start after
preflight without waiting for Mathlib's unrelated docInfo database. The existing
warning, lint, quality, minimal-file, and documentation validation steps remain.

## Incremental exposition extraction

`lake env bash scripts/exposition/extract-all.sh` still runs each project in its
own Lean environment to preserve parser/notation isolation. Outputs are cached
under `.lake/exposition-cache/v1/<project>/<fingerprint>/`. Each key covers:

- All Lean sources under the project, including its entry module.
- Local transitive imports from the entry module's Lake `.setup.json` inventory.
- The toolchain, dependency manifest, Lake configuration, extractor, and driver.

Run after `lake build LeanPool` so compiler inventories reflect the current
source tree. A missing or malformed inventory conservatively hashes the entire
pool. Both JSONL files must pass validation before publication, and their hashes
are checked on reuse. Changed projects are extracted again; deleted projects
are omitted when the outputs are assembled in sorted project order. Obsolete
project generations are removed before saving the CI cache.

To bypass cached results for a comparison:

```sh
lake env bash scripts/exposition/extract-all.sh fresh-dump.jsonl fresh-commands.jsonl --refresh
```

CI uploads `exposition-extraction-diagnostics`, containing per-project wall times,
cache-hit flags, and extraction logs. Local timings are in
`.lake/exposition-timings.json`; failed process logs are retained next to the
project's cache generations. This makes cold-run hotspots measurable without
changing extraction semantics or skipping projects.

The local SumDifferenceExponent smoke test produced identical SHA-256 hashes
for both output files on cold extraction, cache reuse, and forced refresh.
Cache reuse took under a millisecond, versus 5–13 seconds for extraction on that
machine. This is a small-project correctness check, not a whole-pool timing claim.
Measure full-run savings after the main-branch extraction cache has been seeded.

## Pull-request scheduling and project validation

Pull requests retain the required `Documentation preflight` check, including
workspace compatibility and generated-root checks. Full exposition/doc-gen
jobs run on main; use the Documentation workflow's `preview` input to generate
branch artifacts on demand. Branch previews never deploy production Pages.
Ordinary PR builds no longer package the large documentation build artifact.

After compilation, Lean CI partitions every pool source into project units,
including Basic, the root, nested files and unregistered modules. Declaration
lint, axiom audits and option-backdoor audits import all owned modules; each
compiled declaration is checked in its owning unit. Registry declarations use
separate per-entry receipts. Static checks (registry/card consistency,
reachability, forbidden constructs, size limits and Lake options), text style
lint, and Challenge/Solution validation still run every time.

`.lake/validation-cache/v1/passes.json` contains successful receipts keyed by
source contents, each module's transitive compiler import inventory, toolchain,
dependency pins, build options and checker code. Missing import inventories
conservatively hash all local Lean sources. Changes to a project's registry
entry invalidate its declaration check without invalidating sibling projects.
Adding, deleting or editing modules changes the validation coverage. Failed
checks never publish receipts. A registry-only rebase can therefore reuse
proof validation while still checking the registry and generated cards.

Actions saves the small receipt cache after all gates pass. PR cache scope is
`refs/pull/<n>/merge`, so a PR can reuse its previous validation across rebases,
but main and other PRs cannot consume its receipts. Main receipts are available
to all branches. The first run after shipping, a toolchain bump or a checker
change remains cold; subsequent runs should avoid validating unchanged projects.

To bypass receipts for comparison, from `python/`:

```sh
uv run python -m lean_pool.validation_cache lint --repo .. --refresh
uv run python -m lean_pool.validation_cache quality --repo .. --refresh
```

This does not eliminate GitHub's strict up-to-date check requirement or registry
merge conflicts. CI still runs for a new merge result, with compilation handled
by Lake's existing incremental build cache and validation reused by content.
