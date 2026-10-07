# Merge queue and project storage

The organization repository uses GitHub's native merge queue. A ready PR is
added with the normal Merge button or `gh pr merge --auto --squash`. GitHub tests
its proposed squash commit together with the latest main and any preceding
queued PRs. Three proposed groups can build concurrently; up to ten passing PRs
can merge together. A failed group does not merge. There are no bypass actors.

Every group reports the normal required build, separation, documentation,
Python, workflow, and applicable minimal-file checks. Optional heavy checks
report a skipped result when their original trigger paths are absent. Content
separation is checked for each constituent squash commit, so independent content
and infrastructure PRs can coexist in a group without becoming a mixed PR.
The Lean, warning, declaration, style and quality gates still inspect the
combined tree. Build outputs and validation results are reused only after their
existing source, inventory, configuration and dependency checks pass.

A project adds its sources, its own complete public `Imports.lean`, and one
`LeanPool/projects/<slug>.yaml` mapping. It never edits `LeanPool.lean`. Lake's
`LeanPool.*` discovery builds every source, including files accidentally omitted
from a project aggregate; the index and quality checks also reject incomplete
aggregates. Historical tools can still read the previous monolithic registry,
but mixed old and new layouts are rejected.

Generated README statistics and NOTICE are submitted through one protected
`codex/generated-metadata` PR. That PR is not rewritten while checks are running.
For PRs and groups combining metadata and content, Python CI verifies each
authored NOTICE against its own immutable PR registry before regenerating the
combined checkout view for the ordinary generator tests. An inherited stale
generated file therefore cannot block unrelated Python changes; an incorrect
authored attribution edit still fails before regeneration.

Deployment is deliberately staged: merge the infrastructure while the legacy
registry remains, then migrate only the content files. Enable the repository's
`Validated merge queue` ruleset (the checked-in JSON documents the settings),
set `USE_MERGE_QUEUE=true`, and turn off the classic protection's strict
up-to-date requirement while retaining its other requirements. The active
queue replaces repeated author-branch updates with tests of the latest proposed
merge. The old automatic rebase workflow skips when that variable is true.

Measure throughput from actual `merge_group` runs after main's build cache is
warm: record queue entry time, group start/end, merged time, failures and
cancelled/recreated groups. A cold infrastructure migration or a toolchain bump
is not representative of an unchanged project's steady-state queue wait.
