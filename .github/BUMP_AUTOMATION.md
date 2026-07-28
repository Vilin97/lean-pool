# Automated Mathlib bumps

[`mathlib-bump.yml`](workflows/mathlib-bump.yml) migrates the whole pool to a
new Lean/Mathlib release. It runs nightly and needs a human only at the end, to
review the draft PR it opens.

## What runs, and what it costs

| Stage | What it does | Cost |
|---|---|---|
| `detect` | Compares the pinned release against Mathlib's tags | free |
| `probe` | Moves the pins, builds every project, buckets failures per project | free |
| `repair` | One Claude job per broken project, in parallel | subscription quota |
| `assemble` | Applies patches, rebuilds the pool, runs all four gates, opens a draft PR | free |

"Free" means GitHub-hosted runner minutes, which are unmetered for public
repositories. Only `repair` spends anything, and only when something broke.

The `probe` stage is worth having on its own: it runs whether or not a repair
follows, so the morning after a release you already know whether the bump costs
three projects or thirty.

### Repair modes

The `repair` input controls the fan-out:

- `auto` (default) — repair final releases, report only on `-rc` tags. Mathlib
  tags release candidates often; repairing each one would drain the token budget
  for a version you are not adopting yet.
- `always` — repair whatever was detected, including candidates.
- `never` — probe only. Use this to size a bump before committing to it.

## One-time setup

### 1. Claude subscription token

`repair` authenticates with a Claude subscription rather than API credits:

```bash
claude setup-token
```

Store the result as a repository secret named `CLAUDE_CODE_OAUTH_TOKEN`
(Settings → Secrets and variables → Actions). Usage bills against the
subscription's quota, shared with terminal and web sessions.

**These tokens expire.** When one does, `repair` fails with an authentication
error while `detect` and `probe` keep succeeding — so the nightly canary looks
healthy and only the repair half is dead. Two ways to handle it:

- *Simplest:* re-run `claude setup-token` and update the secret when a repair
  job fails to authenticate. The failure is loud and the fix takes a minute.
- *Unattended:* store a fine-grained PAT with `secrets: write` on this
  repository and have the action refresh the stored token automatically. This
  trades a long-lived PAT for never having to think about expiry.

### 2. Pushing to branches (and to fork PRs)

This workflow only ever pushes to `bump/*` branches in this repository, which
the default `GITHUB_TOKEN` can do.

Any automation that needs to push to a **contributor's fork branch** — the
auto-rebase job for import PRs, for instance — cannot use `GITHUB_TOKEN`: it has
no write access to forks even when the PR has *Allow edits by maintainers*
checked. The fix is to authenticate as an app or a user instead:

```yaml
- uses: actions/create-github-app-token@<sha>
  id: app-token
  with:
    app-id: ${{ secrets.APP_ID }}
    private-key: ${{ secrets.APP_PRIVATE_KEY }}
- uses: actions/checkout@<sha>
  with:
    token: ${{ steps.app-token.outputs.token }}
```

A GitHub App is preferable to a personal access token: its permissions are
scoped to this repository, it can be revoked without touching your account, and
its pushes re-trigger `pull_request` CI, which `GITHUB_TOKEN` pushes do not.

## Triggering a bump by hand

Actions → Mathlib Bump → Run workflow. Leave `version` blank to bump to the
newest release, or name one explicitly:

```bash
gh workflow run mathlib-bump.yml -f version=v4.33.0-rc1 -f repair=always
```

To size a bump without spending anything:

```bash
gh workflow run mathlib-bump.yml -f repair=never
```

The probe report (per-project errors and warnings) is attached to the run as the
`bump-report` artifact and summarised on the run page.

## What the automation will not do

- **Merge.** The PR is opened as a draft and stays that way until you review it.
- **Weaken a gate.** Repair agents are instructed never to add `sorry`,
  `native_decide`, an axiom, or a linter waiver, and `assemble` re-runs
  `quality.py`, which fails on those regardless of what an agent was told.
- **Drop a statement.** Agents are told that a lemma now absorbed by Mathlib is
  still not theirs to delete; they report it instead, and the reviewer decides.
  This is deliberately not a hard gate — losing a declaration to Mathlib is a
  legitimate outcome of a bump, so it needs a human judgement, not a check.

## When a repair job fails

Failures are isolated: `fail-fast` is off, so one project failing does not stop
the others, and `assemble` still opens a PR with whatever succeeded. The PR body
lists how many repairs applied and which patches would not apply. Re-run just
the failed jobs from the run page, or fix that project by hand on the `bump/*`
branch.
