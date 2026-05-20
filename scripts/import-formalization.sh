#!/usr/bin/env bash
# Import a Lean formalization from an external repo into lean-pool.
#
# Workflow:
#   1. Clone (or reuse) the external repo into a sibling scratch directory.
#   2. Create a fresh git worktree of lean-pool on a new branch.
#   3. Hand both paths to a headless agent (Claude or Codex)
#      with a detailed prompt covering the bump, vendoring, projects.yml
#      entry, file headers, and CI checks documented in
#      .github/CODE_QUALITY.md.
#   4. Whatever progress the agent makes, push the branch and open a PR in
#      lean-pool. Partial progress is acceptable and expected.
#
# Usage:
#   scripts/import-formalization.sh <source-repo-url> [options]
#
# Options:
#   --slug <name>           Override the derived slug (default: lowercased repo name).
#   --branch <name>         Override the branch name (default: import/<slug>).
#   --source-dir <path>     Reuse an existing clone instead of fetching.
#   --base <branch>         Base branch for the PR (default: main).
#   --bumps-dir <path>      Where to put the worktree + source clone
#                           (default: $LEAN_POOL_BUMPS_DIR or
#                           <lean-pool-parent>/lean-pool-bumps).
#   --agent <name>          Headless agent: claude or codex
#                           (default: $LEAN_POOL_AGENT or claude).
#   --model <id>            Agent model (defaults: claude-opus-4-7 for
#                           Claude, gpt-5.5 for Codex).
#   --effort <level>        Effort level (defaults: max for Claude,
#                           xhigh for Codex).
#   --no-shared-packages    Give each worktree its own .lake/packages copy
#                           instead of symlinking a shared, prebuilt store.
#   --cleanup               Remove the worktree after the PR is opened
#                           (the pushed branch + PR stay; reclaims its .lake).
#   --keep-worktree         Don't print the cleanup hint at the end.
#   --dry-run               Set up everything but skip the agent and PR.
#
# Disk: every import builds the same `LeanPool` target against lean-pool's
# pinned dependency set, so `.lake/packages` (dep sources + ~5 GB of prebuilt
# Mathlib oleans) is identical across runs. It is seeded once into a shared
# store under <bumps-dir>/.shared-lake-packages/<manifest-hash>/ and
# symlinked into each worktree, so N concurrent imports cost ~one copy, not N.
# Each worktree's own build output stays in its private .lake/build.
#
# Environment:
#   LEAN_POOL_BUMPS_DIR     Override default bumps directory.
#   LEAN_POOL_AGENT         Override default agent (claude or codex).
#   LEAN_POOL_AGENT_MODEL   Override default model.
#   LEAN_POOL_AGENT_EFFORT  Override default effort.

set -euo pipefail

# --- Logging -----------------------------------------------------------------

readonly C_RESET=$'\033[0m'
readonly C_BOLD=$'\033[1m'
readonly C_DIM=$'\033[2m'
readonly C_RED=$'\033[31m'
readonly C_GREEN=$'\033[32m'
readonly C_YELLOW=$'\033[33m'
readonly C_BLUE=$'\033[34m'

log()    { printf '%s[import]%s %s\n' "$C_BLUE"  "$C_RESET" "$*" >&2; }
warn()   { printf '%s[import]%s %s\n' "$C_YELLOW" "$C_RESET" "$*" >&2; }
error()  { printf '%s[import]%s %s\n' "$C_RED"   "$C_RESET" "$*" >&2; }
ok()     { printf '%s[import]%s %s\n' "$C_GREEN" "$C_RESET" "$*" >&2; }

die() { error "$*"; exit 1; }

github_repo_of() {
  local url="${1%.git}"
  url="${url%/}"
  case "$url" in
    https://github.com/*) printf '%s' "${url#https://github.com/}" ;;
    http://github.com/*)  printf '%s' "${url#http://github.com/}" ;;
    git@github.com:*)     printf '%s' "${url#git@github.com:}" ;;
    *)                    return 1 ;;
  esac
}

source_repo_registered() {
  local repo="$1"
  local projects_file="$LEAN_POOL_ROOT/LeanPool/projects.yml"
  [[ "$repo" == */* && -f "$projects_file" ]] || return 1
  local normalized_repo
  normalized_repo="$(printf '%s' "$repo" | tr '[:upper:]' '[:lower:]')"
  sed -n 's/^[[:space:]]*github_repo:[[:space:]]*//p' "$projects_file" \
    | tr -d '"' \
    | tr '[:upper:]' '[:lower:]' \
    | grep -Fxq "$normalized_repo"
}

# --- Argument parsing --------------------------------------------------------

SOURCE_URL=""
SLUG=""
BRANCH=""
SOURCE_DIR_OVERRIDE=""
BASE_BRANCH="main"
BUMPS_DIR_OVERRIDE=""
AGENT="${LEAN_POOL_AGENT:-claude}"
MODEL="${LEAN_POOL_AGENT_MODEL:-}"
EFFORT="${LEAN_POOL_AGENT_EFFORT:-}"
KEEP_WORKTREE=false
DRY_RUN=false
SHARED_PACKAGES_ENABLED=true
CLEANUP=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --slug)         SLUG="$2"; shift 2 ;;
    --branch)       BRANCH="$2"; shift 2 ;;
    --source-dir)   SOURCE_DIR_OVERRIDE="$2"; shift 2 ;;
    --base)         BASE_BRANCH="$2"; shift 2 ;;
    --bumps-dir)    BUMPS_DIR_OVERRIDE="$2"; shift 2 ;;
    --agent)        AGENT="$2"; shift 2 ;;
    --model)        MODEL="$2"; shift 2 ;;
    --effort)       EFFORT="$2"; shift 2 ;;
    --no-shared-packages) SHARED_PACKAGES_ENABLED=false; shift ;;
    --cleanup)      CLEANUP=true; shift ;;
    --keep-worktree) KEEP_WORKTREE=true; shift ;;
    --dry-run)      DRY_RUN=true; shift ;;
    -h|--help)
      sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    -*)
      die "Unknown option: $1"
      ;;
    *)
      [[ -z "$SOURCE_URL" ]] || die "Multiple positional args; only one URL expected."
      SOURCE_URL="$1"; shift
      ;;
  esac
done

[[ -n "$SOURCE_URL" ]] || die "Missing source repo URL. See $0 --help."

case "$AGENT" in
  claude)
    MODEL="${MODEL:-claude-opus-4-7}"
    EFFORT="${EFFORT:-max}"
    ;;
  codex)
    MODEL="${MODEL:-gpt-5.5}"
    EFFORT="${EFFORT:-xhigh}"
    ;;
  *)
    die "Unknown agent '$AGENT'. Expected 'claude' or 'codex'."
    ;;
esac

# --- Resolve paths -----------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_POOL_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"
[[ "$(basename "$LEAN_POOL_ROOT")" == "lean-pool" ]] \
  || warn "Expected to be inside a lean-pool checkout; found $LEAN_POOL_ROOT."

DEFAULT_BUMPS_DIR="$(dirname "$LEAN_POOL_ROOT")/lean-pool-bumps"
BUMPS_DIR="${BUMPS_DIR_OVERRIDE:-${LEAN_POOL_BUMPS_DIR:-$DEFAULT_BUMPS_DIR}}"
mkdir -p "$BUMPS_DIR"

# The raw URL segment (e.g. "KakeyaFiniteFields", "partial-regularity").
# Used for the camel-case namespace because it preserves any existing case.
RAW_SLUG="${SOURCE_URL%.git}"
RAW_SLUG="${RAW_SLUG##*/}"

# Lowercase slug used for directories, branch, and projects.yml entry.
[[ -n "$SLUG" ]] || SLUG="$(echo "$RAW_SLUG" | tr '[:upper:]' '[:lower:]')"
[[ "$SLUG" =~ ^[a-z0-9][a-z0-9_-]*$ ]] \
  || die "Derived slug '$SLUG' is not a valid identifier; pass --slug explicitly."

# UpperCamel form for the suggested Lean namespace. Derived from RAW_SLUG
# so existing CamelCase ("KakeyaFiniteFields") survives, and kebab/snake
# cases get word-joined ("partial-regularity" -> "PartialRegularity").
# Computed portably so the script runs under bash 3.2 (macOS /bin/bash).
SLUG_CAMEL="$(printf '%s' "$RAW_SLUG" \
  | awk -F'[-_]' '{for(i=1;i<=NF;i++) printf "%s%s", toupper(substr($i,1,1)), substr($i,2)}')"

[[ -n "$BRANCH" ]] || BRANCH="import/$SLUG"

WORKTREE="$BUMPS_DIR/lean-pool-$SLUG"
SOURCE_DIR="${SOURCE_DIR_OVERRIDE:-$BUMPS_DIR/$SLUG-source}"
AGENT_LOG="$BUMPS_DIR/$SLUG-agent.log.jsonl"

log "Source URL:    $SOURCE_URL"
log "Slug:          $SLUG  (namespace: LeanPool.$SLUG_CAMEL)"
log "Branch:        $BRANCH"
log "Lean-pool:     $LEAN_POOL_ROOT"
log "Worktree:      $WORKTREE"
log "Source clone:  $SOURCE_DIR"
log "Agent log:     $AGENT_LOG"
log "Agent:         $AGENT"
log "Model:         $MODEL  (effort: $EFFORT)"

if SOURCE_GITHUB_REPO="$(github_repo_of "$SOURCE_URL")" \
   && source_repo_registered "$SOURCE_GITHUB_REPO"; then
  ok "Source repo $SOURCE_GITHUB_REPO is already registered in LeanPool/projects.yml; skipping."
  exit 0
fi

# --- Sanity checks -----------------------------------------------------------

case "$AGENT" in
  claude) command -v claude >/dev/null || die "claude CLI not found in PATH." ;;
  codex)  command -v codex >/dev/null || die "codex CLI not found in PATH." ;;
esac
command -v gh >/dev/null     || die "gh CLI not found in PATH; needed to open the PR."
command -v python3 >/dev/null || die "python3 not found in PATH; needed to scan Lean diffs."
gh auth status >/dev/null 2>&1 || die "gh is not authenticated. Run 'gh auth login' first."

# Refuse to clobber an existing worktree silently.
if [[ -e "$WORKTREE" ]]; then
  die "Worktree path already exists: $WORKTREE
       Remove it with: git -C $LEAN_POOL_ROOT worktree remove --force $WORKTREE"
fi

# Refuse to overwrite a branch that already exists locally.
if git -C "$LEAN_POOL_ROOT" rev-parse --verify "refs/heads/$BRANCH" >/dev/null 2>&1; then
  die "Branch already exists locally: $BRANCH
       Delete with: git -C $LEAN_POOL_ROOT branch -D $BRANCH"
fi

# --- Clone (or reuse) the source repo ---------------------------------------

if [[ -n "$SOURCE_DIR_OVERRIDE" ]]; then
  [[ -d "$SOURCE_DIR" ]] || die "--source-dir does not exist: $SOURCE_DIR"
  log "Reusing source clone at $SOURCE_DIR"
elif [[ -d "$SOURCE_DIR" ]]; then
  log "Source clone already present; pulling latest"
  git -C "$SOURCE_DIR" fetch --all --prune
  git -C "$SOURCE_DIR" pull --ff-only || warn "git pull --ff-only failed; continuing with current state."
else
  log "Cloning $SOURCE_URL into $SOURCE_DIR"
  git clone "$SOURCE_URL" "$SOURCE_DIR"
fi

# --- Create the lean-pool worktree ------------------------------------------

# Retry a git command a few times — when several imports run concurrently they
# briefly contend on $LEAN_POOL_ROOT/.git locks (refs, worktrees list).
git_retry() {
  local n=0
  until git "$@"; do
    n=$((n + 1))
    [[ $n -ge 5 ]] && return 1
    warn "git $* failed (attempt $n); retrying in $((n * 3))s..."
    sleep $((n * 3 + RANDOM % 3))
  done
}

# Make sure base branch is up to date so we branch off something reasonable.
log "Fetching origin and updating base $BASE_BRANCH"
git_retry -C "$LEAN_POOL_ROOT" fetch origin --prune || warn "git fetch failed; using whatever refs are local."
BASE_FROM="origin/$BASE_BRANCH"
if ! git -C "$LEAN_POOL_ROOT" rev-parse --verify "$BASE_FROM" >/dev/null 2>&1; then
  warn "$BASE_FROM not found; falling back to local $BASE_BRANCH"
  BASE_FROM="$BASE_BRANCH"
fi

# Pin BASE_REF to the actual SHA the worktree is created from. Using the ref
# name would silently drift if `origin/main` advances during the multi-hour
# agent run — the allowlist guard would then diff against a different base
# than the worktree was branched off, missing additions that overlap files
# now on `main`.
BASE_REF="$(git -C "$LEAN_POOL_ROOT" rev-parse --verify "$BASE_FROM")"
log "Creating worktree at $WORKTREE on new branch $BRANCH (from $BASE_FROM @ ${BASE_REF:0:10})"
git_retry -C "$LEAN_POOL_ROOT" worktree add -b "$BRANCH" "$WORKTREE" "$BASE_REF"

# --- Dependencies: shared, prebuilt .lake/packages store --------------------
#
# All import worktrees build the same `LeanPool` target against lean-pool's
# pinned `lake-manifest.json`, so `.lake/packages` (dep checkouts + the ~5 GB
# of prebuilt Mathlib oleans `lake exe cache get` unpacks) is byte-identical
# across runs. Seed it once into a manifest-keyed shared store and symlink each
# worktree at it; the worktree's own build output stays in its private
# `.lake/build`, so concurrent agents read the shared oleans but never write
# to them. `--no-shared-packages` opts out (one private copy per worktree).

mkdir -p "$WORKTREE/.lake"

fetch_packages_into_worktree() {
  # Resolves deps into $WORKTREE/.lake/packages and unpacks the Mathlib cache.
  log "Pre-fetching dependencies + Mathlib cache (slow on first run)..."
  ( cd "$WORKTREE" && lake exe cache get >/dev/null 2>&1 ) \
    || warn "lake exe cache get failed; the agent will retry."
}

if ! $SHARED_PACKAGES_ENABLED; then
  fetch_packages_into_worktree
else
  SHARED_PACKAGES_ROOT="$BUMPS_DIR/.shared-lake-packages"
  MANIFEST_KEY="$(shasum -a 256 "$WORKTREE/lake-manifest.json" 2>/dev/null | cut -c1-16 || echo nokey)"
  SHARED_PACKAGES="$SHARED_PACKAGES_ROOT/$MANIFEST_KEY"
  SHARED_PACKAGES_READY="$SHARED_PACKAGES/.ready"
  SEED_LOCK="$SHARED_PACKAGES_ROOT/$MANIFEST_KEY.seeding.lock"
  mkdir -p "$SHARED_PACKAGES_ROOT"

  link_shared_packages() {
    rm -rf "$WORKTREE/.lake/packages"
    ln -s "$SHARED_PACKAGES" "$WORKTREE/.lake/packages"
    log "Linked .lake/packages -> shared store ($MANIFEST_KEY)."
  }

  if [[ -f "$SHARED_PACKAGES_READY" ]]; then
    link_shared_packages
  elif mkdir "$SEED_LOCK" 2>/dev/null; then
    # We won the race to seed the shared store; release the lock on exit.
    trap 'rmdir "$SEED_LOCK" 2>/dev/null || true' EXIT
    log "Seeding shared dependency store ($MANIFEST_KEY)..."
    fetch_packages_into_worktree
    if [[ -d "$WORKTREE/.lake/packages" && ! -L "$WORKTREE/.lake/packages" ]]; then
      rm -rf "$SHARED_PACKAGES"
      mv "$WORKTREE/.lake/packages" "$SHARED_PACKAGES"
      touch "$SHARED_PACKAGES_READY"
      link_shared_packages
      ok "Shared store ready at $SHARED_PACKAGES (future imports reuse it)."
    else
      warn "Dependency fetch left no .lake/packages; skipping shared store this run."
    fi
    rmdir "$SEED_LOCK" 2>/dev/null || true
  else
    warn "Shared store is being seeded by another run; using a private .lake/packages this time."
    fetch_packages_into_worktree
  fi
fi

# --- Build the agent prompt --------------------------------------------------

LEAN_TOOLCHAIN="$(cat "$LEAN_POOL_ROOT/lean-toolchain")"

read -r -d '' PROMPT <<PROMPT_EOF || true
You are an autonomous Lean engineer importing an external Lean formalization into the lean-pool monorepo. You run unattended — there is no one watching and no one to hand off to. Your goal is a complete, working import: all of the CI checks below passing. A partial result is a failure; be thorough and relentless.

# Inputs
- Source repository (already cloned, treat as read-only): ${SOURCE_DIR}
- Source URL: ${SOURCE_URL}
- Target slug: ${SLUG}
- lean-pool worktree (your CWD; you edit here): ${WORKTREE}
- Branch (already created and checked out): ${BRANCH}

# Toolchain target (lean-pool's pinned versions)
- Lean: ${LEAN_TOOLCHAIN}
- Mathlib: matching rev (see ${WORKTREE}/lakefile.toml)
- Dependencies and the Mathlib cache are already fetched; \`.lake/packages\` may be a symlink to a shared, prebuilt store, so \`lake build LeanPool\` should not need to rebuild Mathlib and you should not run \`lake exe cache get\` or \`lake update\`.

# Goal
Vendor the source repo's Lean content into LeanPool/${SLUG}/, bump it to lean-pool's toolchain, register it in LeanPool/projects.yml, and make the local CI checks pass.

# Step-by-step
1. Read ${SOURCE_DIR}/README.md (and the source repo's lakefile, lean-toolchain, LICENSE) to figure out: title, authors, main declarations, tags, license. If the license is incompatible with Apache-2.0 (lean-pool is Apache-2.0), STOP — write IMPORT_NOTES.md explaining (do NOT commit it; see note below).
2. Decide which .lean files to vendor. Skip examples/tests/scratch unless the formalization depends on them.
3. Copy the chosen .lean files into LeanPool/${SLUG}/, preserving subdirectory structure. The Lean module path for vendored files becomes \`LeanPool.${SLUG_CAMEL}.…\`; suggested top-level Lean namespace is \`LeanPool.${SLUG_CAMEL}\` (existing inner namespaces from the source repo can be kept underneath).
4. Update each vendored .lean file:
   - Prepend the lean-pool file header (see existing LeanPool/Basic.lean and .github/CODE_QUALITY.md §7). Year 2026, the source authors, Apache-2.0.
   - Replace any broad \`import Mathlib\` with the specific modules actually used.
   - Strip every \`set_option\` directive.
   - Strip diagnostic commands: \`#check\`, \`#print\`, \`#eval\`, \`#reduce\`, \`#guard_msgs\`, \`#lint\`.
   - Reject any file that depends on \`sorry\`, \`admit\`, a new \`axiom\`/\`constant\`, or uses \`unsafe\`/\`partial\`/\`opaque\`/\`@[extern]\`. First try to fix it (complete the proof; replace the unsafe construct). Only if you genuinely cannot, after real effort, may that one file be excluded as a last resort — and record in \`IMPORT_NOTES.md\` exactly what blocked you and what you tried.
5. For every directory you create under LeanPool/, add an import-only index .lean file with a module docstring (style matches LeanPool/Basic.lean's header).
6. Run \`lake exe mk_all\` to regenerate LeanPool.lean.
7. Add a project entry to LeanPool/projects.yml. Required keys: slug, title, entry_module, authors (list), source ({url|arxiv|doi}), status: verified, main_declarations (list of fully-qualified names), tags (list). Optional: msc.
8. Iterate — persistently, as many rounds as it takes — until ALL of these pass cleanly inside ${WORKTREE}:
   - \`lake exe mk_all --check\`
   - \`lake build LeanPool\` — and the build log must contain no warnings (CI greps for \`warning:\`).
   - \`lake exe runLinter LeanPool\`
   - \`lake exe lint-style LeanPool\`
   - \`cd python && uv sync --locked && uv run python -m lean_pool.quality --repo ..\`
9. Commit your work with a clear message. Use multiple commits if it helps — first \`Vendor <name> from <url>\`, then \`Bump to ${LEAN_TOOLCHAIN}\`, etc. Do NOT \`git add\`/commit \`IMPORT_NOTES.md\` (it's read for the PR body only — committing it fails the Content-only PR gate). Do not include AI-generated tags ("Generated with Claude", "Co-Authored-By: …") in commit messages — see CONTRIBUTING.md.
10. STOP. Do not push. Do not open a PR. The wrapper script handles that.

# Hard rules (CI will fail otherwise — see .github/CODE_QUALITY.md)
- No \`sorry\`, \`admit\`, new \`axiom\`/\`constant\`, \`unsafe\`, \`partial\`, \`opaque\`, \`@[extern]\`, or \`set_option\` anywhere in committed files.
- No \`#check\`/\`#print\`/\`#eval\`/\`#reduce\`/\`#guard_msgs\`/\`#lint\` in committed files.
- File header must match the format in .github/CODE_QUALITY.md §7 exactly.
- All imports at the top of the file (no mid-file imports).
- No file over 10000 non-blank/non-comment lines; no proof body over 200 lines.
- The build must be warning-free (CI fails on any \`warning:\` in the log).

# Stay in your lane — what you may COMMIT
You may add or modify, AND COMMIT, ONLY: \`LeanPool.lean\` (regenerate via \`lake exe mk_all\`), files under \`LeanPool/\` (including \`LeanPool/projects.yml\`). That's it — the Content-only PR CI gate rejects a PR that touches anything else. You may *write* \`IMPORT_NOTES.md\` locally (the wrapper reads it for the PR body) but you must NOT commit it. Do NOT modify ANYTHING else at all — in particular do NOT touch \`.github/\` (CI workflows, CODE_QUALITY.md), \`python/\` (incl. \`lean_pool/quality.py\`), \`scripts/\` (incl. \`nolints-style.txt\`), \`lakefile.toml\`, \`lean-toolchain\`, \`lake-manifest.json\`, \`AGENTS.md\`, \`CLAUDE.md\`, \`README.md\`, \`CONTRIBUTING.md\`, or \`.gitignore\`. Do NOT introduce any waiver/exception/escape-hatch: no \`size-limit-ok\` comment, no entry in \`scripts/nolints-style.txt\`, no \`set_option linter.X false\`, no linter toggle in \`lakefile.toml\`, no editing of \`quality.py\` or a workflow to skip a check. If a check fails, fix the code, not the check. If a proof exceeds 200 lines, split it into lemmas; if a file exceeds 10000 lines, split it into modules. The wrapper script reverts any committed change outside that allowlist (and untracks \`IMPORT_NOTES.md\`) before opening the PR, so out-of-scope edits accomplish nothing.

# Do not give up
A partial import is a failure, not an acceptable stopping point. Bumping pain is expected — work through it: when a Mathlib declaration moved or was renamed, find the current name (grep the Mathlib source under \`.lake/packages/mathlib\`, search for nearby lemmas, check release notes); when a lemma you relied on no longer exists, prove it yourself in your own namespace; when a proof breaks under the new Mathlib, repair it; when \`simp\`/\`omega\`/\`aesop\` no longer closes a goal, find the steps that do. Excluding a file is the absolute last resort, permissible only after you have genuinely exhausted these avenues, and every exclusion must be justified in \`IMPORT_NOTES.md\` (local scratch — not committed) with the specific blocker and what you attempted. Keep iterating — many rounds if that's what it takes — until \`lake build LeanPool\` (warning-free), \`lake exe runLinter LeanPool\`, \`lake exe lint-style LeanPool\`, and the \`quality\` check are all clean. Do not stop early.

# Helpful pointers
- ${WORKTREE}/AGENTS.md and ${WORKTREE}/CLAUDE.md — project conventions.
- ${WORKTREE}/LeanPool/Basic.lean — example file with a correct header.
- ${WORKTREE}/.github/CODE_QUALITY.md — full quality contract.
- ${WORKTREE}/.github/workflows/lean_action_ci.yml — exact CI commands.

Begin.
PROMPT_EOF

# --- Run the agent -----------------------------------------------------------

if $DRY_RUN; then
  ok "Dry run complete. Worktree and source clone are ready."
  case "$AGENT" in
    claude) log "Would have run: claude -p ... --model $MODEL --effort $EFFORT" ;;
    codex)  log "Would have run: codex exec ... --model $MODEL --config model_reasoning_effort=\"$EFFORT\"" ;;
  esac
  exit 0
fi

log "Starting headless $AGENT agent. Tail the log with:"
log "  tail -f $AGENT_LOG"
log "(This may take 20-60+ minutes for a non-trivial repo.)"
log "Note: macOS clamshell (lid-close) sleep is NOT prevented by this script."
log "      Keep the lid open, or the agent's API connection will drop and wedge."

# caffeinate -i prevents *idle* sleep for the duration of the agent run.
# It does NOT prevent lid-close sleep; if the laptop is closed, the agent's
# HTTPS connection dies and the process hangs on a dead socket. (Array is
# always non-empty so it expands cleanly under `set -u` in bash 3.2.)
AGENT_EXIT=0
case "$AGENT" in
  claude)
    if command -v caffeinate >/dev/null; then
      AGENT_RUNNER=(caffeinate -i claude)
    else
      AGENT_RUNNER=(claude)
    fi
    (
      cd "$WORKTREE"
      "${AGENT_RUNNER[@]}" -p "$PROMPT" \
        --model "$MODEL" \
        --effort "$EFFORT" \
        --permission-mode bypassPermissions \
        --output-format stream-json \
        --verbose \
        --add-dir "$SOURCE_DIR"
    ) > "$AGENT_LOG" 2>&1 || AGENT_EXIT=$?
    ;;
  codex)
    if command -v caffeinate >/dev/null; then
      AGENT_RUNNER=(caffeinate -i codex)
    else
      AGENT_RUNNER=(codex)
    fi
    (
      cd "$WORKTREE"
      "${AGENT_RUNNER[@]}" --ask-for-approval never exec \
        -C "$WORKTREE" \
        --add-dir "$SOURCE_DIR" \
        --model "$MODEL" \
        --config "model_reasoning_effort=\"$EFFORT\"" \
        --sandbox danger-full-access \
        --json \
        "$PROMPT"
    ) > "$AGENT_LOG" 2>&1 || AGENT_EXIT=$?
    ;;
esac

if [[ $AGENT_EXIT -eq 0 ]]; then
  ok "Agent exited cleanly."
else
  warn "Agent exited with code $AGENT_EXIT. Will still push and open a PR with whatever progress it made."
fi

# --- Commit any uncommitted progress, push, and open the PR -----------------

cd "$WORKTREE"

# IMPORT_NOTES.md / FAILURE.md are per-PR scratch: the wrapper reads them for
# the PR body below, but they must never be committed (the Content-only PR gate
# rejects anything outside LeanPool/**). Keep the working-tree copies; just keep
# them out of every commit the wrapper makes, and untrack them if the agent
# committed them.
SCRATCH_FILES=(IMPORT_NOTES.md FAILURE.md)
unstage_scratch() { git reset -q -- "${SCRATCH_FILES[@]}" 2>/dev/null || true; }

# If the agent left changes uncommitted, commit them so the PR shows everything.
if ! git diff --quiet || ! git diff --cached --quiet || [[ -n "$(git ls-files --others --exclude-standard)" ]]; then
  warn "Uncommitted changes detected; committing as WIP."
  git add -A
  unstage_scratch
  # After unstaging scratch files (IMPORT_NOTES.md / FAILURE.md), there may be
  # nothing left to commit if the agent only added those. That's not an error.
  if ! git diff --cached --quiet; then
    git commit -m "WIP: agent partial progress on $SLUG import" \
      -m "The wrapper script committed this on the agent's behalf because the agent left changes uncommitted (likely exited early)."
  fi
fi

# If the agent's own commits tracked the scratch files, untrack them (keeping the
# working-tree copies for the PR body).
if git ls-files -- "${SCRATCH_FILES[@]}" | grep -q .; then
  warn "Agent committed per-PR scratch file(s); untracking: $(git ls-files -- "${SCRATCH_FILES[@]}" | tr '\n' ' ')"
  git rm --cached -q -- "${SCRATCH_FILES[@]}" 2>/dev/null || true
  git commit -q -m "Drop per-PR scratch files from the import" \
    -m "IMPORT_NOTES.md / FAILURE.md are read for the PR body but are never committed (Content-only PR gate)." || true
fi

# --- Guard: revert anything the agent touched outside the import allowlist ---
# An import may only add/modify LeanPool.lean and LeanPool/**. If the agent
# edited CI workflows, quality.py, lint allowlists, lakefile/toolchain/manifest,
# etc. — or *added* any file outside LeanPool/ (a sneak attempt to slip a new
# script or workflow into the PR) — undo it before the PR goes up. Reverting
# (rather than refusing) keeps the legitimate import.
#
# The diff is computed with --diff-filter=ACMRTUXB and parsed with -z so file
# names with spaces survive; M/A/D/R/T are all handled, with deletes restored
# from BASE_REF. BASE_REF is pinned to a SHA up top, so this stays correct
# even if origin/main advanced during the agent run.
OUT_OF_SCOPE=()
status=""
while IFS= read -r -d '' tok; do
  if [[ -z "$status" ]]; then status="$tok"; continue; fi
  p="$tok"; s="$status"; status=""
  case "$p" in
    LeanPool.lean|LeanPool/*) continue ;;   # allowed
  esac
  case "$s" in
    A|A?*)        # added by the agent: just remove
      git rm -f --quiet -- "$p" 2>/dev/null || rm -f -- "$p" ;;
    D|D?*)        # deleted by the agent: restore from base
      git checkout "$BASE_REF" -- "$p" 2>/dev/null || true ;;
    M*|T*|U*|X*|B*)  # modified / type-changed / unmerged / etc.: restore base version
      if git cat-file -e "$BASE_REF:$p" 2>/dev/null; then
        git checkout "$BASE_REF" -- "$p"
      else
        # Wasn't in BASE_REF either, so this is effectively an add — remove.
        git rm -f --quiet -- "$p" 2>/dev/null || rm -f -- "$p"
      fi ;;
    R*)           # rename: handled as an old-path delete + new-path add — both names
                  # land in this loop separately, so no extra work here.
      : ;;
    *)            # unknown status: be safe — restore from base if it exists, else remove
      if git cat-file -e "$BASE_REF:$p" 2>/dev/null; then
        git checkout "$BASE_REF" -- "$p"
      else
        git rm -f --quiet -- "$p" 2>/dev/null || rm -f -- "$p"
      fi ;;
  esac
  OUT_OF_SCOPE+=("$s $p")
done < <(git diff -z --name-status --diff-filter=ACDMRTUXB "$BASE_REF..HEAD")

if [[ ${#OUT_OF_SCOPE[@]} -gt 0 ]]; then
  warn "Agent changed ${#OUT_OF_SCOPE[@]} path(s) outside the import allowlist — reverting:"
  for entry in "${OUT_OF_SCOPE[@]}"; do warn "  $entry"; done
  git add -A
  unstage_scratch
  git commit -m "Revert agent edits outside the import allowlist" \
    -m "Auto-reverted by scripts/import-formalization.sh (an import may only touch LeanPool.lean and LeanPool/): ${OUT_OF_SCOPE[*]}" || true
fi

# The allowlist above intentionally permits LeanPool/** because imports live
# there. That does not permit Lean escape hatches or diagnostics inside the
# imported Lean files, so scan the committed Lean diff before opening the PR.
FORBIDDEN_LEAN_DIFF="$(
  python3 - "$BASE_REF" <<'PY'
import re
import subprocess
import sys
from pathlib import Path

base_ref = sys.argv[1]
forbidden = re.compile(
    r"(?<![A-Za-z0-9_])set_option(?![A-Za-z0-9_])"
    r"|maxHeartbeats"
    r"|synthInstance\.maxHeartbeats"
    r"|#(?:check|print|eval|reduce|guard_msgs|lint)"
    r"|(?<![A-Za-z0-9_])(?:sorry|admit|axiom|constant|unsafe|partial|opaque)(?![A-Za-z0-9_])"
    r"|@\[\s*extern"
)
hunk_header = re.compile(r"^@@ .* \+(\d+)(?:,(\d+))? @@")


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank Lean comments and strings while preserving line numbers."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth > 0:
            if pair == "/-":
                block_depth += 1
                result.append("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.append("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            in_line_comment = True
            result.append("  ")
            index += 2
        elif pair == "/-":
            block_depth = 1
            result.append("  ")
            index += 2
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1

    return "".join(result)


diff = subprocess.run(
    [
        "git",
        "diff",
        "--unified=0",
        f"{base_ref}..HEAD",
        "--",
        "LeanPool.lean",
        "LeanPool/**/*.lean",
    ],
    check=True,
    stdout=subprocess.PIPE,
    text=True,
).stdout

added_lines: dict[str, set[int]] = {}
current_file: str | None = None
new_line: int | None = None

for raw_line in diff.splitlines():
    if raw_line.startswith("+++ b/"):
        current_file = raw_line[6:]
        new_line = None
        continue
    if raw_line.startswith("+++ /dev/null"):
        current_file = None
        new_line = None
        continue

    match = hunk_header.match(raw_line)
    if match:
        new_line = int(match.group(1))
        continue

    if current_file is None or new_line is None:
        continue

    if raw_line.startswith("+") and not raw_line.startswith("+++"):
        if current_file.endswith(".lean"):
            added_lines.setdefault(current_file, set()).add(new_line)
        new_line += 1
    elif raw_line.startswith("-") and not raw_line.startswith("---"):
        continue
    elif raw_line.startswith("\\ No newline"):
        continue
    else:
        new_line += 1

for file_name in sorted(added_lines):
    path = Path(file_name)
    if not path.exists():
        continue
    original_lines = path.read_text().splitlines()
    stripped_lines = strip_lean_comments_and_strings(path.read_text()).splitlines()
    for line_number in sorted(added_lines[file_name]):
        if line_number > len(stripped_lines):
            continue
        if forbidden.search(stripped_lines[line_number - 1]):
            original = original_lines[line_number - 1] if line_number <= len(original_lines) else ""
            print(f"{file_name}: {original}")
PY
)"

if [[ -n "$FORBIDDEN_LEAN_DIFF" ]]; then
  warn "Forbidden Lean token(s) found in the committed LeanPool diff; recording FAILURE.md (not committed — surfaced in the PR body)."
  {
    echo "# Import guard failure"
    echo ""
    echo "The wrapper found forbidden Lean tokens in added LeanPool lines:"
    echo ""
    printf '%s\n' "$FORBIDDEN_LEAN_DIFF" | sed 's/^/- `/' | sed 's/$/`/'
    echo ""
    echo "Remove these escape hatches or diagnostics before merging."
  } > FAILURE.md
fi

# --- Post-revert sanity check: the committed diff must be content-only ------
# Belt-and-suspenders for the allowlist guard above. If anything outside the
# allowlist still shows up in the branch's diff against the base, refuse to
# push: the in-script guard has a bug and the Content-only PR CI gate would
# reject the PR anyway. Better to fail loudly here than to open a doomed PR.
LEFTOVER="$(
  git diff -z --name-only --diff-filter=ACMRTUXB "$BASE_REF..HEAD" \
    | tr '\0' '\n' \
    | { grep -vE '^(LeanPool\.lean|LeanPool/.+)$' || true; }
)"
if [[ -n "$LEFTOVER" ]]; then
  error "Allowlist guard let non-content paths slip through. Not pushing. Offending paths:"
  printf '%s\n' "$LEFTOVER" | sed 's/^/  - /' >&2
  error "Worktree left at $WORKTREE for inspection. Fix the wrapper, then re-run."
  exit 2
fi

# Bail out cleanly if there's literally nothing to PR.
COMMIT_COUNT="$(git rev-list --count "$BASE_REF..HEAD" 2>/dev/null || echo 0)"
if [[ "$COMMIT_COUNT" == "0" ]]; then
  warn "No commits on $BRANCH beyond $BASE_REF. Nothing to push or PR."
  warn "The worktree is at $WORKTREE if you want to inspect it."
  exit 1
fi

log "Pushing $BRANCH ($COMMIT_COUNT commit(s)) to origin"
git_retry push -u origin "$BRANCH"

# Build a PR body that surfaces the import status honestly.
PR_TITLE="Import $SLUG formalization"
PR_BODY_FILE="$BUMPS_DIR/$SLUG-pr-body.md"
{
  echo "Imported from ${SOURCE_URL}."
  echo ""
  echo "**Slug:** \`$SLUG\`"
  echo "**Toolchain target:** \`$LEAN_TOOLCHAIN\`"
  echo "**Branch:** \`$BRANCH\` (auto-generated by \`scripts/import-formalization.sh\`)"
  echo "**Agent:** \`$AGENT\` using \`$MODEL\` at effort \`$EFFORT\`, exited with code \`$AGENT_EXIT\`."
  echo ""
  echo "**Commits on this branch:**"
  git --no-pager log "$BASE_REF..HEAD" --pretty=format:'- %h %s' || true
  echo ""
  if [[ -f "$WORKTREE/IMPORT_NOTES.md" ]]; then
    echo ""
    echo "## Import notes (from agent)"
    echo ""
    cat "$WORKTREE/IMPORT_NOTES.md"
  fi
  if [[ -f "$WORKTREE/FAILURE.md" ]]; then
    echo ""
    echo "## Agent flagged this import as blocked"
    echo ""
    cat "$WORKTREE/FAILURE.md"
  fi
  if [[ ${#OUT_OF_SCOPE[@]} -gt 0 ]]; then
    echo ""
    echo "## ⚠️ Out-of-scope edits reverted"
    echo ""
    echo "The agent modified files outside the import allowlist; the wrapper reverted them before opening this PR. Reverted paths:"
    echo ""
    for p in "${OUT_OF_SCOPE[@]}"; do echo "- \`$p\`"; done
    echo ""
    echo "If any of those changes were actually necessary, that's a signal the import isn't clean — review before merging."
  fi
  echo ""
  echo "---"
  echo "_Opened automatically by \`scripts/import-formalization.sh\`. Review the diff carefully before merging — the agent ran unattended._"
} > "$PR_BODY_FILE"

log "Opening PR against $BASE_BRANCH"
PR_URL="$(gh pr create \
  --base "$BASE_BRANCH" \
  --head "$BRANCH" \
  --title "$PR_TITLE" \
  --body-file "$PR_BODY_FILE")"

ok "PR opened: $PR_URL"

if $CLEANUP; then
  log "Removing worktree $WORKTREE (--cleanup); the pushed branch and PR stay."
  # `git worktree remove` deletes the dir, including the .lake/packages symlink
  # — never the shared store it points at. --force because .lake and the
  # agent's untracked files would otherwise block it.
  git -C "$LEAN_POOL_ROOT" worktree remove --force "$WORKTREE" \
    || warn "worktree remove failed; remove $WORKTREE by hand."
  log "Agent log kept at $AGENT_LOG."
else
  log "Worktree left at $WORKTREE for inspection."
  if ! $KEEP_WORKTREE; then
    log "When done, clean up with:"
    log "  git -C $LEAN_POOL_ROOT worktree remove --force $WORKTREE"
    log "  git -C $LEAN_POOL_ROOT branch -D $BRANCH   # only after the PR is merged/closed"
    if $SHARED_PACKAGES_ENABLED; then
      log "  rm -rf $BUMPS_DIR/.shared-lake-packages   # reclaims the shared ~5 GB dep store"
    fi
  fi
fi
