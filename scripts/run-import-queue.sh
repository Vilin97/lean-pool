#!/usr/bin/env bash
# Run the lean-pool import queue overnight: drive scripts/import-formalization.sh
# over a list of external repos, a few at a time, keeping the machine awake, then
# wait for the resulting PRs' CI to settle and print a summary.
#
# Usage:
#   scripts/run-import-queue.sh [options] [url ...]
#
# With no urls, uses the built-in default list (the 10 in
# candidates/import-queue.md).
#
# Options:
#   --jobs N           How many imports to run at once (default 2).
#   --urls-file F      Read newline-separated urls from F ('#' comments ok).
#   --agent NAME       Headless agent: claude or codex
#                      (default: $LEAN_POOL_AGENT or claude).
#   --model ID         Forwarded as LEAN_POOL_AGENT_MODEL.
#   --effort LEVEL     Forwarded as LEAN_POOL_AGENT_EFFORT.
#   --keep-worktrees   Don't pass --cleanup to the import script.
#   --no-caffeinate    Don't re-exec under `caffeinate`.
#   --ci-timeout MIN   Minutes to wait for CI to settle at the end (default 150;
#                      0 = don't wait, just list the PRs).
#   --dry-run          Print the plan and exit.
#
# ┌─ READ THIS BEFORE LEAVING IT OVERNIGHT ────────────────────────────────────┐
# │ caffeinate stops *idle* sleep but NOT lid-close (clamshell) sleep. If the   │
# │ laptop sleeps, every running agent's API connection drops and the whole run │
# │ stalls until the machine wakes. Keep the lid OPEN and the machine PLUGGED   │
# │ IN for the entire run.                                                      │
# └────────────────────────────────────────────────────────────────────────────┘
#
# Usage, not cost: each import is one headless agent. The default is Claude;
# set LEAN_POOL_AGENT=codex (or pass --agent codex) to use Codex instead.
# For Codex, the import script defaults to gpt-5.5 with xhigh reasoning. Ten
# long runs is a heavy draw on whichever provider/account is selected; use
# --jobs 1 or a lower LEAN_POOL_AGENT_EFFORT to go easier on limits.
#
# Resumable: an import whose `import/<slug>` branch already exists on origin is
# skipped, so re-running the queue picks up where it left off.

set -euo pipefail

# --- Logging -----------------------------------------------------------------

C_RESET=$'\033[0m'; C_RED=$'\033[31m'; C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_BLUE=$'\033[34m'
log()   { printf '%s[queue %s]%s %s\n' "$C_BLUE"   "$(date +%H:%M:%S)" "$C_RESET" "$*" >&2; }
warn()  { printf '%s[queue %s]%s %s\n' "$C_YELLOW"  "$(date +%H:%M:%S)" "$C_RESET" "$*" >&2; }
error() { printf '%s[queue %s]%s %s\n' "$C_RED"    "$(date +%H:%M:%S)" "$C_RESET" "$*" >&2; }
ok()    { printf '%s[queue %s]%s %s\n' "$C_GREEN"  "$(date +%H:%M:%S)" "$C_RESET" "$*" >&2; }
die()   { error "$*"; exit 1; }

# --- Paths -------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMPORT_SCRIPT="$SCRIPT_DIR/import-formalization.sh"
[[ -x "$IMPORT_SCRIPT" ]] || die "Can't find $IMPORT_SCRIPT (or it's not executable)."
LEAN_POOL_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"
DEFAULT_BUMPS_DIR="$(dirname "$LEAN_POOL_ROOT")/lean-pool-bumps"
BUMPS_DIR="${LEAN_POOL_BUMPS_DIR:-$DEFAULT_BUMPS_DIR}"
AGENT="${LEAN_POOL_AGENT:-claude}"
# owner/name of the lean-pool remote, for `gh`.
REPO_SLUG="$(git -C "$LEAN_POOL_ROOT" remote get-url origin 2>/dev/null \
  | sed -E 's#(git@github.com:|https://github.com/)##; s#\.git$##' || echo "")"

# Default queue — keep in sync with candidates/import-queue.md (ordered by
# ascending import risk: smallest toolchain jump first).
DEFAULT_URLS=(
  https://github.com/math-inc/Erdos1196
  https://github.com/pitmonticone/SumsThreeSquares
  https://github.com/mrdouglasny/OSforGFF
  https://github.com/frenzymath/Anderson-Conjecture
  https://github.com/frenzymath/Archon-FirstProof-Results
  https://github.com/ShangtongZhang/rl-theory-in-lean
  https://github.com/AxiomMath/ramanujan-tau-misses-primes
  https://github.com/AxiomMath/partial-regularity
  https://github.com/AxiomMath/dead-ends
  https://github.com/AxiomMath/lattice-triangle
)

slug_of() { local u="${1%.git}"; printf '%s' "${u##*/}" | tr '[:upper:]' '[:lower:]'; }

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

is_registered_source() {
  local repo normalized_repo
  repo="$(github_repo_of "$1")" || return 1
  [[ "$repo" == */* ]] || return 1
  [[ -f "$LEAN_POOL_ROOT/LeanPool/projects.yml" ]] || return 1
  normalized_repo="$(printf '%s' "$repo" | tr '[:upper:]' '[:lower:]')"
  sed -n 's/^[[:space:]]*github_repo:[[:space:]]*//p' "$LEAN_POOL_ROOT/LeanPool/projects.yml" \
    | tr -d '"' \
    | tr '[:upper:]' '[:lower:]' \
    | grep -Fxq "$normalized_repo"
}

# --- One import (also the worker invoked by the parallel fan-out) ------------
#
# `run-import-queue.sh --run-one [--keep-worktrees] <url>` does exactly one
# import; the main mode fans these out with `xargs -P`.

if [[ "${1:-}" == "--run-one" ]]; then
  shift
  KEEP=false; [[ "${1:-}" == "--keep-worktrees" ]] && { KEEP=true; shift; }
  URL="${1:?--run-one needs a url}"
  SLUG="$(slug_of "$URL")"
  QUEUE_DIR="$BUMPS_DIR/queue-logs"; mkdir -p "$QUEUE_DIR"
  LOGF="$QUEUE_DIR/$SLUG-import.log"
  if is_registered_source "$URL"; then
    log "SKIP  $SLUG — source already registered in LeanPool/projects.yml."
    exit 0
  fi
  # Skip if the branch already exists upstream (resume support).
  if git -C "$LEAN_POOL_ROOT" ls-remote --exit-code --heads origin "import/$SLUG" >/dev/null 2>&1; then
    log "SKIP  $SLUG — import/$SLUG already on origin."
    exit 0
  fi
  CLEAN_FLAG=(--cleanup); $KEEP && CLEAN_FLAG=()
  log "START $SLUG — log: $LOGF"
  if "$IMPORT_SCRIPT" "$URL" "${CLEAN_FLAG[@]}" >"$LOGF" 2>&1; then
    PR="$(grep -o 'PR opened: .*' "$LOGF" | tail -1 | sed 's/^PR opened: //')"
    ok "DONE  $SLUG — ${PR:-(no PR line found; check $LOGF)}"
  else
    rc=$?
    warn "ENDED $SLUG — import script exited $rc (it still opens a PR on partial progress; check $LOGF)"
  fi
  exit 0
fi

# --- Argument parsing (main mode) -------------------------------------------

ORIG_ARGS=("$@")   # forwarded verbatim to the caffeinate re-exec

JOBS=2
URLS_FILE=""
KEEP_WORKTREES=false
USE_CAFFEINATE=true
CI_TIMEOUT_MIN=150
DRY_RUN=false
URLS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --jobs)          JOBS="$2"; shift 2 ;;
    --urls-file)     URLS_FILE="$2"; shift 2 ;;
    --agent)         AGENT="$2"; shift 2 ;;
    --model)         LEAN_POOL_AGENT_MODEL="$2"; export LEAN_POOL_AGENT_MODEL; shift 2 ;;
    --effort)        LEAN_POOL_AGENT_EFFORT="$2"; export LEAN_POOL_AGENT_EFFORT; shift 2 ;;
    --keep-worktrees) KEEP_WORKTREES=true; shift ;;
    --no-caffeinate) USE_CAFFEINATE=false; shift ;;
    --ci-timeout)    CI_TIMEOUT_MIN="$2"; shift 2 ;;
    --dry-run)       DRY_RUN=true; shift ;;
    --_caffeinated)  USE_CAFFEINATE=false; shift ;;   # internal: already wrapped
    -h|--help)       sed -n '2,35p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*)              die "Unknown option: $1" ;;
    *)               URLS+=("$1"); shift ;;
  esac
done

# Re-exec under caffeinate so idle sleep can't pause the run mid-flight.
# (Skipped for --dry-run, and when --no-caffeinate / --_caffeinated was given.)
if $USE_CAFFEINATE && ! $DRY_RUN && command -v caffeinate >/dev/null; then
  log "Re-executing under: caffeinate -dimsu"
  exec caffeinate -dimsu -- "$0" --_caffeinated "${ORIG_ARGS[@]+"${ORIG_ARGS[@]}"}"
fi

# Resolve the URL list: positional args > --urls-file > built-in default.
if [[ ${#URLS[@]} -eq 0 ]]; then
  if [[ -n "$URLS_FILE" ]]; then
    [[ -f "$URLS_FILE" ]] || die "--urls-file not found: $URLS_FILE"
    while IFS= read -r line; do
      line="${line%%#*}"; line="${line## }"; line="${line%% }"
      [[ -n "$line" ]] && URLS+=("$line")
    done < "$URLS_FILE"
  else
    URLS=("${DEFAULT_URLS[@]}")
  fi
fi
[[ ${#URLS[@]} -gt 0 ]] || die "No urls to process."

case "$AGENT" in
  claude|codex) ;;
  *) die "Unknown agent '$AGENT'. Expected 'claude' or 'codex'." ;;
esac
export LEAN_POOL_AGENT="$AGENT"

# --- Sanity checks -----------------------------------------------------------

command -v "$AGENT" >/dev/null || die "$AGENT CLI not found in PATH."
command -v gh >/dev/null     || die "gh CLI not found in PATH."
gh auth status >/dev/null 2>&1 || die "gh is not authenticated (gh auth login)."
[[ -n "$REPO_SLUG" ]] || warn "Could not determine the GitHub repo slug; the CI summary may be limited."

QUEUE_DIR="$BUMPS_DIR/queue-logs"; mkdir -p "$QUEUE_DIR"
RUNNER_LOG="$QUEUE_DIR/queue-runner.log"   # informational; this script also logs to stderr

log "lean-pool:   $LEAN_POOL_ROOT  ($REPO_SLUG)"
log "bumps dir:   $BUMPS_DIR"
log "queue logs:  $QUEUE_DIR/  (per-repo: <slug>-import.log, agent stream: <slug>-agent.log.jsonl)"
log "agent:       $AGENT  model: ${LEAN_POOL_AGENT_MODEL:-agent default}  effort: ${LEAN_POOL_AGENT_EFFORT:-agent default}"
log "concurrency: $JOBS    CI wait: ${CI_TIMEOUT_MIN}m    cleanup worktrees: $([[ $KEEP_WORKTREES == true ]] && echo no || echo yes)"
log "queue (${#URLS[@]} repos, in order):"
for u in "${URLS[@]}"; do log "  - $u  (-> import/$(slug_of "$u"))"; done

if $DRY_RUN; then ok "Dry run — nothing launched."; exit 0; fi

echo
warn "Keep the lid OPEN and the machine PLUGGED IN for the whole run — clamshell sleep will stall it."
echo

# --- Run: seed once, then fan out -------------------------------------------

# The first import seeds the shared .lake/packages store (see
# import-formalization.sh). Running it alone first means everyone after it just
# symlinks the store instead of two cold runs racing on the seed lock.
log "Phase 1/3 — seeding run: $(slug_of "${URLS[0]}")"
"$0" --run-one $($KEEP_WORKTREES && echo --keep-worktrees) "${URLS[0]}" || true

if [[ ${#URLS[@]} -gt 1 ]]; then
  log "Phase 2/3 — remaining $(( ${#URLS[@]} - 1 )) imports, $JOBS at a time"
  printf '%s\n' "${URLS[@]:1}" | grep . \
    | xargs -P "$JOBS" -n 1 -- "$0" --run-one $($KEEP_WORKTREES && echo --keep-worktrees)
fi
ok "All imports finished. PRs (if any) are open as drafts."

# --- Wait for CI and summarize ----------------------------------------------

summarize() {
  echo; echo "================ IMPORT QUEUE SUMMARY ($(date)) ================"
  printf "%-34s %-8s %-9s %s\n" "repo" "PR" "CI" "notes"
  for u in "${URLS[@]}"; do
    local slug; slug="$(slug_of "$u")"
    local pr_json pr_num pr_url ci notes=""
    pr_json="$(gh pr list --repo "$REPO_SLUG" --head "import/$slug" --state all --json number,url,isDraft --jq '.[0] // empty' 2>/dev/null || echo "")"
    if [[ -z "$pr_json" ]]; then
      printf "%-34s %-8s %-9s %s\n" "$slug" "—" "—" "no PR (see $QUEUE_DIR/$slug-import.log)"
      continue
    fi
    pr_num="$(printf '%s' "$pr_json" | sed -n 's/.*"number":\([0-9]*\).*/\1/p')"
    pr_url="$(printf '%s' "$pr_json" | sed -n 's/.*"url":"\([^"]*\)".*/\1/p')"
    local buckets
    buckets="$(gh pr checks "$pr_num" --repo "$REPO_SLUG" --json bucket,name 2>/dev/null || echo "[]")"
    if [[ "$buckets" == "[]" || -z "$buckets" ]]; then ci="?"; notes="no checks reported"
    elif printf '%s' "$buckets" | grep -q '"bucket":"fail"'; then ci="FAIL"
         notes="failed: $(printf '%s' "$buckets" | grep -o '"name":"[^"]*","bucket":"fail"' | sed 's/.*"name":"\([^"]*\)".*/\1/' | paste -sd, -)"
    elif printf '%s' "$buckets" | grep -q '"bucket":"pending"'; then ci="pending"; notes="still running"
    else ci="pass"
    fi
    printf "%-34s #%-7s %-9s %s\n" "$slug" "$pr_num" "$ci" "${notes:-$pr_url}"
  done
  echo "================================================================"
}

if [[ "$CI_TIMEOUT_MIN" -le 0 ]]; then
  log "Skipping CI wait (--ci-timeout 0)."
  summarize | tee -a "$RUNNER_LOG"
  exit 0
fi

log "Phase 3/3 — waiting up to ${CI_TIMEOUT_MIN}m for CI on the open PRs to settle..."
deadline=$(( $(date +%s) + CI_TIMEOUT_MIN * 60 ))
while :; do
  pending=0
  for u in "${URLS[@]}"; do
    slug="$(slug_of "$u")"
    pr_num="$(gh pr list --repo "$REPO_SLUG" --head "import/$slug" --state all --json number --jq '.[0].number // empty' 2>/dev/null || echo "")"
    [[ -z "$pr_num" ]] && continue
    if gh pr checks "$pr_num" --repo "$REPO_SLUG" --json bucket --jq '.[].bucket' 2>/dev/null | grep -q '^pending$'; then
      pending=$((pending+1))
    fi
  done
  [[ "$pending" -eq 0 ]] && { ok "All CI runs have settled."; break; }
  if [[ "$(date +%s)" -ge "$deadline" ]]; then warn "CI wait timed out with $pending PR(s) still running."; break; fi
  log "  $pending PR(s) still have CI running; checking again in 2 min."
  sleep 120
done

summarize | tee -a "$RUNNER_LOG"
