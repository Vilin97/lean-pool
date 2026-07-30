"""Contract tests for challenge verification and its PR comment companion."""

import re
from pathlib import Path

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
VERIFIER_PATH = REPOSITORY_ROOT / ".github/workflows/challenge-verify.yml"
COMMENTER_PATH = REPOSITORY_ROOT / ".github/workflows/challenge-verify-comment.yml"


def test_verifier_remains_read_only_and_uploads_results_after_failure() -> None:
    """Untrusted PR code emits a report but never receives a writable token."""
    workflow = VERIFIER_PATH.read_text()

    assert "permissions:\n  contents: read\n" in workflow
    assert "pull-requests: write" not in workflow
    assert "name: challenge-comparator-report" in workflow
    assert "if: always() && github.event_name == 'pull_request'" in workflow
    assert "pr-number.txt" in workflow
    assert "head-sha.txt" in workflow
    assert "base-sha.txt" in workflow
    assert "merge-sha.txt" in workflow
    assert "merge-tree.txt" in workflow
    assert "results.json" in workflow
    assert "pull_request:\n    types:" in workflow
    assert "pull_request:\n    paths:" not in workflow
    assert "challenge-comparator-report-${{ github.run_attempt }}" in workflow


def test_verifier_records_every_result_instead_of_stopping_at_first_failure() -> None:
    """A multi-claim PR receives an explicit result for every comparator run."""
    workflow = VERIFIER_PATH.read_text()

    assert "while IFS= read -r slug; do" in workflow
    assert 'result_status="failed"' in workflow
    assert "lean_pool.challenge_report record" in workflow
    assert "git diff --no-renames --name-only" in workflow
    assert 'exit "$overall_status"' in workflow


def test_verifier_does_not_trust_pr_scoped_executable_caches() -> None:
    """A force-pushed PR cannot reuse binaries or oleans poisoned by an old head."""
    workflow = VERIFIER_PATH.read_text()

    assert "enable-cache: ${{ github.event_name != 'pull_request' }}" in workflow
    assert workflow.count("if: github.event_name != 'pull_request'") >= 2
    assert "cache: false" in workflow


def test_commenter_uses_a_trusted_workflow_run_context() -> None:
    """The writable job runs only trusted default-branch rendering code."""
    workflow = COMMENTER_PATH.read_text()

    assert 'workflows: ["Verify challenge solutions"]' in workflow
    assert "actions: read" in workflow
    assert "pull-requests: write" in workflow
    assert "ref: ${{ github.event.repository.default_branch }}" in workflow
    assert "persist-credentials: false" in workflow
    assert "challenge-comparator-comment -->" in workflow
    assert 'issues/comments/$existing" --input -' in workflow
    assert 'gh pr comment "$PR_NUMBER"' in workflow
    assert "The comparator report could not be validated" in workflow
    assert "This PR no longer claims a challenge solution" in workflow
    assert "lean_pool.challenge_report extract" in workflow
    assert "unzip " not in workflow
    assert "workflow_dispatch:" not in workflow
    assert "pull_request_target:\n    types:" in workflow
    assert "pull_request_target:\n    paths:" not in workflow
    assert "conclusion != 'cancelled'" not in workflow
    assert re.search(r"--slurp\s+--jq", workflow) is None


def test_commenter_handles_fork_runs_and_validates_artifact_identity() -> None:
    """Fork PRs work even when workflow_run.pull_requests is empty."""
    workflow = COMMENTER_PATH.read_text()

    assert "HEAD_OWNER:" in workflow
    assert "HEAD_BRANCH:" in workflow
    assert "RUN_HEAD_SHA:" in workflow
    assert '-f "head=$HEAD_OWNER:$HEAD_BRANCH"' in workflow
    assert "--paginate --slurp" in workflow
    assert '[ "$reported_head" = "$RUN_HEAD_SHA" ]' in workflow
    assert '"$reported_pr" != "$candidate_pr"' in workflow
    assert '"$current_head" != "$RUN_HEAD_SHA"' in workflow
    assert '"$returned_file_count" -ne "$expected_file_count"' in workflow
    assert "verifier_trusted=false" in workflow
    assert '--verifier-trusted "$VERIFIER_TRUSTED"' in workflow


def test_commenter_authenticates_the_merge_and_base_verifier() -> None:
    """The final verdict matches the merge tree judged by trusted producer code."""
    workflow = COMMENTER_PATH.read_text()

    assert '"refs/pull/$candidate_pr/head"' in workflow
    assert "git merge-tree --write-tree" in workflow
    assert '"$live_parents" != "$current_base $current_head"' in workflow
    assert '"$reported_tree" != "$merge_tree"' in workflow
    assert 'git show "$MERGE_TREE:Challenge/challenges.yml"' in workflow
    assert '--head-registry "$MERGE_REGISTRY"' in workflow
    assert 'git diff --quiet "$current_base" HEAD --' in workflow
    assert ".github/workflows/challenge-verify.yml" in workflow
    assert "scripts/challenge python" in workflow


def test_pending_and_final_writers_share_identity_and_recheck_head() -> None:
    """A delayed placeholder cannot overwrite a verdict for a newer PR state."""
    workflow = COMMENTER_PATH.read_text()

    assert (
        "group: challenge-comparator-write-${{ github.event.pull_request.number }}"
        in workflow
    )
    assert (
        "group: challenge-comparator-write-${{ needs.resolve.outputs.number }}"
        in workflow
    )
    assert workflow.count("cancel-in-progress: false") == 2
    assert "needs: resolve" in workflow
    assert "phase=pending" in workflow
    assert "phase=final" in workflow
    assert (
        "challenge-comparator-order workflow=$WORKFLOW_ID "
        "run=$RUN_NUMBER attempt=$RUN_ATTEMPT"
    ) in workflow
    assert '"$existing_attempt" -ge "$RUN_ATTEMPT"' in workflow
    assert '"$current_attempt" != "$RUN_ATTEMPT"' in workflow
    assert "A final verdict already covers this exact PR merge" in workflow
    assert workflow.count('"$current_head" != "$HEAD_SHA"') >= 2
    assert workflow.count('"$current_base" != "$BASE_SHA"') >= 2


def test_commenter_selects_only_the_current_rerun_artifact() -> None:
    """A failed attempt cannot collide with or overwrite a successful rerun."""
    workflow = COMMENTER_PATH.read_text()

    assert (
        workflow.count('artifact_name="challenge-comparator-report-$RUN_ATTEMPT"') == 2
    )
    assert (
        workflow.count("RUN_ATTEMPT: ${{ github.event.workflow_run.run_attempt }}") >= 2
    )
    assert "RUN_NUMBER: ${{ github.event.workflow_run.run_number }}" in workflow
    assert "/attempts/${{ github.event.workflow_run.run_attempt }}" in workflow
