# Azure Codex reviews

The LLM review workflow uses `gpt-6-astra` at `xhigh` reasoning effort through
the authenticated Codex account pool on the `lean` Azure VM. It consumes that
pool's Codex quota, with no OpenAI API key and no fallback to paid API requests.
The existing review rubrics, CI prerequisite, verdict aggregation, and sticky
comments still apply. Comments identify the model, token counts, and quota billing.

GitHub Actions continues to fetch the PR and post the comment. Only the review
instructions and contributor text cross SSH. The workflow checks out its trusted
base code and never executes PR-head code on the VM. The worker runs Codex with
ChatGPT authentication required, user configuration ignored, a read-only sandbox,
and shell, apps, plugins, browser, image, and agent tools disabled. Each request
uses a temporary directory on `/data`, removed when it finishes. The VM's existing
account dispatcher handles account selection and quota waits.

Each model call has a 272,000-estimated-token input ceiling, including the
review instructions, PR description, shared evidence, and prior-art results.
Oversized diffs are partitioned losslessly, preferring complete files and Lean
command boundaries. Oversized individual commands continue in numbered source
ranges. Every diff character is covered, with a SHA-256 digest and range manifest.
No file body is discarded to meet the budget. Missing or truncated GitHub text
patches are reconstructed from hash-verified Git blobs; source acquisition fails
if those blobs cannot be retrieved. GitHub line statistics can be zero for an
omitted nonempty patch, so they are never treated as proof that a file is empty.

For each rubric, up to three source portions are reviewed concurrently. Their
complete structured evidence and open questions feed a final integration review.
That review checks the headline contracts and dependencies across modules. It
can request exact declaration or file excerpts from the original diff, with up
to three source follow-ups when summaries leave a semantic question unanswered. It
must explicitly resolve every non-passing portion, finding, and open question
before it can pass; unresolved obligations force discussion. Missing/malformed
portion results or integration evidence that cannot fit fail the run rather than
silently reducing coverage. Small diffs still use one call per rubric.

A context-window rejection retries using smaller lossless portions. The token
estimate is conservative, not an exact tokenizer measurement; the ceiling does
not change the model's actual context window. Reported usage includes all source
and integration calls, including successful work before a retry; unknown usage
is disclosed. The workflow uploads the complete structured evidence and coverage
manifest as the `review-evidence` artifact. The existing blocking/advisory rubric rules remain intact.
Each worker call has a 100-minute timeout, including quota waits; a timeout kills
its dispatcher process group and fails the review.

## Deployment

The standalone worker is `lean_pool/codex_review.py`, installed as
`/data/lean-pool-review/worker.py` on `lean`. It uses only the Python standard
library and invokes `/home/vasil/.local/bin/codex-auto`. The worker file is owned
by root; `/data/lean-pool-review/jobs` is private to `vasil` for temporary requests.
To update it from the repository root:

```bash
ssh lean 'sudo tee /data/lean-pool-review/worker.py >/dev/null' \
  < python/lean_pool/codex_review.py
```

The dedicated public key in `vasil`'s `authorized_keys` has these options:

```text
restrict,command="/usr/bin/python3 /data/lean-pool-review/worker.py --worker"
```

It cannot open a shell, forward ports, or select another command. Model and
effort values are validated, and contributor text is passed through stdin.

Repository secrets:

- `REVIEW_AZURE_SSH_KEY`: the dedicated private SSH key, used only by this workflow.
- `REVIEW_AZURE_KNOWN_HOSTS`: the VM's pinned Ed25519 host key, obtained through
  an already trusted connection. Never replace this with an unverified keyscan.

Codex credentials stay on the VM. Do not copy or print its `auth.json` files.
Use `cx status` and `cx doctor` on the VM to diagnose authentication, quota,
and disk issues. Rotate the dedicated SSH key by adding a new restricted public
key, updating the repository secret, verifying a review, then removing the old
dedicated key. Do not remove other operator keys.

## Local use and failures

Configure an SSH alias using the restricted key and pinned host key, then run:

```bash
cd python
REVIEW_SSH_HOST=lean-pool-review-azure PR_NUMBER=123 \
  uv run --group review python -m lean_pool.review
```

`REVIEW_SSH_CONFIG` optionally selects a separate SSH configuration file.
`REVIEW_BACKEND` defaults to `codex-azure`. Connection, authentication, timeout,
and malformed-output errors fail the job, without contacting the paid API.
After fixing the VM or its credentials, rerun the workflow or request `/review`.

The legacy API backend remains available only when explicitly selected with
`REVIEW_BACKEND=openai`, `REVIEW_MODEL`, and `OPENAI_API_KEY`. The production
workflow neither selects it nor supplies that key.
