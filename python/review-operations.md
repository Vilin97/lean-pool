# Pull request reviews

A privately operated worker checks open PRs and new `/review` comments every ten
minutes. Anyone can request a review on any open PR. Multiple requests awaiting
the same review are combined. New content PR heads are reviewed automatically
after Lean Action CI succeeds. Explicit requests can review infrastructure PRs
and report failing or missing CI without assuming the code has passed.

Reviews use GPT-6-Astra with `xhigh` reasoning and Codex subscription quota.
The reviewer can inspect the exact PR source, run terminal commands, use Lake,
and execute code in its review workspace. The worker publishes the existing
sticky review comment, including the reviewed commit, findings, rubric verdicts,
tokens, and nominal API-equivalent cost. The estimate is not a charge.

Execution logs, account selection, credentials, queue state, and deployment
configuration are private. No review transcripts are uploaded to public Actions
artifacts. A new commit supersedes unfinished reviews of an older head; a result
for an obsolete head is never posted as a current review.

When subscription capacity is unavailable, requests wait for a later poll.
There is no fallback to paid OpenAI or Azure API requests. Deployment and
operator instructions are maintained separately from this public repository.
