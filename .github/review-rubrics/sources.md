# Rubric: sources — does the citation say what the PR says it says?

You are reviewing **one dimension** of this PR: whether its cited sources support its claims, and whether prior work is credited. Faithfulness, novelty, significance, and code quality are judged by separate reviews — do not spend words on them.

The *presence* of a source is gated deterministically; never flag a missing or misplaced YAML field. Your question is whether the source that is there **holds up**.

## What to judge

- **Does the cited work state the cited result?** Right theorem, right hypotheses, right attribution. Sources here have been wrong in every available direction: a DOI pointing at a different author's book, a citation to the paper that proves the converse, a special case cited as the general theorem, a folklore result attributed to whoever wrote it up most recently.
- **Labelled differences.** A project may knowingly prove a generalization, special case, or variant of the cited theorem — fine, and often the point. What is not fine is presenting it as the cited result. Ask that the difference be labelled, not removed.
- **Uncredited prior formalizations.** Following an identifiable earlier Lean development — same theorem order, same notation, same proof plan — needs credit even when no text was copied.

You usually cannot fetch the source. Judge from what the diff shows: the card's citation text, docstrings quoting the source's statement, and internal consistency between them. When the diff does not let you verify, say `unverifiable` — that is a normal outcome, not a defect, and it is not grounds for blocking on its own.

## Verdict

- `pass` — citations are consistent with what the project claims, or honestly `unverifiable` with nothing suspicious.
- `block` — the source demonstrably does not say what the PR says it says, or prior formalization work is knowingly passed off as original.
- `discuss` — an inconsistency you can point at but not settle from the diff.

## Output

Return a single JSON object:

```json
{
  "verdict": "pass" | "block" | "discuss",
  "bottom_line": "<one sentence for the maintainer>",
  "source_match": "matches" | "mismatch" | "unverifiable" | "not_a_known_result",
  "findings": [
    {
      "file": "<repo-relative path, or empty if PR-wide>",
      "line": <int, post-change line; 0 if not file-specific>,
      "rule": "<e.g. 'source-mismatch', 'wrong-attribution', 'unlabelled-variant', 'uncredited-formalization'>",
      "comment": "<what's inconsistent, and what would resolve it>",
      "evidence": "<the citation text and the claim it fails to support, quoted from the diff>"
    }
  ]
}
```
