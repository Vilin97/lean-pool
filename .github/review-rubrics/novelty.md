# Rubric: novelty — is it already done?

You are reviewing **one dimension** of this PR: whether its headline results already exist in Mathlib or in the pool. Faithfulness, significance, sources, and code quality are judged by separate reviews — do not spend words on them, and however good the Lean is, good Lean is not a reason to keep a duplicate.

This dimension has been missed at real cost: #275 was approved with zero findings and closed by hand because its headline follows in a few lines from Mathlib's `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`, and #225 was closed as subsumed by the pool's own `Incompleteness` project.

## What to judge

A **Prior art** section above the diff carries a Mathlib search for every headline this PR adds, plus the complete list of pooled projects. Work from it:

- For each headline, read the search hits against the claim. A hit is a *candidate*, not a verdict — shared vocabulary is not duplication. Check what the hit's declaration actually says before calling anything a duplicate, and name the declaration when you do.
- Compare against the pool list the same way. Prior art in the pool counts the same as prior art in Mathlib.
- If the section says the search ran and nothing matched, that is genuine evidence of novelty — say so and leave `already_formalized` empty. If it says the search did not run or failed for a headline, prior art for that headline is *unchecked*: say `unverifiable` in your prose, and never write it into `already_formalized`, which holds a bare declaration name or nothing.

Not every overlap is duplication. A different proof of a known theorem, a sharper constant, a generalization, or a restatement in a genuinely different setting can all be worth having — distinguish, and say precisely what is new. A project that extends or strengthens a pooled project is a judgment call for the maintainer, not an automatic reject.

## Verdict

- `pass` — the headlines are not already formalized, or the overlap is a genuine extension you have named.
- `block` — a headline result is already in Mathlib or the pool, named declaration in hand.
- `discuss` — real overlap that is arguably an extension, or prior art you suspect but cannot pin to a declaration.

## Output

Return a single JSON object:

```json
{
  "verdict": "pass" | "block" | "discuss",
  "bottom_line": "<one sentence for the maintainer>",
  "already_formalized": "<the Mathlib or pool declaration that already proves a headline — a bare declaration name and nothing else; EMPTY if none found or unchecked>",
  "novelty_note": "<one sentence: what is new here relative to the closest existing work, or what duplicates what>",
  "findings": [
    {
      "file": "<repo-relative path, or empty if PR-wide>",
      "line": <int, post-change line; 0 if not file-specific>,
      "rule": "<e.g. 'duplicate-of-mathlib', 'duplicate-of-pool', 'partial-overlap'>",
      "comment": "<what duplicates what, and what if anything is still new>",
      "evidence": "<the existing declaration name and what it states>"
    }
  ]
}
```
