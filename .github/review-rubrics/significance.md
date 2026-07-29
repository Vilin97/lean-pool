# Rubric: significance — is this worth having?

You are reviewing **one dimension** of this PR: whether the mathematics (or computer science, physics, game theory — a quarter of the pool is not pure mathematics, judged by its own field's standards) is worth pooling. Faithfulness, novelty, sources, and code quality are judged by separate reviews — do not spend words on them.

## What we want

- **Completed, self-contained projects.** A clear main theorem or set of theorems, proven within the PR.
- **Significance.** A result a working mathematician (or theoretical computer scientist) would name. Graduate or research level.
- **Theory building.** We prefer formalizations that develop a piece of mathematics over ad-hoc problem-solving on isolated obscure problems. Famous, named open problems with their own published statement *are* fine.

## What we don't want

- Single utility lemmas of any size, no matter how technical the proof. ("PMF.binomial_add_binomial" with a 160-line proof is still one utility lemma.)
- Random API generalizations or refactors with no headline result — what's the *theorem*?
- Pure problem-solving on obscure problems with no recognized program behind them.
- Undergraduate-textbook exercises (basic real analysis identities, group-axiom-style lemmas, intro probability calculations).
- **Bulk that someone else has to maintain.** Where most of the added lines are machine-emitted — proof certificates, extracted terms, generated case tables — say what fraction they are, whether the repository can regenerate them, and what they are built on. Generated bulk riding an internal or unstable Mathlib API turns every version bump into a regeneration liability, and that cost lands on the pool.

## Calibration

The median pooled project is ~2,800 lines of Lean, the tenth percentile ~900, and only four of 138 are under 500. Small is not disqualifying — but a small project has to carry its weight on significance.

**Worth having:** `clawristotle` (Vlasov-Maxwell-Landau steady-state classification, ~10K LOC, paper-anchored); `formal-learning-theory` (~19K LOC, several named theorems); `hadwiger-nelson-bounds` (kernel-checked 5 ≤ χ(ℝ²) ≤ 7 — a named open problem honestly bounded); `erdos132-n14` (~2K LOC conditional case of Erdős 132, conditionality disclosed); `sensitivity`, `circuit-complexity`, `pumping-cfg` (theoretical CS at the same bar).

**Not worth having:** two trivial binomial-PMF corollaries; an additive-convolution API generalization with no headline; a 176-line single-lemma PR proving an undergrad probability identity, however gnarly the proof.

## When there is no project to judge

A mixed PR can arrive with no new project in it — a Mathlib bump repairing every library, a CI change touching a pooled file, a project removal. Do not force it through this rubric: set `fit` to `not_applicable`, say in one sentence what the PR does, and `pass` unless something in the pooled Lean it touches is objectionable on this dimension.

## Verdict

- `pass` — graduate-or-research-level content a mathematician would name, or `not_applicable`.
- `block` — undergraduate exercise, utility lemma, no headline result, or unmaintainable generated bulk.
- `discuss` — genuinely borderline: real but modest content, or generated bulk whose maintenance price a human should weigh.

## Output

Return a single JSON object:

```json
{
  "verdict": "pass" | "block" | "discuss",
  "bottom_line": "<one sentence for the maintainer>",
  "fit": "good_fit" | "borderline" | "not_a_fit" | "not_applicable",
  "level": "undergraduate" | "graduate" | "research",
  "branch": "<one short phrase: e.g. 'analytic number theory', 'circuit complexity', 'PDE'>",
  "mode": "theory_building" | "problem_solving" | "mixed",
  "significance_one_sentence": "<what would a mathematician say the contribution is, or why it isn't one>",
  "findings": [
    {
      "file": "<repo-relative path, or empty if PR-wide>",
      "line": <int, post-change line; 0 if not file-specific>,
      "rule": "<e.g. 'no-headline-result', 'textbook-exercise', 'generated-bulk'>",
      "comment": "<what's wrong, where, concrete suggestion>",
      "evidence": "<what in the diff the finding rests on>"
    }
  ]
}
```
