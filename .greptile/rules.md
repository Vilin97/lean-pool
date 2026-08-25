# Lean Pool supervisory review

Apply this rubric to every pull request that adds or materially changes a pooled
formalization. It is the same review standard used by Lean Pool's daily project
acquisition automation. Your comparative advantage is repository-wide,
cross-file analysis: trace declarations and consumers, find existing
abstractions, and identify integration and maintainability defects that a
diff-only reviewer can miss.

Do not infer quality from social or workflow state. A pull request is not good
because it is merged, closed, approved, old, authored by a maintainer, or green
in CI. Historical pull requests must be judged as if they were new. Conversely,
do not report that kernel-checked Lean fails to prove its formal statement merely
because a proof is difficult to understand.

## Review the complete contribution

Read the complete diff, the project card, all added project modules, relevant
existing Lean Pool code, and any upstream source material available in the pull
request. Do not review only the headline file or the first defect found. When
the diff is elided or required evidence is unavailable, identify the unchecked
area and do not describe the pull request as safe to merge.

Evaluate all of the following axes:

1. **Significance and Lean Pool fit.** The contribution should be a substantial,
   completed formalization of graduate- or research-level mathematics or a
   related discipline, not a tutorial, exercise set, isolated utility lemma,
   tool, scaffold, or bulk with no meaningful headline.
2. **Headline faithfulness.** For every `main_results` entry, compare the exact
   Lean declaration type with its informal claim, quantifier by quantifier.
   Check domains, hypotheses, boundary cases, conditionality, finiteness,
   universes, and whether the conclusion is weaker than advertised. Look for
   vacuous hypotheses, surrogate objects, and hard content hidden in structure
   fields, class fields, inductive constructors, or unexercised predicates.
3. **Novelty.** Check for concrete prior art in Mathlib and Lean Pool. Shared
   vocabulary is not duplication: name the existing declaration and compare its
   type before filing a finding. A generalization, sharper result, or genuinely
   different setting may still be valuable.
4. **Source fidelity and attribution.** Check that cited sources, theorem names,
   hypotheses, authors, and claims are mutually consistent; that variants,
   special cases, and external assumptions are disclosed; and that identifiable
   earlier formalizations receive credit. Never claim to have verified an
   external source that was not available.
5. **Downstream value, abstraction, and generality.** Determine whether the new
   infrastructure is likely to be useful to other formalizations. Flag custom
   representations that duplicate an existing Mathlib or Lean Pool abstraction
   without a bridge, APIs specialized to one example without need, assumptions
   or typeclasses stronger than their consumers require, and public definitions
   with no nontrivial consumer or witness.
6. **Completion and partial-import risk.** Check that the meaningful upstream
   project is present, the headline does not depend on omitted material, all
   added modules are reachable from the project entry module, and exclusions are
   disclosed. A cherry-picked fragment must not be presented as the complete
   upstream result.
7. **License and provenance.** Check the concrete evidence available in the pull
   request for a compatible upstream license, pinned source revision, proof
   provenance, preserved authorship, and copied or adapted code attribution.
   Internal consistency is reviewable; unavailable external evidence must be
   reported as unverified rather than silently assumed.
8. **Maintainability and code quality.** Look for duplicated proof spines,
   parallel pipelines differing only by names, dead branches, unused theorem
   hypotheses, overstrong interfaces, near-duplicate definitions, irrelevant
   imports, generated bulk, monolithic proofs, unstable internal dependencies,
   and architecture likely to make future Mathlib bumps expensive. Group all
   instances of the same defect into one finding.
9. **Measured cost.** Use compile-time, heartbeat, profile, generated-line, and
   code-size evidence when it is available in the pull request. Distinguish
   import time from declaration elaboration time. Do not infer acceptable
   performance merely from a green build, and do not invent measurements when
   profile evidence is unavailable.

## Findings and verdict discipline

- Report only concrete, actionable findings with exact files, declarations, and
  evidence. Explain the risk to Lean Pool and the smallest suitable correction.
- A real mismatch in headline, source, license, provenance, completion, or hidden
  assumptions is blocking. Significant maintainability, generated-bulk,
  performance, dependency, or generality concerns require maintainer judgment.
- Do not soften one dimension because another is strong. Important mathematics
  can still be inaccurately described or unmaintainable.
- Do not call the pull request safe to merge unless every applicable dimension
  above has been checked at the current head. State exactly which dimensions are
  unverified.
- After a targeted repair, review the new head rather than carrying forward a
  stale approval or stale finding.

## Out of scope and noise control

Do not comment on checks already enforced deterministically unless the pull
request weakens or evades them: compilation, `sorry`/`admit`, declared axioms,
file headers, whitespace, naming style, line length, ASCII, `simp` preferences,
docstring presence, generated root-import ordering, or ordinary linter output.
Do not request a waiver, gate change, or linter suppression. Do not produce
encouragement, generic summaries, taste preferences, or findings without cited
evidence.
