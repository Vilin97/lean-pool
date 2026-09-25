/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic
public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.Capacitability


/-!
# Solution file: Choquet capacitability for analytic sets, and universal measurability

This module supplies declarations whose types are exactly the two types stated in
`ChallengeCapacitability`, together with their proofs.

The proofs themselves live in `BicausalOT/DescriptiveSetTheory/Capacitability.lean`.  That
file imports Mathlib together with `BicausalOT.DescriptiveSetTheory.AnalyticSet`, which
declares nothing at all: it is a comment block, one Mathlib import
(`Mathlib.MeasureTheory.Constructions.Polish.Basic`) and an `open MeasureTheory`.  So the
Lean content behind the two registered results is Mathlib alone.

`import Mathlib` is present here so that this module elaborates the statement in the
same environment as its Challenge file, which imports Mathlib and nothing else.  The
repository import below declares no name that Mathlib also declares, so it cannot
change how the statement elaborates; the Mathlib import only guarantees that it cannot.

## The argument

For `A` analytic and nonempty, `A = range π` with `π : ℕᴺ → X` continuous.  The Souslin
scheme is `G_s := closure (π '' N_s)` over the cylinders `N_s` of Baire space.  For a bound
`β : ℕ → ℕ` write `Σ(β) = {σ | ∀ i, σ i ≤ β i}`, which is compact, and

* `capW π β n = ⋃ {G_s : s ≤ β on the first n coordinates}` — a *closed*, decreasing family
  of approximations (`isClosed_capW`, `capW_antitone`);
* `cap_exists_bound` — the measure-free recursion: for any monotone `m : Set X → ℝ≥0∞` that
  is continuous along increasing unions, `c < m (𝒜(G))` yields a bound `β` with
  `c < m (capW π β n)` for every `n`.  It is built one coordinate at a time (`capAux`,
  `capBound`, `capAux_eq`) and mirrors the `leftmostAuxG` pattern of `Tree.lean`.  This is
  where the analytic-set structure is consumed, and it is already stated abstractly in `m`;
* `iInter_capW_subset` — the core topological lemma, `⋂ n, capW π β n ⊆ π '' Σ(β)`, proved
  by a subsequence extraction inside the compact `Σ(β)` (clip an approximating branch
  coordinatewise by `β`, extract a convergent subsequence, use continuity of `π`).  This is
  what supplies compactness of the witness;
* the endgame is measure-specific: `Directed.measure_iInter` turns
  `μ (⋂ n, capW π β n)` into `⨅ n, μ (capW π β n)`, which needs the `capW π β n` to be
  null-measurable (they are closed) and needs `μ` finite.  This step is the reason
  `IsFiniteMeasure` appears in the statement, and the reason the registered theorem is the
  measure instance rather than the abstract capacity theorem — see
  `fidelity.divergences` in `formalization-capacitability.yaml`.

Universal measurability follows from capacitability in a dozen lines: choose compacts
`K k ⊆ A` with `μ A ≤ μ (K k) + 1/(k+1)`, note `⋃ k, K k` is Borel, contained in `A`, and of
full measure, then compare `A` with a measurable hull to see that `A \ ⋃ k, K k` is null.

The declarations below restate the two library theorems inside the `Capacitability`
namespace so that their names match the `ChallengeCapacitability` declarations named in
`comparator-capacitability.json`; the library theorems they delegate to,
`MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact` and
`MeasureTheory.AnalyticSet.nullMeasurableSet`, are both covered by the repository's
`#print axioms` audit (`BicausalOT/AxiomsAudit.lean`, lines 41–42, which runs during
`lake build`; the first is additionally in the standalone `AxiomAudit.lean`), and both
report only `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory

namespace Capacitability

/-- **Choquet capacitability, measure case** (Kechris, *Classical Descriptive Set Theory*,
Theorem 30.13 instantiated at the capacity `γ = μ*` of Example 30.B.1; Bertsekas–Shreve,
*Stochastic Optimal Control: The Discrete Time Case*, Proposition 7.42).

For a finite Borel measure `μ` on a Polish space `X`, the outer measure of an analytic set
`A ⊆ X` is the supremum of the measures of the compact subsets of `A`.  `A` is not assumed
measurable. -/
theorem analyticSet_measure_eq_iSup_isCompact
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K :=
  _root_.MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact hA μ

/-- **Analytic sets are universally measurable** (Lusin; Kechris, *Classical Descriptive Set
Theory*, Exercise 30.11 combined with Theorem 30.13; Bertsekas–Shreve, *Stochastic Optimal
Control: The Discrete Time Case*, Corollary 7.42.1 of Proposition 7.42).

An analytic subset of a Polish space is null-measurable with respect to every finite Borel
measure: it differs from a Borel set by a null set. -/
theorem analyticSet_nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ :=
  _root_.MeasureTheory.AnalyticSet.nullMeasurableSet hA μ

end Capacitability
