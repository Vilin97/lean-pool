/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingLinearity

/-!
# The potential measure of the supremum resolvent

Additivity and continuity along monotone limits make the supremum resolvent countably additive
on measurable observables (`minimalResolvent_tsum`), so at a positive shift it is the integral
against a finite measure on the state space, the potential measure `minimalPotential`
(`lintegral_minimalPotential`, `isFiniteMeasure_minimalPotential`).

This is the form in which the supremum resolvent is compared with the kernel resolvent of a
transition semigroup: an identity tested on continuous observables vanishing at infinity extends
to all nonnegative measurable observables through the two potential measures.

Monotonicity of the transported resolvents in the index is a bare hypothesis throughout.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

/-- **The supremum resolvent is countably additive** on measurable observables: finite additivity
and continuity along monotone limits give the sum of a series. -/
theorem minimalResolvent_tsum (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {u : ℕ → alpha → ℝ≥0∞} (hu : ∀ i, Measurable (u i))
    (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ ∑' i, u i y) x =
      ∑' i, minimalResolvent R emb lam (u i) x := by
  have hpartial : ∀ N, Measurable fun y ↦ ∑ i ∈ Finset.range N, u i y := fun N ↦
    Finset.measurable_sum _ fun i _ ↦ hu i
  have hpartialMono : Monotone fun N ↦ fun y ↦ ∑ i ∈ Finset.range N, u i y := by
    intro a b hab y
    have hsub : Finset.range a ⊆ Finset.range b := Finset.range_subset_range.2 hab
    exact Finset.sum_le_sum_of_subset hsub
  have hfinite : ∀ N, minimalResolvent R emb lam (fun y ↦ ∑ i ∈ Finset.range N, u i y) x =
      ∑ i ∈ Finset.range N, minimalResolvent R emb lam (u i) x := by
    intro N
    induction N with
    | zero => simpa using minimalResolvent_zero R emb hemb hlam x
    | succ N ih =>
        have hsplit : (fun y ↦ ∑ i ∈ Finset.range (N + 1), u i y) =
            fun y ↦ (∑ i ∈ Finset.range N, u i y) + u N y := by
          funext y
          rw [Finset.sum_range_succ]
        rw [hsplit, minimalResolvent_add R emb hemb hmono hlam (hpartial N) (hu N) x, ih,
          Finset.sum_range_succ]
  have hseries : (fun y ↦ ∑' i, u i y) = fun y ↦ ⨆ N, ∑ i ∈ Finset.range N, u i y := by
    funext y
    exact ENNReal.tsum_eq_iSup_nat
  rw [hseries, minimalResolvent_iSup R emb hemb lam hpartial hpartialMono x,
    ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr hfinite

omit [MeasurableSpace alpha] in
/-- The indicator of a countable disjoint union is the sum of the indicators. -/
private theorem tsum_indicator_one {S : ℕ → Set alpha}
    (hdisj : Pairwise (Function.onFun Disjoint S)) (y : alpha) :
    (⋃ i, S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y =
      ∑' i, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
  by_cases hy : y ∈ ⋃ i, S i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    have hzero : ∀ i, i ≠ j → (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y = 0 := by
      intro i hij
      exact Set.indicator_of_notMem
        (fun hmem ↦ Set.disjoint_left.mp (hdisj hij) hmem hj) _
    rw [Set.indicator_of_mem hy, tsum_eq_single j hzero, Set.indicator_of_mem hj]
  · have hzero : ∀ i, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y = 0 := fun i ↦
      Set.indicator_of_notMem (fun hmem ↦ hy (Set.mem_iUnion.mpr ⟨i, hmem⟩)) _
    rw [Set.indicator_of_notMem hy]
    simp only [hzero, tsum_zero]

/-- **The potential measure of the supremum resolvent** at a positive shift: the measure whose
value on a measurable set is the supremum resolvent of its indicator. -/
def minimalPotential (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) : Measure alpha :=
  Measure.ofMeasurable
    (fun S _ ↦ minimalResolvent R emb lam (S.indicator fun _ ↦ 1) x)
    (by simpa using minimalResolvent_zero R emb hemb hlam x)
    (fun {S} hS hdisj ↦ by
      have hindicator : (⋃ i, S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) =
          fun y ↦ ∑' i, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
        funext y
        exact tsum_indicator_one hdisj y
      rw [hindicator,
        minimalResolvent_tsum R emb hemb hmono hlam
          (fun i ↦ measurable_const.indicator (hS i)) x])

/-- The potential measure of a measurable set is the supremum resolvent of its indicator. -/
theorem minimalPotential_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) {S : Set alpha} (hS : MeasurableSet S) :
    minimalPotential R emb hemb hmono hlam x S =
      minimalResolvent R emb lam (S.indicator fun _ ↦ 1) x :=
  Measure.ofMeasurable_apply S hS

/-- **The supremum resolvent is integration against its potential measure**, on every
nonnegative measurable observable. -/
theorem lintegral_minimalPotential (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂minimalPotential R emb hemb hmono hlam x = minimalResolvent R emb lam f x := by
  refine Measurable.ennreal_induction
    (motive := fun g ↦ ∫⁻ y, g y ∂minimalPotential R emb hemb hmono hlam x =
      minimalResolvent R emb lam g x) ?_ ?_ ?_ hf
  · intro c S hS
    have hconst : (S.indicator fun _ ↦ c) = fun y ↦ c * (S.indicator fun _ ↦ (1 : ℝ≥0∞)) y := by
      funext y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    rw [lintegral_indicator_const hS, minimalPotential_apply R emb hemb hmono hlam x hS,
      hconst, minimalResolvent_const_mul R emb hemb lam c
        (measurable_const.indicator hS) x]
  · intro g h _hdisj hg hh ihg ihh
    have hlhs : ∫⁻ y, (g + h) y ∂minimalPotential R emb hemb hmono hlam x =
        ∫⁻ y, g y ∂minimalPotential R emb hemb hmono hlam x +
          ∫⁻ y, h y ∂minimalPotential R emb hemb hmono hlam x := by
      simp only [Pi.add_apply]
      exact lintegral_add_left hg _
    rw [hlhs, ihg, ihh]
    exact (minimalResolvent_add R emb hemb hmono hlam hg hh x).symm
  · intro g hg hgmono ih
    rw [lintegral_iSup hg hgmono, minimalResolvent_iSup R emb hemb lam hg hgmono x]
    exact iSup_congr ih

/-- The potential measure is finite at a positive shift, with mass at most `1 / lam`. -/
theorem isFiniteMeasure_minimalPotential (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsFiniteMeasure (minimalPotential R emb hemb hmono hlam x) := by
  refine ⟨?_⟩
  rw [minimalPotential_apply R emb hemb hmono hlam x MeasurableSet.univ, Set.indicator_univ]
  exact lt_of_le_of_lt
    (minimalResolvent_one_le R emb (fun m ↦ (hemb m).injective) hlam x) ENNReal.ofReal_lt_top

end MarkovProcess

end

end PortComputability
