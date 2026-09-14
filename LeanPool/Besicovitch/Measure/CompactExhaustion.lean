/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Compact cores of measurable exhaustions

An increasing measurable exhaustion which covers a finite-measure set almost everywhere contains
a compact core with arbitrarily small discarded mass.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LeanPool.Besicovitch

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [T2Space X]

/-- An almost-everywhere increasing measurable exhaustion contains a compact core losing less than
any prescribed positive mass. -/
theorem exists_compact_in_monotone_ae_cover_measure_sdiff_lt {mu : Measure X}
    [Measure.InnerRegularCompactLTTop mu] {A : Set X} (hA : MeasurableSet A)
    (hA_finite : mu A ≠ ∞) {G : ℕ → Set X} (hG_measurable : ∀ n, MeasurableSet (G n))
    (hG_subset : ∀ n, G n ⊆ A) (hG_mono : Monotone G)
    (hcovered : ∀ᵐ x ∂mu.restrict A, x ∈ ⋃ n, G n)
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ (n : ℕ) (F : Set X), IsCompact F ∧ F ⊆ G n ∧ mu (A \ F) < epsilon := by
  have hnull : mu (⋂ n, A \ G n) = 0 := by
    have hnull_restrict : (mu.restrict A) (⋂ n, A \ G n) = 0 := by
      rw [← ae_eq_empty]
      refine eventuallyEq_set.2 ?_
      filter_upwards [hcovered] with x hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      constructor
      · intro hx_inter
        have hxn : x ∈ A \ G n := mem_iInter.1 hx_inter n
        exact (hxn.2 hn).elim
      · simp
    rw [Measure.restrict_apply' hA] at hnull_restrict
    have hinter_subset : (⋂ n, A \ G n) ⊆ A := by
      intro x hx
      have hx0 : x ∈ A \ G 0 := mem_iInter.1 hx 0
      exact hx0.1
    simpa only [inter_eq_self_of_subset_left hinter_subset] using hnull_restrict
  have hanti : Antitone fun n ↦ A \ G n := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hxG ↦ hx.2 (hG_mono hmn hxG)⟩
  have hmeasurable (n : ℕ) : NullMeasurableSet (A \ G n) mu :=
    (hA.diff (hG_measurable n)).nullMeasurableSet
  have hfinite : ∃ n : ℕ, mu (A \ G n) ≠ ∞ :=
    ⟨0, ne_top_of_le_ne_top hA_finite (measure_mono sdiff_subset)⟩
  have hinf : (⨅ n, mu (A \ G n)) = 0 := by
    rw [← hanti.measure_iInter hmeasurable hfinite, hnull]
  have hexceptional (epsilon : ℝ≥0∞) (hepsilon : 0 < epsilon) :
      ∃ n, mu (A \ G n) < epsilon := by
    by_contra h
    push Not at h
    have : epsilon ≤ (⨅ n, mu (A \ G n)) := le_iInf h
    rw [hinf] at this
    exact (not_le_of_gt hepsilon) this
  have hhalf : 0 < epsilon / 2 := ENNReal.div_pos hepsilon.ne' (by norm_num)
  obtain ⟨m, hm⟩ := hexceptional (epsilon / 2) hhalf
  have hG_finite : mu (G m) ≠ ∞ :=
    ne_top_of_le_ne_top hA_finite (measure_mono (hG_subset m))
  obtain ⟨F, hFG, hF_compact, hGF⟩ :=
    (hG_measurable m).exists_isCompact_sdiff_lt hG_finite hhalf.ne'
  refine ⟨m, F, hF_compact, hFG, ?_⟩
  have hsubset : A \ F ⊆ (A \ G m) ∪ (G m \ F) := by
    intro x hx
    by_cases hxG : x ∈ G m
    · exact Or.inr ⟨hxG, hx.2⟩
    · exact Or.inl ⟨hx.1, hxG⟩
  calc
    mu (A \ F) ≤ mu ((A \ G m) ∪ (G m \ F)) := measure_mono hsubset
    _ ≤ mu (A \ G m) + mu (G m \ F) := measure_union_le _ _
    _ < epsilon / 2 + epsilon / 2 := ENNReal.add_lt_add hm hGF
    _ = epsilon := ENNReal.add_halves epsilon

/-- The compact core can be chosen so that the discarded mass is a prescribed positive fraction
of the retained mass. -/
theorem exists_compact_in_monotone_ae_cover_measure_sdiff_lt_mul {mu : Measure X}
    [Measure.InnerRegularCompactLTTop mu] {A : Set X} (hA : MeasurableSet A)
    (hA_pos : 0 < mu A) (hA_finite : mu A ≠ ∞) {G : ℕ → Set X}
    (hG_measurable : ∀ n, MeasurableSet (G n)) (hG_subset : ∀ n, G n ⊆ A)
    (hG_mono : Monotone G) (hcovered : ∀ᵐ x ∂mu.restrict A, x ∈ ⋃ n, G n)
    {coefficient : ℝ≥0∞} (hcoefficient_pos : 0 < coefficient)
    (hcoefficient_finite : coefficient ≠ ∞) :
    ∃ (n : ℕ) (F : Set X), IsCompact F ∧ F ⊆ G n ∧
      mu (A \ F) < coefficient * mu F := by
  let halfMass := mu A / 2
  let tolerance := min halfMass (coefficient * halfMass)
  have hhalf_pos : 0 < halfMass := ENNReal.div_pos hA_pos.ne' (by norm_num)
  have htolerance_pos : 0 < tolerance := by
    rw [lt_min_iff]
    exact ⟨hhalf_pos, ENNReal.mul_pos hcoefficient_pos.ne' hhalf_pos.ne'⟩
  obtain ⟨n, F, hF_compact, hFG, herror⟩ :=
    exists_compact_in_monotone_ae_cover_measure_sdiff_lt hA hA_finite hG_measurable
      hG_subset hG_mono hcovered htolerance_pos
  refine ⟨n, F, hF_compact, hFG, ?_⟩
  have hFA : F ⊆ A := hFG.trans (hG_subset n)
  have hF_measurable : MeasurableSet F := hF_compact.isClosed.measurableSet
  have herror_half : mu (A \ F) < halfMass := herror.trans_le (min_le_left _ _)
  have herror_scaled : mu (A \ F) < coefficient * halfMass :=
    herror.trans_le (min_le_right _ _)
  have hdecomposition : mu (A \ F) + mu F = mu A := by
    simpa only [inter_eq_right.mpr hFA] using
      measure_sdiff_add_inter (μ := mu) A hF_measurable
  have hhalf_lt : halfMass < mu F := by
    by_contra h
    have hF_le : mu F ≤ halfMass := le_of_not_gt h
    have hF_finite : mu F ≠ ∞ :=
      ne_top_of_le_ne_top hA_finite (measure_mono hFA)
    have hsum_lt : mu (A \ F) + mu F < halfMass + halfMass :=
      ENNReal.add_lt_add_of_lt_of_le hF_finite herror_half hF_le
    have : mu A < mu A := by
      calc
        mu A = mu (A \ F) + mu F := hdecomposition.symm
        _ < halfMass + halfMass := hsum_lt
        _ = mu A := ENNReal.add_halves (mu A)
    exact this.false
  exact herror_scaled.trans <|
    ENNReal.mul_lt_mul_right hcoefficient_pos.ne' hcoefficient_finite hhalf_lt

end LeanPool.Besicovitch
