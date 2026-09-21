/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardOverlapPrefix

/-!
# Deleting inactive intervals from the actual bad-input operator

Activity refers to the literal restricted bad-scale input. Every inactive
localized integral vanishes pointwise. Hence deletion preserves arbitrary
fixed weighted sums, including physical-scale truncations and generation
prefixes whose original ordering is retained. Regenerating the filtered
family need not preserve the original numerical generation labels.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

/-- The members of `N` whose interval bad input is nonzero somewhere. -/
noncomputable def activeBadIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) : Finset RealInterval :=
  N.filter fun I ↦ ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0

theorem activeBadIntervals_subset
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) :
    activeBadIntervals S f I₀ k₀ s scale N ⊆ N := Finset.filter_subset _ _

theorem localizedBadPiece_eq_zero_of_inactive
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval)
    (hinactive : ¬ ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x = 0 := by
  have hz (t : ℝ) : intervalBadInput S f I₀ k₀ s scale I t = 0 :=
    not_ne_iff.mp fun ht ↦ hinactive ⟨t, ht⟩
  unfold krauseLaceyLocalizedPiece
  have hzero (y : ℝ) : I.centralThird.indicator
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) (x - y) = 0 := hz (x - y)
  simp only [hzero, mul_zero, integral_zero]

/-- Deletion preserves every fixed coefficient choice, not merely the
unweighted sum. -/
theorem sum_weighted_localizedBadPiece_eq_active
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (c : RealInterval → ℂ) (x : ℝ) :
    (∑ I ∈ N, c I * krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x) =
    ∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N,
      c I * krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
  symm
  apply Finset.sum_subset (activeBadIntervals_subset S f I₀ k₀ s scale N)
  intro I hI hn
  have hi : ¬ ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0 :=
    fun h ↦ hn (Finset.mem_filter.mpr ⟨hI, h⟩)
  rw [localizedBadPiece_eq_zero_of_inactive S f I₀ k₀ s scale I hi x, mul_zero]

/-- In particular, every physical length-threshold sum is unchanged. -/
theorem sum_lengthTail_localizedBadPiece_eq_active
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (ell : ℤ) (x : ℝ) :
    (∑ I ∈ N, if (2 : ℝ) ^ ell ≤ I.length then
      krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0) =
    ∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N,
      if (2 : ℝ) ^ ell ≤ I.length then krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0 := by
  simpa only [ite_mul, one_mul, zero_mul] using
    sum_weighted_localizedBadPiece_eq_active S f I₀ k₀ s scale N
      (fun I ↦ if (2 : ℝ) ^ ell ≤ I.length then 1 else 0) x

/-- Original generation-prefix sums are preserved when only inactive
terms are deleted; this does not identify newly recomputed layer labels. -/
theorem sum_generationPrefix_localizedBadPiece_eq_active
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) (x : ℝ) :
    (∑ I ∈ N, if generationIndex N I < n then
      krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0) =
    ∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N,
      if generationIndex N I < n then krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0 := by
  simpa only [ite_mul, one_mul, zero_mul] using
    sum_weighted_localizedBadPiece_eq_active S f I₀ k₀ s scale N
      (fun I ↦ if generationIndex N I < n then 1 else 0) x

/-- An active good interval meets a genuine selected bad cell, which
must lie inside it by laminarity and the definition of the good family. -/
theorem exists_badScaleCell_subset_of_active
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I : RealInterval} (hI : I ∈ goodCollection S f 0 I₀)
    (hactive : ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0) :
    ∃ J ∈ badScaleCells S f I₀ k₀ (scale I + 2 - s), J.carrier ⊆ I.carrier := by
  obtain ⟨x, hx⟩ := hactive
  have hi := Set.indicator_apply_ne_zero.mp hx
  obtain ⟨J, hJ, hxJ⟩ := exists_mem_badScaleCells_of_ne_zero hi.2
  have hchild := badScaleCells_subset S f I₀ k₀ _ hJ
  have hgood := Finset.mem_filter.mp hI
  have hnot : ¬I.carrier ⊆ J.carrier := fun h ↦ hgood.2 ⟨J, hchild, h⟩
  have hne : I ≠ J := by intro h; exact hnot (h ▸ Subset.rfl)
  refine ⟨J, hJ, ?_⟩
  rcases hlam hgood.1 (stoppingChildren_subset S f 0 I₀ hchild) hne with h | h | hd
  · exact (hnot h).elim
  · exact h
  · exact (Set.disjoint_left.mp hd (I.centralThird_subset_carrier hi.1) hxJ).elim

/-- Above the grouped base scale, activity charges the full parent
length to a literal contained stopping cell with the exact `2^s` ratio. -/
theorem exists_chargedCell_of_active_above_base
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale)
    (hbase : k₀ < scale I + 2 - s)
    (hactive : ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0) :
    ∃ J ∈ stoppingChildren S f 0 I₀,
      J.carrier ⊆ I.carrier ∧ I.length = (2 : ℝ) ^ s * J.length := by
  obtain ⟨J, hJ, hJI⟩ := exists_badScaleCell_subset_of_active f I₀ k₀ s scale hlam
    (Finset.mem_filter.mp hI).1 hactive
  have hmax := (Finset.mem_filter.mp hJ).2
  have hlt : (2 : ℝ) ^ k₀ < (2 : ℝ) ^ (scale I + 2 - s) :=
    (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)) hbase
  have hlenJ : J.length = (2 : ℝ) ^ (scale I + 2 - s) := by
    rcases max_cases ((2 : ℝ) ^ k₀) J.length with h | h
    · exact (ne_of_lt hlt (h.1.symm.trans hmax)).elim
    · exact h.1.symm.trans hmax
  refine ⟨J, badScaleCells_subset S f I₀ k₀ _ hJ, hJI, ?_⟩
  rw [(Finset.mem_filter.mp hI).2.1, hlenJ, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring


end KrauseLaceyBadScale
end QuadraticCarleson
