/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Attainment of the largest eigenvalue of a compact positive operator

This Hilbert-space lemma will be applied to the compact energy realization's
Gram operator. It does not itself assert manifold eigenfunction regularity.
-/

@[expose] public noncomputable section
open Module Set

namespace LichnerowiczObata

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- A nonzero compact positive symmetric operator has a largest positive
eigenvalue. No finite-dimensionality of the Hilbert space is assumed. -/
theorem exists_largest_positive_eigenvalue
    (T : V →L[ℝ] V) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ v, 0 ≤ inner ℝ v (T v)) (hn : T ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Module.End.HasEigenvalue T.toLinearMap r ∧
      ∀ s : ℝ, Module.End.HasEigenvalue T.toLinearMap s → s ≤ r := by
  have hex : ∃ s : ℝ, Module.End.HasEigenvalue T.toLinearMap s ∧ s ≠ 0 := by
    by_contra h
    push Not at h
    exact hn ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hc hs).mp h)
  obtain ⟨s, hsEig, hs0⟩ := hex
  have hspos : 0 < s := lt_of_le_of_ne
    (eigenvalue_nonneg_of_nonneg hsEig hp) (Ne.symm hs0)
  have hsSpec : s ∈ spectrum ℝ T := (hc.hasEigenvalue_iff_mem_spectrum hs0).mp hsEig
  obtain ⟨r, hrSpec, hrmax⟩ := (spectrum.isCompact T).exists_isMaxOn
    ⟨s, hsSpec⟩ continuous_id.continuousOn
  have hrpos : 0 < r := hspos.trans_le (hrmax hsSpec)
  refine ⟨r, hrpos, (hc.hasEigenvalue_iff_mem_spectrum hrpos.ne').mpr hrSpec, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · simpa [ht0] using hrpos.le
  · exact hrmax ((hc.hasEigenvalue_iff_mem_spectrum ht0).mp ht)

end LichnerowiczObata
