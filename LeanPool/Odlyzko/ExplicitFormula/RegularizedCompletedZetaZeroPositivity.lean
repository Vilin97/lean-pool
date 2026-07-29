/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaZeroPositivity
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouPositivity

/-!
# Regularized Completed Zeta Zero Positivity

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem re_poitouTransform_regularized_nonneg_of_completedZetaZero
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s ∈ (completedDedekindZetaZeroDivisor K).support) :
    0 ≤ (poitouTransform (regularizedScaledTartar y δ) s).re :=
  re_poitouTransform_regularizedScaledTartar_nonneg hy hδ
    (completedDedekindZetaZeroDivisor_support_re_mem_Icc K hs)

theorem re_sum_poitouTransform_regularized_mul_completedZetaZeroDivisor_nonneg
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {S : Finset ℂ}
    (hS : ∀ s ∈ S, s ∈ (completedDedekindZetaZeroDivisor K).support) :
    0 ≤ (∑ s ∈ S, poitouTransform (regularizedScaledTartar y δ) s *
      (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  apply re_sum_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
  intro s hs
  exact re_poitouTransform_regularized_nonneg_of_completedZetaZero
    K hy hδ (hS s hs)

theorem re_sum_poitouTransform_regularized_completedZetaZerosInClosedRectangle_nonneg
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ)
    (a b u v : ℝ) :
    0 ≤
      (∑ s ∈ completedDedekindZetaZerosInClosedRectangle K a b u v,
        poitouTransform (regularizedScaledTartar y δ) s *
          (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  apply
    re_sum_poitouTransform_regularized_mul_completedZetaZeroDivisor_nonneg
      K hy hδ
  intro s hs
  exact
    (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hs |>.2

end NumberField.Odlyzko
