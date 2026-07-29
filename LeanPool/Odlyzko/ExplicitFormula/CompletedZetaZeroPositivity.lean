/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeRectangles
public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouPositivity

/-!
# Completed Zeta Zero Positivity

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem completedDedekindZetaZeroDivisor_support_re_mem_Icc
    {s : ℂ} (hs : s ∈ (completedDedekindZetaZeroDivisor K).support) :
    s.re ∈ Icc 0 1 := by
  have hs0 :
      poleClearedCompletedDedekindZetaContinuation K s = 0 :=
    poleClearedCompletedDedekindZetaContinuation_eq_zero_of_mem_support K hs
  constructor
  · by_contra h
    exact poleClearedCompletedDedekindZetaContinuation_ne_zero_of_re_lt_zero K
      (lt_of_not_ge h) hs0
  · by_contra h
    exact poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (lt_of_not_ge h) hs0

private theorem completedDedekindZetaZeroDivisor_apply_nonneg (s : ℂ) :
    0 ≤ (completedDedekindZetaZeroDivisor K s : ℤ) := by
  have h :=
    meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_nonneg K s
  rw [meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_eq_divisor K s] at h
  simp_all

private theorem re_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
    (Φ : ℂ → ℂ) {s : ℂ} (hΦ : 0 ≤ (Φ s).re) :
    0 ≤ (Φ s * (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  norm_num [mul_re]
  exact mul_nonneg hΦ
    (by exact_mod_cast completedDedekindZetaZeroDivisor_apply_nonneg K s)

theorem re_sum_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
    (Φ : ℂ → ℂ) {S : Finset ℂ}
    (hΦ : ∀ s ∈ S, 0 ≤ (Φ s).re) :
    0 ≤ (∑ s ∈ S, Φ s *
      (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert s S hsnot ih =>
      rw [Finset.sum_insert hsnot, add_re]
      exact add_nonneg
        (re_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
          K Φ (hΦ s (Finset.mem_insert_self s S)))
        (ih fun z hz ↦ hΦ z (Finset.mem_insert_of_mem hz))

end NumberField.Odlyzko
