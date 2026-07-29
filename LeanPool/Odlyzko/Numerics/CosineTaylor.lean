/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

/-- A cos lower six used in the Odlyzko-bound argument. -/
noncomputable def cosLowerSix (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

theorem taylorWithinEval_cos_eight {x : ℝ} (hx0 : x ≠ 0) :
    taylorWithinEval Real.cos 8 (Set.uIcc 0 x) 0 x =
      cosLowerSix x + x ^ 8 / 40320 := by
  rw [taylor_within_apply]
  -- `uniqueDiffOn_uIcc` postdates v4.32; derive it from `uniqueDiffOn_Icc`.
  have hu : UniqueDiffOn ℝ (Set.uIcc 0 x) := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · rw [Set.uIcc_of_ge h.le]; exact uniqueDiffOn_Icc h
    · rw [Set.uIcc_of_le h.le]; exact uniqueDiffOn_Icc h
  have hmem : (0 : ℝ) ∈ Set.uIcc 0 x := Set.left_mem_uIcc
  simp_rw [iteratedDerivWithin_eq_iteratedDeriv hu Real.contDiff_cos.contDiffAt hmem]
  simp only [Finset.sum_range_succ,
    smul_eq_mul, sub_zero,
    ]
  norm_num [cosLowerSix]
  ring

theorem cosLowerSix_le_cos {x : ℝ} (hx : |x| ≤ 4) :
    cosLowerSix x ≤ Real.cos x := by
  by_cases hx0 : x = 0
  · simp [hx0, cosLowerSix]
  obtain ⟨c, hc, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.cos) (n := 8)
      (Ne.symm hx0) Real.contDiff_cos.contDiffOn
  rw [taylorWithinEval_cos_eight hx0] at hrem
  have hderiv : iteratedDeriv 9 Real.cos c = -Real.sin c := by
    (convert congrFun (Real.iteratedDeriv_odd_cos 4) c using 1; norm_num)
  rw [hderiv] at hrem
  have hpow8 : 0 ≤ x ^ 8 := by positivity
  have hremLower :
      -(x ^ 8 * |x| / 362880) ≤ Real.cos x -
        (cosLowerSix x + x ^ 8 / 40320) := by
    rw [hrem]
    have hfac : (9 : ℕ).factorial = 362880 := by norm_num
    rw [hfac]
    have habssin : |Real.sin c| ≤ 1 := Real.abs_sin_le_one c
    have habsprod :
        |(-Real.sin c) * x ^ 9| ≤ |x| ^ 9 := by simp_all
    have habspow : |x| ^ 9 = x ^ 8 * |x| := by
      rw [pow_succ]
      have heven : |x| ^ 8 = x ^ 8 := by
        rw [← abs_pow, abs_of_nonneg hpow8]
      simp_all
    grind
  have hdom : x ^ 8 * |x| / 362880 ≤ x ^ 8 / 40320 := by
    have : x ^ 8 * |x| ≤ x ^ 8 * 9 := by (gcongr; linarith)
    grind
  linarith

end NumberField.Odlyzko
