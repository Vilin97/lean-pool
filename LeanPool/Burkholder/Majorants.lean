/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.Burkholder.Majorants.Definitions
import LeanPool.Burkholder.Majorants.MajorantPL2
import LeanPool.Burkholder.Majorants.MajorantPG2
import LeanPool.Burkholder.Majorants.MajorantPEq2

/-!
# Burkholder majorants: existence of the special function

Assembles the regime-by-regime constructions into the existence of a Burkholder
majorant for every exponent `p > 1`.
-/

noncomputable section



namespace Majorants


/- Final result: majorant exists for p > 1 -/

/--
Main existence theorem for the Burkholder majorant when `p > 1`.

In plain terms: this says we can build a function `u` (with first derivatives)
that has controlled growth, satisfies the tangent-step inequality used in the
martingale argument, dominates the base Burkholder function `v`, and is
nonpositive on the opposite-sign region `x * y ≤ 0`.

The proof dispatches to the specialized constructions in the three regimes
`p = 2`, `p > 2`, and `1 < p < 2`.
-/
theorem exists_majorant_p_g_1 (p : ℝ) (hp : p > 1) :
    ∃ u du_dx du_dy : ℝ → ℝ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Set.univ ∧
      ContinuousOn (fun z : ℝ × ℝ => du_dx z.1 z.2) Set.univ ∧
      ContinuousOn (fun z : ℝ × ℝ => du_dy z.1 z.2) Set.univ ∧
      (∀ x y,
       |u x y| ≤ C * (Real.rpow |x| p + Real.rpow |y| p)) ∧
      (∀ x y,
        |du_dx x y| ≤ C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y,
        |du_dy x y| ≤ C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y h k, h * k ≤  0 →
          u (x + h) (y + k) ≤ u x y + du_dx x y * h + du_dy x y * k) ∧
      (∀ x y, v p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, p ≠ 2∧ x*y = 0 ∧ (x,y) ≠ (0,0) → u x y < 0)  := by
        by_cases hp2 : p = 2
        · -- Case p = 2
          rcases exists_majorant_p_eq_2 p hp2 with
            ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
              hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, _haxis⟩
          refine ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
            hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, ?_⟩
          intro x y hxy
          exact False.elim (hxy.1 hp2)
        by_cases hp_gt_2 : 2 < p
        · -- Case p > 2
          rcases exists_majorant_geTwo p hp_gt_2 with
            ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
              hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, haxis⟩
          refine ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
            hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, ?_⟩
          intro x y hxy
          exact haxis x y ⟨hxy.2.1, hxy.2.2⟩
        -- Case 1 < p < 2
        have hp1 : 1 < p := hp
        have hp_lt_2 : p < 2 := lt_of_le_of_ne (le_of_not_gt hp_gt_2) hp2
        rcases exists_majorant_leTwo p ⟨hp1, hp_lt_2⟩ with
          ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
            hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, haxis⟩
        refine ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
          hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, ?_⟩
        intro x y hxy
        exact haxis x y ⟨hxy.2.1, hxy.2.2⟩





end Majorants
