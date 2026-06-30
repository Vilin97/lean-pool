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


/-!
# Burkholder majorant for `p = 2`

Constructs the Burkholder majorant in the special case `p = 2`.
-/

noncomputable section



namespace Majorants

/--
Explicit majorant package in the special case `p = 2`.

At this exponent the construction becomes very concrete: we can take
`u(x,y) = x*y`, with derivatives `du_dx = y` and `du_dy = x`.
This theorem checks, one by one, that this choice satisfies the full list of
majorant requirements (growth, tangency, domination of `v`, and sign behavior).
-/
theorem exists_majorant_p_eq_2 (p : ℝ) (hp : p = 2) :
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
      (∀ x y, x*y = 0  ↔ u x y = 0):= by
  subst p
  refine ⟨fun x y => x * y, fun _ y => y, fun x _ => x, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · exact (continuous_fst.mul continuous_snd).continuousOn
  · exact continuous_snd.continuousOn
  · exact continuous_fst.continuousOn
  · intro x y
    have hsq : 2 * |x| * |y| ≤ |x| ^ 2 + |y| ^ 2 := by
      nlinarith [sq_nonneg (|x| - |y|)]
    have hxy_le : |x * y| ≤ |x| ^ 2 + |y| ^ 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg x, abs_nonneg y]
    simpa [Real.rpow_two, sq_abs] using hxy_le
  · intro x y
    have hle : |y| ≤ |x| + |y| := by
      exact le_add_of_nonneg_left (abs_nonneg x)
    calc
      |y| ≤ |x| + |y| := hle
      _ = Real.rpow |x| (2 - 1) + Real.rpow |y| (2 - 1) := by
        norm_num [Real.rpow_one]
      _ = 1 * (Real.rpow |x| (2 - 1) + Real.rpow |y| (2 - 1)) := by ring
  · intro x y
    have hle : |x| ≤ |x| + |y| := by
      exact le_add_of_nonneg_right (abs_nonneg y)
    calc
      |x| ≤ |x| + |y| := hle
      _ = Real.rpow |x| (2 - 1) + Real.rpow |y| (2 - 1) := by
        norm_num [Real.rpow_one]
      _ = 1 * (Real.rpow |x| (2 - 1) + Real.rpow |y| (2 - 1)) := by ring
  · intro x y h k hk
    nlinarith
  · intro x y
    calc
      v 2 x y = x * y := by
        unfold v
        norm_num [pStar, q]
        ring
      _ ≤ x * y := le_rfl
  · intro x y hxy
    exact hxy
  · intro x y
    rfl

end Majorants
