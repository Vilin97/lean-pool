/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params

/-! Explicit smallness for the finite geometric sums in the transported
`H_m` estimate. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- A finite geometric sum with ratio at most one half is at most two. -/
theorem hm_pow_sum_range_le_two {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, x ^ n ≤ 2 := by
  let S := ∑ n ∈ Finset.range N, x ^ n
  have hgeom : S * (1 - x) = 1 - x ^ N := by
    simpa [S] using geom_sum_mul_of_le_one (show x ≤ 1 by linarith) N
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hdenhalf : 1 / 2 ≤ 1 - x := by linarith
  have hhalf : S * (1 / 2) ≤ S * (1 - x) :=
    mul_le_mul_of_nonneg_left hdenhalf hS0
  have hnum : 1 - x ^ N ≤ 1 := by nlinarith [pow_nonneg hx0 N]
  rw [hgeom] at hhalf
  have hbound : S * (1 / 2) ≤ 1 := hhalf.trans hnum
  dsimp [S] at hbound ⊢
  nlinarith

end AVenhance.Infra.Section4
