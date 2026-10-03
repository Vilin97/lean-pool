/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.GradSnorm

/-! # Step 4: analytic `snorm` bounds for the flow slice

`FlowForErgodicBound A e X` (the derivative bounds `|∇ⁿX| ≤ A n! (A/e)^{n-1}`) gives
`⟦X⟧_{j,2A/e} ≤ K e` for every `j ≥ 1`, with `K` the absolute constant of
`exists_poly_le_two_pow`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff
open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.AnalyticBridge

open AVenhance AVenhance.FaaDiBruno

/-- `(j+1)² ≤ K 2^j`. -/
theorem sq_succ_le_of_poly {K : ℝ} (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n) (j : ℕ) :
    ((j : ℝ) + 1) ^ 2 ≤ K * 2 ^ j := by
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 3) ^ 2 := by gcongr; linarith
  have h2 : ((j : ℝ) + 3) ^ 2 ≤ ((j : ℝ) + 3) ^ 5 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  exact h1.trans (h2.trans (hK j))

/-- Abstract-real core of step 4. -/
theorem flow_bound_real {K : ℝ} (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    {A e : ℝ} (hA : 0 < A) (he : 0 < e) (k : ℕ) :
    A * ((k + 1).factorial : ℝ) * (A / e) ^ k ≤
      K * e * (2 * A / e) ^ (k + 1) * ((k + 1).factorial : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
  have hx : 0 < A / e := div_pos hA he
  have hpos : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hsq := sq_succ_le_of_poly hK (k + 1)
  have hAe : A = e * (A / e) := by field_simp
  have h2 : 2 * A / e = 2 * (A / e) := by ring
  rw [h2]
  set x := A / e with hxdef
  have hfac : (0 : ℝ) ≤ ((k + 1).factorial : ℝ) := Nat.cast_nonneg _
  calc A * ((k + 1).factorial : ℝ) * x ^ k * (((k + 1 : ℕ) : ℝ) + 1) ^ 2
      ≤ A * ((k + 1).factorial : ℝ) * x ^ k * (K * 2 ^ (k + 1)) := by
        gcongr
    _ = K * e * (2 * x) ^ (k + 1) * ((k + 1).factorial : ℝ) := by
        rw [mul_pow, pow_succ x k]
        conv_lhs => rw [hAe]
        ring

/-- Step 4: `⟦X⟧_{j,2A/e} ≤ K e` for `j ≥ 1`. -/
theorem snorm_flow_le {K : ℝ} (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    {A e : ℝ} (hA : 0 < A) (he : 0 < e) {X : Vec 2 → Vec 2}
    (hX : FlowForErgodicBound A e X) (j : ℕ) (hj : 1 ≤ j) :
    snorm X j (2 * A / e) ≤ ENNReal.ofReal (K * e) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  refine snorm_le_of_derivativeSup_le X (by positivity) ?_
  refine (hX (k + 1) hj).trans (ENNReal.ofReal_le_ofReal ?_)
  simpa using flow_bound_real hK hA he k

end AVenhance.Infra.Section5.AnalyticBridge

end
