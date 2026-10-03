/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmParameterTransfers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Abstract-real scalar algebra for the `HTilde_m` gradient bound (16)-(18)

Pure real-number lemmas: the geometric `r₀`-sum after the `τ'` cancellation, the elimination
of `1/√ν`, and the `ε_{m-1}^{-(2+γ)}` rpow identity.  No `Real.exp` and no transcendental
`nlinarith`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

/-- The `r₀`-th term, with `τ'^{-r₀}` cancelled against `(8τ)^{r₀+1}`. -/
theorem leh_term_eq (N Z c P t t' : ℝ) (r : ℕ) :
    16 * N * (Z * (t'⁻¹) ^ r) * (c * P * (8 * t) ^ (r + 1)) =
      (16 * N * Z * c * P * (8 * t)) * (8 * t / t') ^ r := by
  rw [div_eq_mul_inv, mul_pow, inv_pow, pow_succ]
  ring

/-- The geometric sum after the cancellation. -/
theorem leh_sum_le (J : ℕ) {D x : ℝ} (hD : 0 ≤ D) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    ∑ r ∈ Finset.range J, D * x ^ r ≤ 2 * D := by
  rw [← Finset.mul_sum]
  have := AVenhance.Infra.Section4.hm_pow_sum_range_le_two hx0 hx J
  nlinarith only [this, hD]

/-- `ε^{-(1+γ/2)}` squared times `ε^{2+γ}` is one. -/
theorem leh_rpow_neg_sq_mul {E g : ℝ} (hE : 0 < E) :
    (E ^ (-(1 + g / 2))) ^ 2 * E ^ (2 + g) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le, ← Real.rpow_add hE]
  have : -(1 + g / 2) * ((2 : ℕ) : ℝ) + (2 + g) = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

/-- The scale chain `ν τ L² ≤ C 2^{-28} ε^{4δ}`. -/
theorem leh_nu_t_L2_le {ν C a t L2 G c28 E4 : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (hL : 0 ≤ L2)
    (hν : ν ≤ C * (a * G)) (hLG : L2 * G = 1) (hat : a * t ≤ c28 * E4) :
    ν * t * L2 ≤ C * (c28 * E4) := by
  calc
    ν * t * L2 ≤ C * (a * G) * t * L2 := by
      gcongr
    _ = C * (a * t) * (L2 * G) := by ring
    _ = C * (a * t) := by rw [hLG, mul_one]
    _ ≤ C * (c28 * E4) := by gcongr

/-- Final real chain: `√μ √2 (2 D) ≤ 256 √2 N c CA K S (ν τ L²)`. -/
theorem leh_final_real {N c CA K S μ ν t L2 X Cn : ℝ}
    (hN : 0 ≤ N) (hc : 0 ≤ c) (hCA : 0 ≤ CA) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hμ : 0 < μ) (hμν : μ ≤ ν) (ht : 0 ≤ t) (hL : 0 ≤ L2) (hX0 : 0 ≤ X) (hX : X ≤ K * ν)
    (hνt : ν * t * L2 ≤ Cn) :
    Real.sqrt μ * (Real.sqrt 2 * (2 * ((128 * N * c * CA) * (S / Real.sqrt ν) * X * t * L2))) ≤
      256 * Real.sqrt 2 * N * c * CA * K * S * Cn := by
  have hν : 0 < ν := lt_of_lt_of_le hμ hμν
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsq : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt hν.le
  have hsμ : Real.sqrt μ ≤ Real.sqrt ν := Real.sqrt_le_sqrt hμν
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set s := Real.sqrt ν with hsdef
  have hrest : 0 ≤ Real.sqrt 2 * (2 * ((128 * N * c * CA) * (S / s) * X * t * L2)) := by
    positivity
  calc
    Real.sqrt μ * (Real.sqrt 2 * (2 * ((128 * N * c * CA) * (S / s) * X * t * L2)))
        ≤ s * (Real.sqrt 2 * (2 * ((128 * N * c * CA) * (S / s) * X * t * L2))) :=
      mul_le_mul_of_nonneg_right hsμ hrest
    _ = 256 * Real.sqrt 2 * N * c * CA * S * X * t * L2 := by
      field_simp
      ring
    _ ≤ 256 * Real.sqrt 2 * N * c * CA * S * (K * ν) * t * L2 := by
      gcongr
    _ = 256 * Real.sqrt 2 * N * c * CA * K * S * (ν * t * L2) := by ring
    _ ≤ 256 * Real.sqrt 2 * N * c * CA * K * S * Cn := by gcongr

end AVenhance.Infra.Section5.RelativeError
