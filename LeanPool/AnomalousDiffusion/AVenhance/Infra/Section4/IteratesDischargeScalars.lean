/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params

/-! # Iterates Discharge Scalars

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open AVenhance

/-- The two averaging errors retain their distinct powers and constants. -/
def iterateMeanScaleConstant (β Ccut P : ℝ) : ℝ :=
  (160 / 9) * ((4 * Real.pi ^ 2 * Ccut * Nstar β * 2 ^ Nstar β) * P ^ Nstar β +
    (2 * Nstar β * Ccut * ((Nstar β).factorial : ℝ) *
      2 ^ Nstar β * 2 ^ Nstar β * Ccut ^ 2 * 8 ^ Nstar β) * (1 / 4 : ℝ) ^ Nstar β)

/-- The same squared coefficient budget controls the terminal-aware ratio and
one-step averaging error. Its inputs are scalar coefficients, not PDE bounds. -/
theorem iterate_discharge_smallness {x P L r : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hr : r ≤ P * x ^ 2) (hsmall : x ^ 2 ≤ (smallnessBudget 0 P L)⁻¹) :
    r ≤ 1 / 2 ∧ L * (r + x) ≤ 9 / 160 := by
  let D := smallnessBudget 0 P L
  have hD : 0 < D := by unfold D smallnessBudget; positivity
  have hDP : 2 * P ≤ D := by
    unfold D smallnessBudget
    nlinarith only [sq_nonneg ((320 / 9 : ℝ) * L * (1 + P))]
  have hPL : P * x ^ 2 ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall hP
    have h2 : P * D⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hD).mpr
      linarith only [hDP]
    exact h1.trans h2
  have hDL : 4 * ((160 / 9) * L * (1 + P)) ^ 2 ≤ D := by
    unfold D smallnessBudget
    nlinarith only [hP]
  have hlin := linear_smallness_of_square hx
    (show 0 ≤ (160 / 9) * L * (1 + P) by positivity) hD hDL hsmall
  have hx2 : x ^ 2 ≤ x := by nlinarith only [mul_nonneg hx (sub_nonneg.mpr hx1)]
  have hrr := hr.trans (mul_le_mul_of_nonneg_left hx2 hP)
  have hb := mul_le_mul_of_nonneg_left (add_le_add_right hrr x) hL
  have ha : L * (P * x + x) ≤ 9 / 320 := by nlinarith only [hlin]
  constructor
  · exact hr.trans hPL
  · nlinarith only [hb, ha]

/-- Both finite-average error powers have the required rho gain. -/
theorem iterate_two_error_mean_scale {e δ κprev B A D P r h : ℝ} {N : ℕ}
    (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hN : 2 ≤ N)
    (hκ : 0 ≤ κprev) (hA : 0 ≤ A) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hr : 0 ≤ r) (hrP : r ≤ P * e ^ (2 * δ))
    (hh : 0 ≤ h) (hhP : h ≤ (1 / 4) * e ^ δ)
    (hsize : B ≤ (160 / 9) * κprev) :
    B * (A * r ^ N + D * h ^ N) ≤
      κprev * ((160 / 9) * (A * P ^ N + D * (1 / 4 : ℝ) ^ N)) * e ^ (2 * δ) := by
  have hrpow := pow_le_pow_left₀ hr hrP N
  have hhpow := pow_le_pow_left₀ hh hhP N
  have hρ : 0 ≤ e ^ (2 * δ) := Real.rpow_nonneg he.le _
  have hρ1 : e ^ (2 * δ) ≤ 1 := Real.rpow_le_one he.le he1 (by positivity)
  have hρpow : (e ^ (2 * δ)) ^ N ≤ e ^ (2 * δ) :=
    by simpa only [pow_one] using pow_le_pow_of_le_one hρ hρ1 (by omega : 1 ≤ N)
  have hcast : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : 2 * δ ≤ δ * (N : ℝ) := by
    calc
      2 * δ = δ * 2 := by ring
      _ ≤ δ * (N : ℝ) := mul_le_mul_of_nonneg_left hcast hδ.le
  have hδpow : (e ^ δ) ^ N ≤ e ^ (2 * δ) := by
    rw [← Real.rpow_mul_natCast he.le]
    exact Real.rpow_le_rpow_of_exponent_ge he he1 hexp
  rw [mul_pow] at hrpow hhpow
  have hrbound := hrpow.trans (mul_le_mul_of_nonneg_left hρpow (pow_nonneg hP N))
  have hhbound := hhpow.trans (mul_le_mul_of_nonneg_left hδpow (by positivity : 0 ≤ (1 / 4 : ℝ) ^
      N))
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hrbound hA)
    (mul_le_mul_of_nonneg_left hhbound hD)
  have hm := mul_le_mul hsize hsum (by positivity : 0 ≤ A * r ^ N + D * h ^ N)
    (mul_nonneg (by norm_num) hκ)
  convert hm using 1
  ring

/-- Enlarging the l.V constant absorbs the cheap-input threshold without an
additional data-dependent smallness parameter. -/
theorem iterate_discharge_threshold_from_source {C₀ D ρ : ℝ}
    (hC : 1 ≤ C₀) (hDp : 0 < D) (hD : D ≤ C₀)
    (hsmall : ρ ≤ (4 * C₀ ^ 3)⁻¹) : ρ ≤ D⁻¹ := by
  have hpow : C₀ ≤ C₀ ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by norm_num : 1 ≤ (3 : ℕ))
  have hCp : 0 < C₀ := by linarith only [hC]
  have hb : D ≤ 4 * C₀ ^ 3 := by linarith only [hD, hpow, hCp]
  exact hsmall.trans ((inv_le_inv₀ (by positivity : 0 < 4 * C₀ ^ 3) hDp).mpr hb)

end AVenhance.Infra.Section4
