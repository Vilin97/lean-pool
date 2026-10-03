/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Abstract-real scale arithmetic for the leading-error estimate

Pure real lemmas (no project definitions) used to combine the corrector bounds with the scale
package `left_to_show_scales`: the size of `Χ_{m,k}`, the products `(a ε_m²/κ_m) √κ_m ≤ √K √κ_{m-1}`
and the ratios `ε_m / ε_{m-1}^s ≤ K ε_{m-1}^d`. -/

@[expose] public section

namespace AVenhance.Infra.Section5.RelativeError

/-- The corrector bound `(4π²κ/ε²)⁻¹ |2π a ε| = a ε³/(2πκ)` is at most `ε · (a ε²/κ)`. -/
theorem corrector_size_le {a ε κ : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hκ : 0 < κ) :
    (4 * Real.pi ^ 2 * κ / ε ^ 2)⁻¹ * |2 * Real.pi * a * ε| ≤ ε * (a * ε ^ 2 / κ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ1 : 3 ≤ Real.pi := Real.pi_gt_three.le
  have habs : |2 * Real.pi * a * ε| = 2 * Real.pi * a * ε := abs_of_nonneg (by positivity)
  rw [habs]
  have hid : (4 * Real.pi ^ 2 * κ / ε ^ 2)⁻¹ * (2 * Real.pi * a * ε) =
      (a * ε ^ 3 / κ) / (2 * Real.pi) := by
    field_simp
    ring
  rw [hid]
  have hid2 : ε * (a * ε ^ 2 / κ) = a * ε ^ 3 / κ := by ring
  rw [hid2]
  have hnn : 0 ≤ a * ε ^ 3 / κ := by positivity
  exact div_le_self hnn (by linarith)

/-- `c √κ ≤ √K √κ'` from `a² ε⁴/κ ≤ K κ'`, where `c = a ε²/κ`. -/
theorem corr_mul_sqrt_le {a ε κ K κp : ℝ} (ha : 0 ≤ a) (hκ : 0 < κ)
    (hK : 0 ≤ K) (hκp : 0 ≤ κp) (h : a ^ 2 * ε ^ 4 / κ ≤ K * κp) :
    a * ε ^ 2 / κ * Real.sqrt κ ≤ Real.sqrt K * Real.sqrt κp := by
  have hL : 0 ≤ a * ε ^ 2 / κ * Real.sqrt κ := by positivity
  have hR : 0 ≤ Real.sqrt K * Real.sqrt κp := by positivity
  refine (sq_le_sq₀ hL hR).1 ?_
  have h1 : (a * ε ^ 2 / κ * Real.sqrt κ) ^ 2 = a ^ 2 * ε ^ 4 / κ := by
    rw [mul_pow, Real.sq_sqrt hκ.le]
    field_simp
  have h2 : (Real.sqrt K * Real.sqrt κp) ^ 2 = K * κp := by
    rw [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hκp]
  rw [h1, h2]
  exact h

/-- `ε_m / e^s ≤ K e^d` from `ε_m ≤ K e^q` and `d + s ≤ q`, `0 < e ≤ 1`. -/
theorem eps_ratio_le {εm e K q s d : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hK : 0 ≤ K)
    (hm : εm ≤ K * e ^ q) (hd : d + s ≤ q) : εm / e ^ s ≤ K * e ^ d := by
  have hs : 0 < e ^ s := Real.rpow_pos_of_pos he s
  rw [div_le_iff₀ hs]
  have hqs : e ^ q = e ^ s * e ^ (q - s) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hd' : e ^ (q - s) ≤ e ^ d :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  calc εm ≤ K * e ^ q := hm
    _ = K * e ^ (q - s) * e ^ s := by rw [hqs]; ring
    _ ≤ K * e ^ d * e ^ s := by gcongr

/-- First-order terms: `√κ_m ((20 e c + ε_m c D) ‖∇T‖) ≤ √K (20 + 2^20 K) A e S`. -/
theorem gradient_term_le {c sm sp nT εm e₁ e K A S : ℝ}
    (hsp : 0 ≤ sp) (hnT : 0 ≤ nT) (hεm : 0 ≤ εm) (he₁ : 0 < e₁) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hcs : c * sm ≤ Real.sqrt K * sp) (hT : sp * nT ≤ A * S)
    (hr : εm / e₁ ≤ K * e) :
    sm * ((20 * e * c + εm * c * (16 * (2 ^ 16 * e₁⁻¹))) * nT) ≤
      Real.sqrt K * (20 + 2 ^ 20 * K) * A * e * S := by
  have hK0 : 0 ≤ K := by linarith
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hr0 : 0 ≤ εm / e₁ := div_nonneg hεm he₁.le
  have h1 : sm * ((20 * e * c + εm * c * (16 * (2 ^ 16 * e₁⁻¹))) * nT) =
      (c * sm) * (20 * e + 2 ^ 20 * (εm / e₁)) * nT := by
    rw [div_eq_mul_inv]
    ring
  have hco : 0 ≤ 20 * e + 2 ^ 20 * (εm / e₁) := by positivity
  have h2 : (c * sm) * (20 * e + 2 ^ 20 * (εm / e₁)) * nT ≤
      (Real.sqrt K * sp) * (20 * e + 2 ^ 20 * (K * e)) * nT := by
    have : 20 * e + 2 ^ 20 * (εm / e₁) ≤ 20 * e + 2 ^ 20 * (K * e) := by
      have := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2 ^ 20)
      linarith
    gcongr
  have h3 : (Real.sqrt K * sp) * (20 * e + 2 ^ 20 * (K * e)) * nT =
      Real.sqrt K * (20 + 2 ^ 20 * K) * e * (sp * nT) := by ring
  have h4 : Real.sqrt K * (20 + 2 ^ 20 * K) * e * (sp * nT) ≤
      Real.sqrt K * (20 + 2 ^ 20 * K) * e * (A * S) := by
    apply mul_le_mul_of_nonneg_left hT
    positivity
  calc _ = _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ = _ := by ring

/-- Second-order terms: `√κ_m (4 ε_m c ‖∇∂_pT‖) ≤ 4 √K K A² e S`. -/
theorem hessian_term_le {c sm sp s εm ρ e K A S : ℝ}
    (hs : 0 ≤ s) (hεm : 0 ≤ εm) (hρ : 0 < ρ) (hK : 1 ≤ K) (hS : 0 ≤ S)
    (hcs : c * sm ≤ Real.sqrt K * sp)
    (hT : sp * s ≤ A * (A / ρ) * S) (hr : εm / ρ ≤ K * e) :
    sm * (4 * εm * c * s) ≤ 4 * Real.sqrt K * K * A ^ 2 * e * S := by
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have h1 : sm * (4 * εm * c * s) = 4 * εm * ((c * sm) * s) := by ring
  have h2 : 4 * εm * ((c * sm) * s) ≤ 4 * εm * ((Real.sqrt K * sp) * s) := by gcongr
  have h3 : 4 * εm * ((Real.sqrt K * sp) * s) = 4 * εm * Real.sqrt K * (sp * s) := by ring
  have h4 : 4 * εm * Real.sqrt K * (sp * s) ≤ 4 * εm * Real.sqrt K * (A * (A / ρ) * S) := by
    apply mul_le_mul_of_nonneg_left hT
    positivity
  have h5 : 4 * εm * Real.sqrt K * (A * (A / ρ) * S) =
      4 * Real.sqrt K * A ^ 2 * S * (εm / ρ) := by
    field_simp
  have h6 : 4 * Real.sqrt K * A ^ 2 * S * (εm / ρ) ≤ 4 * Real.sqrt K * A ^ 2 * S * (K * e) := by
    apply mul_le_mul_of_nonneg_left hr
    positivity
  calc _ = _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ = _ := h5
    _ ≤ _ := h6
    _ = _ := by ring

/-- `e^{4δ} ≤ e^{2δ}` for `0 < e ≤ 1`, `0 ≤ δ`. -/
theorem rpow_four_le_two {e δ : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 ≤ δ) :
    e ^ (4 * δ) ≤ e ^ (2 * δ) :=
  Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)

end AVenhance.Infra.Section5.RelativeError
