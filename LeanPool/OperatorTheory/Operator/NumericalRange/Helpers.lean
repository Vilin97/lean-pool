/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Recovered helper lemmas for the numerical range

These lemmas reconstruct identities lost during the accidental deletion.
They support the recovered convexity and spectrum-inclusion proofs.
-/
import LeanPool.OperatorTheory.Operator.NumericalRange.Basic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_inv_norm_smul {x : E} (hx : x ≠ 0) :
    ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem inner_apply_real_smul_add_real_smul (A : E →L[ℂ] E)
    (x₀ x₁ : E) (ω : ℂ) (u v : ℝ) :
    ⟪(u : ℂ) • x₀ + (v : ℂ) • (ω • x₁),
      A ((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁))⟫_ℂ =
    (u : ℂ) ^ 2 * ⟪x₀, A x₀⟫_ℂ +
      ((u * v : ℝ) : ℂ) *
        (ω * ⟪x₀, A x₁⟫_ℂ + starRingEnd ℂ ω * ⟪x₁, A x₀⟫_ℂ) +
      (v : ℂ) ^ 2 * (‖ω‖ ^ 2 : ℂ) * ⟪x₁, A x₁⟫_ℂ := by
  simp only [map_add, map_smul]
  simp only [inner_add_left, inner_add_right]
  simp only [inner_smul_left, inner_smul_right]
  rw [← Complex.conj_mul' ω]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

theorem inner_apply_self_eq_of_not_linearIndependent (A : E →L[ℂ] E)
    {x₀ x₁ : E} (hx₀ : ‖x₀‖ = 1) (hx₁ : ‖x₁‖ = 1)
    (h : ¬ LinearIndependent ℂ ![x₀, x₁]) :
    ⟪x₀, A x₀⟫_ℂ = ⟪x₁, A x₁⟫_ℂ := by
  have hx₀_ne : x₀ ≠ 0 := by
    intro hx₀_zero
    rw [hx₀_zero, norm_zero] at hx₀
    norm_num at hx₀
  rw [LinearIndependent.pair_iff' hx₀_ne, not_forall] at h
  simp only [not_ne_iff] at h
  obtain ⟨c, hc⟩ := h
  have hc_norm : ‖c‖ = 1 := by
    calc
      ‖c‖ = ‖c‖ * ‖x₀‖ := by rw [hx₀, mul_one]
      _ = ‖c • x₀‖ := (norm_smul c x₀).symm
      _ = ‖x₁‖ := congrArg norm hc
      _ = 1 := hx₁
  rw [← hc, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', hc_norm]
  norm_num

theorem inner_smul_sub_smul_one_apply_self (c : ℂ) (z₀ : ℂ) (A : E →L[ℂ] E)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (c • (A - z₀ • 1)) x⟫_ℂ = c * (⟪x, A x⟫_ℂ - z₀) := by
  simp only [smul_apply, sub_apply, one_apply_eq_self, inner_smul_right, inner_sub_right,
    inner_self_eq_norm_sq_to_K, hx, mul_sub]
  norm_num

theorem inner_sub_smul_one_apply_self (A : E →L[ℂ] E) (l : ℂ)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (A - l • 1) x⟫_ℂ = ⟪x, A x⟫_ℂ - l := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hx]
  norm_num

theorem smul_add_smul_mem_numericalRange_of_mem_normalized (A : E →L[ℂ] E)
    {z₀ z₁ : ℂ} (hz : z₀ ≠ z₁)
    {a b : ℝ} (hab : a + b = 1)
    (hb : (b : ℂ) ∈ numericalRange ((z₁ - z₀)⁻¹ • (A - z₀ • 1))) :
    a • z₀ + b • z₁ ∈ numericalRange A := by
  obtain ⟨x, hx, hinner⟩ := hb
  refine ⟨x, hx, ?_⟩
  rw [inner_smul_sub_smul_one_apply_self _ _ A hx] at hinner
  have hdenom : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr hz.symm
  field_simp [hdenom] at hinner
  have habc := congrArg (fun r : ℝ => (r : ℂ)) hab
  push_cast at habc
  change ⟪x, A x⟫_ℂ = (a : ℂ) * z₀ + (b : ℂ) * z₁
  calc
    ⟪x, A x⟫_ℂ = z₀ + (⟪x, A x⟫_ℂ - z₀) := by ring
    _ = z₀ + (z₁ - z₀) * (b : ℂ) := by rw [hinner]
    _ = ((a : ℂ) + (b : ℂ)) * z₀ + (z₁ - z₀) * (b : ℂ) := by
      rw [habc, one_mul]
    _ = (a : ℂ) * z₀ + (b : ℂ) * z₁ := by ring

theorem inner_inv_norm_smul_apply (A : E →L[ℂ] E) {x : E} (hx : x ≠ 0) :
    ⟪((‖x‖ : ℂ)⁻¹) • x, A (((‖x‖ : ℂ)⁻¹) • x)⟫_ℂ =
    ⟪x, A x⟫_ℂ / (‖x‖ : ℂ) ^ 2 := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul']
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x)]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hx]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
