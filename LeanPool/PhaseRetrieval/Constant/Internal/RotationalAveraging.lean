/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # RotationalAveraging.lean
  Rotational averaging lower bound for `rho`.
  Scaffolding notes: ElementaryLemmas/rotational_averaging.md

  Dependencies: Definitions

  Public API:
  - `rotational_averaging_bound` (Theorem 2.6)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.Definitions

/-! # RotationalAveraging -/


open MeasureTheory Real Complex Finset

noncomputable section

namespace FockSPR

/-! ### Auxiliary lemmas for the arc bound -/

/-- `‖1 + r exp(iθ)‖² = 1 + 2r cos(θ) + r²`. -/
private lemma normSq_one_add (r θ : ℝ) :
    ‖(1 : ℂ) + ↑r * Complex.exp (Complex.I * ↑θ)‖ ^ 2 =
    1 + 2 * r * Real.cos θ + r ^ 2 := by
  rw [sq, norm_mul_self_eq_normSq,
    show Complex.I * (↑θ : ℂ) = (↑θ : ℂ) * Complex.I from mul_comm _ _]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.exp_mul_I, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `cos(θ) ≥ √2/2` whenever `|θ| ≤ π/4`. -/
private lemma cos_ge_sqrt2_div2 {θ : ℝ} (hθ : |θ| ≤ Real.pi / 4) :
    Real.cos θ ≥ Real.sqrt 2 / 2 := by
  rw [ge_iff_le, ← Real.cos_pi_div_four, ← Real.cos_abs θ]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (by linarith [Real.pi_pos]) hθ

/-- `‖1 + r exp(iθ)‖ ≥ 1` for `r ≥ 0` and `|θ| ≤ π/4`. -/
private lemma norm_one_add_ge_one {r : ℝ} (hr : 0 ≤ r) {θ : ℝ}
    (hθ : |θ| ≤ Real.pi / 4) :
    ‖(1 : ℂ) + ↑r * Complex.exp (Complex.I * ↑θ)‖ ≥ 1 := by
  rw [ge_iff_le, ← Real.sqrt_one, ← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt
    (by rw [normSq_one_add]; nlinarith [cos_ge_sqrt2_div2 hθ, Real.sqrt_nonneg 2])

/-- When `‖1 + w‖ ≥ 1`, `rho(w) = ‖1 + w‖ − 1`. -/
private lemma rho_eq_norm_sub {w : ℂ} (hw : ‖(1 : ℂ) + w‖ ≥ 1) :
    rho w = ‖(1 : ℂ) + w‖ - 1 := by simp only [rho]; rw [abs_of_nonneg]; linarith

/-- `‖r * exp(iθ)‖ = r` for `r ≥ 0`. -/
private lemma norm_r_exp (r θ : ℝ) (hr : 0 ≤ r) :
    ‖(↑r : ℂ) * Complex.exp (Complex.I * ↑θ)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    show Complex.I * (↑θ : ℂ) = (↑θ : ℂ) * Complex.I from mul_comm _ _,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ## Private Lemma 2.6a: Pointwise bound on an arc

For `r ≥ 0` and `θ ∈ ℝ` with `|θ| ≤ π/4`:
  `rho(r * exp(i θ)) ≥ r / √2`

**Proof of 2.6a**:
- `cos(θ) ≥ 1/√2` for `|θ| ≤ π/4`.
- `|1 + r exp(iθ)|² = 1 + 2r cos(θ) + r²`, so
  `|1 + r exp(iθ)| − 1 = (r² + 2r cos(θ)) / (|1+r exp(iθ)| + 1)`.
- Numerator `≥ r² + √2 r > 0`, so `|1+r exp(iθ)| > 1` and `rho = |1+…| − 1`.
- Denominator `≤ (1 + r) + 1 = r + 2`.
- So `rho ≥ r(r + √2)/(r + 2) ≥ r/√2`.
- Last step: `(r + √2)/(r + 2) ≥ 1/√2` <=> `(√2 − 1)r ≥ 0`. ✓
-/
private lemma rho_arc_lower_bound {r : ℝ} (hr : 0 ≤ r) {θ : ℝ} (hθ : |θ| ≤ Real.pi / 4) :
    rho (↑r * Complex.exp (Complex.I * ↑θ)) ≥ r / Real.sqrt 2 := by
  set w := (↑r : ℂ) * Complex.exp (Complex.I * ↑θ) with hw_def
  have ha1 : ‖(1 : ℂ) + w‖ ≥ 1 := norm_one_add_ge_one hr hθ
  rw [rho_eq_norm_sub ha1]
  set a := ‖(1 : ℂ) + w‖
  have hsq : a ^ 2 = 1 + 2 * r * Real.cos θ + r ^ 2 := normSq_one_add r θ
  have ha_le : a ≤ 1 + r := by
    change ‖(1 : ℂ) + w‖ ≤ 1 + r
    calc ‖(1 : ℂ) + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = 1 + r := by rw [norm_one, norm_r_exp r θ hr]
  have hcos : Real.cos θ ≥ Real.sqrt 2 / 2 := cos_ge_sqrt2_div2 hθ
  have h1 : 0 ≤ a - 1 := by linarith
  have h2 : (a - 1) * (r + 2) ≥ r * (r + Real.sqrt 2) := by
    have hprod : (a - 1) * (a + 1) = r ^ 2 + 2 * r * Real.cos θ := by nlinarith
    nlinarith [Real.sqrt_nonneg 2]
  rw [ge_iff_le, div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)]
  nlinarith [mul_nonneg h1 (Real.sqrt_nonneg 2), mul_nonneg hr (Real.sqrt_nonneg 2),
    mul_nonneg hr h1, sq_nonneg (a - 1 - r / Real.sqrt 2),
    Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 2]

/-! ### Auxiliary lemmas for the integral bound -/

/-- `fourier 1 (↑θ)` equals `exp(i θ)` on `AddCircle (2π)`. -/
private lemma fourier_mk_eq (θ : ℝ) :
    (fourier 1 (QuotientAddGroup.mk θ : AddCircle T) : ℂ) =
    Complex.exp (Complex.I * ↑θ) := by
  simp only [fourier_apply, one_zsmul, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  have : 2 * Real.pi / T = 1 := by unfold T; field_simp
  rw [this, one_mul]; exact mul_comm _ _

/-- The integrand `θ ↦ rho(r * fourier 1 (↑θ))²` is continuous on `ℝ`. -/
private lemma integrand_continuous (r : ℝ) :
    Continuous fun θ : ℝ =>
      (rho (↑r * (fourier 1 (↑θ : AddCircle T) : ℂ))) ^ 2 := by
  apply Continuous.pow; unfold rho
  exact ((Continuous.norm (Continuous.add continuous_const
    (Continuous.mul continuous_const
      ((fourier 1 : C(AddCircle T, ℂ)).continuous.comp
        continuous_quotient_mk')))).sub continuous_const).abs

/-! ## Theorem 2.6: Rotational averaging bound

For `r ≥ 0`:
  `∫ t, rho(r * exp(i t))² d(haar) ≥ r² / 8`

where the integral is w.r.t. normalized Haar measure on `AddCircle T`.

**Proof**:
Step 1: On the arc `{|θ| ≤ π/4}`, `rho(r exp(iθ)) ≥ r/√2` (Private Lemma 2.6a).
Step 2: The arc has measure `1/4` under Haar.
Step 3: `∫ rho² d(haar) ≥ (1/4)(r/√2)² = r²/8`.

**Lean proof**:
Convert to an interval integral on `ℝ` via `integral_haarAddCircle` and
`integral_preimage`, then bound from below on `[-π/4, π/4]`.
-/
theorem rotational_averaging_bound {r : ℝ} (hr : 0 ≤ r) :
    ∫ t : AddCircle T, (rho (↑r * (fourier 1 t : ℂ))) ^ 2 ∂AddCircle.haarAddCircle ≥
      r ^ 2 / 8 := by
  rw [ge_iff_le, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage T (-Real.pi),
    show -Real.pi + T = Real.pi by (unfold T; ring)]
  set f := fun θ : ℝ =>
    (rho (↑r * (fourier 1 (↑θ : AddCircle T) : ℂ))) ^ 2
  -- Lower bound on Icc(-π/4, π/4)
  have h_Icc_bound :
      r ^ 2 / 2 * (Real.pi / 2) ≤
        ∫ θ in Set.Icc (-(Real.pi / 4)) (Real.pi / 4), f θ := by
    have h1 :
        r ^ 2 / 2 * volume.real (Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) ≤
          ∫ θ in Set.Icc (-(Real.pi / 4)) (Real.pi / 4), f θ :=
      setIntegral_ge_of_const_le_real measurableSet_Icc
        (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (fun θ hθ => by
          simp only [f, fourier_mk_eq]
          have habs : |θ| ≤ Real.pi / 4 := abs_le.mpr ⟨hθ.1, hθ.2⟩
          calc r ^ 2 / 2
              = (r / Real.sqrt 2) ^ 2 := by rw [div_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
            _ ≤ _ := pow_le_pow_left₀ (div_nonneg hr (Real.sqrt_nonneg _))
                      (rho_arc_lower_bound hr habs).le 2)
        ((integrand_continuous r).continuousOn.integrableOn_compact isCompact_Icc)
    rwa [Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
      show Real.pi / 4 - -(Real.pi / 4) = Real.pi / 2 from by ring] at h1
  -- Icc integral ≤ Ioc integral (integrand ≥ 0)
  have h_mono :
      ∫ θ in Set.Icc (-(Real.pi / 4)) (Real.pi / 4), f θ ≤
        ∫ θ in Set.Ioc (-Real.pi) Real.pi, f θ := by
    apply setIntegral_mono_set
    · exact ((integrand_continuous r).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact ae_of_all _ fun θ => by positivity
    · exact ae_of_all _ fun θ hθ =>
        ⟨by linarith [hθ.1, Real.pi_pos],
         by linarith [hθ.2, Real.pi_pos]⟩
  -- Combine with T⁻¹ factor
  rw [smul_eq_mul]
  calc r ^ 2 / 8
      = T⁻¹ * (r ^ 2 / 2 * (Real.pi / 2)) := by unfold T; field_simp; ring
    _ ≤ T⁻¹ * ∫ θ in Set.Ioc (-Real.pi) Real.pi, f θ := by
        apply mul_le_mul_of_nonneg_left (le_trans h_Icc_bound h_mono)
        exact inv_nonneg.mpr (le_of_lt T_pos)

end FockSPR
