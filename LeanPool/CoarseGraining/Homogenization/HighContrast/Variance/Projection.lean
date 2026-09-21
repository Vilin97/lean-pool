/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Variance as the smallest quadratic distance to a constant

Two elementary `L²` facts underlying the opening step in the proof of
`t.block.variance`:

  `Var[F] ≤ 𝔼[(F − 𝔼[F_σ])²] ≤ 2·𝔼[|F − F_σ|²] + 2·Var[F_σ]`.

* `variance_le_integral_sub_const` : `Var[F] ≤ ∫ (F − c)²` for any constant `c`
  (variance is the smallest mean-square distance to a constant).
* `var_le_two_integral_add_two_var` : the `(x+y)² ≤ 2x² + 2y²` split, taking
  `c = 𝔼[G]` so the second term is exactly `Var[G]`.
-/

namespace Homogenization

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Variance is the smallest quadratic distance to a constant.** -/
theorem variance_le_integral_sub_const {F : Ω → ℝ} (hF : MemLp F 2 μ) (c : ℝ) :
    Var[F; μ] ≤ ∫ ω, (F ω - c) ^ 2 ∂μ := by
  have hFint : Integrable F μ := hF.integrable (by norm_num)
  set e := μ[F] with hedef
  have hI1 : Integrable (fun ω => (F ω - e) ^ 2) μ :=
    (hF.sub (memLp_const e)).integrable_sq
  have hI2c : Integrable (fun ω => (e - c) * (2 * F ω - c - e)) μ :=
    (((hFint.const_mul 2).sub (integrable_const c)).sub (integrable_const e)).const_mul (e - c)
  have hlin : (∫ ω, (2 * F ω - c - e) ∂μ) = e - c := by
    have h1 : (fun ω => 2 * F ω - c - e) =ᵐ[μ] (fun ω => 2 * F ω - (c + e)) := by
      filter_upwards with ω; ring
    rw [integral_congr_ae h1, integral_sub (hFint.const_mul 2) (integrable_const _),
      integral_const_mul, integral_const, ← hedef]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  have hexp : (∫ ω, (F ω - c) ^ 2 ∂μ)
      = (∫ ω, (F ω - e) ^ 2 ∂μ) + (e - c) ^ 2 := by
    have hcongr : (fun ω => (F ω - c) ^ 2)
        =ᵐ[μ] (fun ω => (F ω - e) ^ 2 + (e - c) * (2 * F ω - c - e)) := by
      filter_upwards with ω; ring
    rw [integral_congr_ae hcongr, integral_add hI1 hI2c, integral_const_mul, hlin]
    ring
  rw [variance_eq_integral hF.aestronglyMeasurable.aemeasurable, hexp]
  nlinarith [sq_nonneg (e - c)]

/-- **The `(x+y)² ≤ 2x² + 2y²` split.**  With `c = 𝔼[G]`, the constant-distance
bound of `variance_le_integral_sub_const` becomes `2·∫(F−G)² + 2·Var[G]`. -/
theorem var_le_two_integral_add_two_var {F G : Ω → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Var[F; μ] ≤ 2 * (∫ ω, (F ω - G ω) ^ 2 ∂μ) + 2 * Var[G; μ] := by
  have h1 : Var[F; μ] ≤ ∫ ω, (F ω - μ[G]) ^ 2 ∂μ :=
    variance_le_integral_sub_const hF (μ[G])
  have hpt : (fun ω => (F ω - μ[G]) ^ 2)
      ≤ fun ω => 2 * (F ω - G ω) ^ 2 + 2 * (G ω - μ[G]) ^ 2 := by
    intro ω
    nlinarith [sq_nonneg ((F ω - G ω) - (G ω - μ[G]))]
  have hFG : Integrable (fun ω => (F ω - G ω) ^ 2) μ := (hF.sub hG).integrable_sq
  have hGc : Integrable (fun ω => (G ω - μ[G]) ^ 2) μ :=
    (hG.sub (memLp_const _)).integrable_sq
  have hFc : Integrable (fun ω => (F ω - μ[G]) ^ 2) μ :=
    (hF.sub (memLp_const _)).integrable_sq
  have h2 : (∫ ω, (F ω - μ[G]) ^ 2 ∂μ)
      ≤ ∫ ω, (2 * (F ω - G ω) ^ 2 + 2 * (G ω - μ[G]) ^ 2) ∂μ :=
    integral_mono hFc ((hFG.const_mul 2).add (hGc.const_mul 2)) hpt
  rw [integral_add (hFG.const_mul 2) (hGc.const_mul 2), integral_const_mul,
    integral_const_mul] at h2
  have hvarG : (∫ ω, (G ω - μ[G]) ^ 2 ∂μ) = Var[G; μ] :=
    (variance_eq_integral hG.aestronglyMeasurable.aemeasurable).symm
  rw [hvarG] at h2
  linarith [h1, h2]

end Homogenization
