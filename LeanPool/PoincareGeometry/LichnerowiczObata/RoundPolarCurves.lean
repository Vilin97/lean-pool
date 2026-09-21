/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Explicit unit-speed polar curves on a round sphere -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The meridian with pole direction `p`, initial direction `q`, and radius `R`. -/
def roundPolarCurve (R : ℝ) (p q : E) (s : ℝ) : E :=
  R • (Real.cos (s / R) • p + Real.sin (s / R) • q)

theorem norm_orthonormal_pair (p q : E) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℝ p q = 0) (a b : ℝ) :
    ‖a • p + b • q‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, hp, hq, real_inner_smul_left, real_inner_smul_right, hpq, sq_abs]

/-- The explicit meridian lies on the actual metric sphere. -/
theorem roundPolarCurve_mem_sphere {R : ℝ} (hR : 0 < R) (p q : E)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℝ p q = 0) (s : ℝ) :
    roundPolarCurve R p q s ∈ Metric.sphere (0 : E) R := by
  have hn := norm_orthonormal_pair p q hp hq hpq (Real.cos (s / R)) (Real.sin (s / R))
  have hu : ‖Real.cos (s / R) • p + Real.sin (s / R) • q‖ = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (s / R),
      norm_nonneg (Real.cos (s / R) • p + Real.sin (s / R) • q)]
  simp only [Metric.mem_sphere, dist_zero_right, roundPolarCurve, norm_smul,
    Real.norm_eq_abs, abs_of_pos hR, hu, mul_one]

/-- Arc length is the time parameter in this explicit round-sphere curve. -/
theorem hasDerivAt_roundPolarCurve {R : ℝ} (hR : R ≠ 0) (p q : E) (s : ℝ) :
    HasDerivAt (roundPolarCurve R p q)
      ((-Real.sin (s / R)) • p + Real.cos (s / R) • q) s := by
  have hd := ((((hasDerivAt_id s).div_const R).cos.smul_const p).add
    (((hasDerivAt_id s).div_const R).sin.smul_const q)).const_smul R
  convert hd using 1
  · rfl
  · simp only [id_eq, smul_add, smul_smul]
    have hmul (a : ℝ) : R * (a * (1 / R)) = a := by field_simp
    rw [hmul, hmul]

theorem roundPolarCurve_velocity_norm (p q : E) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℝ p q = 0) (R s : ℝ) :
    ‖(-Real.sin (s / R)) • p + Real.cos (s / R) • q‖ = 1 := by
  have hn := norm_orthonormal_pair p q hp hq hpq (-Real.sin (s / R)) (Real.cos (s / R))
  nlinarith [Real.sin_sq_add_cos_sq (s / R),
    norm_nonneg ((-Real.sin (s / R)) • p + Real.cos (s / R) • q)]

@[simp] theorem roundPolarCurve_zero (R : ℝ) (p q : E) :
    roundPolarCurve R p q 0 = R • p := by
  simp [roundPolarCurve]

/-- All meridians reach the same antipodal pole at distance `π R`. -/
theorem roundPolarCurve_antipode {R : ℝ} (hR : R ≠ 0) (p q : E) :
    roundPolarCurve R p q (Real.pi * R) = -(R • p) := by
  simp [roundPolarCurve, mul_div_cancel_right₀ _ hR]

end LichnerowiczObata
