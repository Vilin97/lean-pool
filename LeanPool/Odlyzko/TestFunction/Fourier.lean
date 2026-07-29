/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Weight
public import LeanPool.Odlyzko.TestFunction.Amplitude

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory Set

namespace NumberField.Odlyzko

theorem intervalIntegral_one_sub_sq_mul_cos {x : ℝ} (hx : x ≠ 0) :
    ∫ t : ℝ in (-1)..1, (1 - t ^ 2) * Real.cos (x * t) =
      4 * (Real.sin x - x * Real.cos x) / x ^ 3 := by
  let F : ℝ → ℝ := fun t ↦
    (1 - t ^ 2) * Real.sin (x * t) / x -
      2 * t * Real.cos (x * t) / x ^ 2 +
      2 * Real.sin (x * t) / x ^ 3
  have hF (t : ℝ) :
      HasDerivAt F ((1 - t ^ 2) * Real.cos (x * t)) t := by
    have hsin : HasDerivAt (fun u : ℝ ↦ Real.sin (x * u))
        (Real.cos (x * t) * x) t := by
      convert ((hasDerivAt_id t).const_mul x).sin using 1 <;> simp
    have hcos : HasDerivAt (fun u : ℝ ↦ Real.cos (x * u))
        (-Real.sin (x * t) * x) t := by
      convert ((hasDerivAt_id t).const_mul x).cos using 1 <;> simp
    dsimp [F]
    have hraw := ((((hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2)).mul hsin).div_const x
      |>.sub ((((hasDerivAt_const t 2).mul (hasDerivAt_id t)).mul hcos).div_const (x ^ 2))
      |>.add (((hasDerivAt_const t 2).mul hsin).div_const (x ^ 3)))
    convert hraw using 1
    all_goals try rfl
    · field_simp
      simp only [id_eq, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hF t)]
  · dsimp [F]
    simp only [one_pow, neg_sq, mul_one, mul_neg, Real.sin_neg, Real.cos_neg]
    grind
  · exact (by fun_prop : Continuous (fun t : ℝ ↦
      (1 - t ^ 2) * Real.cos (x * t))).intervalIntegrable _ _

theorem tartarAmplitude_eq_cosineTransform (x : ℝ) :
    Tartar.amplitude x = (3 / 4 : ℝ) * ∫ t : ℝ, Tartar.weight t * Real.cos (x * t) := by
  by_cases hx : x = 0
  · subst x
    simp [integral_tartarWeight]
  · rw [tartarWeight_eq_indicator]
    have hind :
        (fun t : ℝ ↦
          (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * Real.cos (x * t)) =
        (Set.Icc (-1 : ℝ) 1).indicator
          (fun t ↦ (1 - t ^ 2) * Real.cos (x * t)) := by
      funext t
      exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
        (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ Real.cos (x * u))).symm
    rw [hind]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral_one_sub_sq_mul_cos hx, tartarAmplitude_eq_of_ne hx]
    grind

theorem tartarWeight_mul_cos_integrable (x : ℝ) :
    Integrable (fun t : ℝ ↦ Tartar.weight t * Real.cos (x * t)) := by
  apply tartarWeight_integrable.mul_bdd
  · exact (by fun_prop : Continuous (fun t : ℝ ↦ Real.cos (x * t))).aestronglyMeasurable
  · filter_upwards [] with t
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (x * t)

theorem norm_integral_tartarWeight_mul_cos_le (x : ℝ) :
    ‖∫ t : ℝ, Tartar.weight t * Real.cos (x * t)‖ ≤ 4 / 3 := by
  calc
    ‖∫ t : ℝ, Tartar.weight t * Real.cos (x * t)‖
        ≤ ∫ t : ℝ, Tartar.weight t :=
      norm_integral_le_of_norm_le tartarWeight_integrable <| .of_forall fun t ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tartarWeight_nonneg t)]
        exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (tartarWeight_nonneg t)).trans_eq
          (mul_one _)
    _ = 4 / 3 := integral_tartarWeight

theorem abs_tartarAmplitude_le_one (x : ℝ) : |Tartar.amplitude x| ≤ 1 := by
  rw [tartarAmplitude_eq_cosineTransform, abs_mul]
  have h := norm_integral_tartarWeight_mul_cos_le x
  rw [Real.norm_eq_abs] at h
  norm_num
  nlinarith

theorem tartarTestFunction_le_one (x : ℝ) : Tartar.testFunction x ≤ 1 := by
  rw [Tartar.testFunction]
  have h := (sq_le_sq₀ (abs_nonneg (Tartar.amplitude x)) zero_le_one).mpr
    (abs_tartarAmplitude_le_one x)
  simp_all

end NumberField.Odlyzko
