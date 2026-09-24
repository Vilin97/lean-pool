/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorDisplayBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallMemLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# The rescaled `L¹` Poincaré display

The scale-invariant `L^{3/2}` Poincaré inequality gives the `L¹` display after
Hölder on the ball and comparison of the differential norm with the Euclidean
norm of the gradient.  These steps contribute respectively
`(4π/3)^(1/3) r` and `√3` to the constant.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Heat
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private theorem sum_abs_le_sqrt_three_vec3EuclideanNorm (v : Vec3) :
    (∑ i : Fin 3, |v i|) ≤ Real.sqrt 3 * vec3EuclideanNorm v := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
    (fun _ : Fin 3 => (1 : ℝ)) (fun i : Fin 3 => |v i|)
  calc
    ∑ i : Fin 3, |v i| = ∑ i : Fin 3, (1 : ℝ) * |v i| := by simp
    _ ≤ Real.sqrt (∑ i : Fin 3, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ i : Fin 3, |v i| ^ 2) := hcs
    _ = Real.sqrt 3 * vec3EuclideanNorm v := by
      rw [show (∑ i : Fin 3, (1 : ℝ) ^ 2) = 3 by norm_num]
      congr 2
      exact Finset.sum_congr rfl (fun i _ => sq_abs _)

private theorem fderiv_norm_le_sqrt_three_classicalGradient
    {g : Vec3 → ℝ} (x : Vec3) :
    ‖fderiv ℝ g x‖ ≤ Real.sqrt 3 * vec3EuclideanNorm (classicalGradient g x) := by
  rw [opNorm_eq_sum_abs_basis]
  exact sum_abs_le_sqrt_three_vec3EuclideanNorm (classicalGradient g x)

/-- The rescaled `L¹` Poincaré display on every Euclidean ball, with the
correct absolute constant
`(4π/3)^(1/3) √3 · poincareSobolevL1Constant.toReal`. -/
theorem poincareSobolevL1_ball_of_unit
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) (g : Vec3 → ℝ)
    (hg : ContDiff ℝ 1 g) :
    (∫ x in euclideanBall x₀ r,
      |g x - ⨍ y in euclideanBall x₀ r, g y|) ≤
      ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * Real.sqrt 3 *
        poincareSobolevL1Constant.toReal) * r *
        ∫ x in euclideanBall x₀ r,
          vec3EuclideanNorm (classicalGradient g x) := by
  let B : Set Vec3 := euclideanBall x₀ r
  let μ : Measure Vec3 := volume.restrict B
  let f : Vec3 → ℝ := fun x => g x - average μ g
  have hBvol : volume B < ∞ := by
    change volume (euclideanBall x₀ r) < ∞
    rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq]
    finiteness
  let _ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, Measure.restrict_apply_univ] using hBvol
  have hfcont : Continuous f := hg.continuous.sub continuous_const
  have hfmem : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    exact memLp_euclideanBall_of_continuous hr hfcont (ENNReal.ofReal (3 / 2 : ℝ))
  have hone : MemLp (fun _ : Vec3 => (1 : ℝ)) (ENNReal.ofReal (3 : ℝ)) μ :=
    memLp_const 1
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq hpq hfmem hone
  have hconst :
      (∫ x, ‖(1 : ℝ)‖ ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) =
        (volume B).toReal ^ (1 / 3 : ℝ) := by
    rw [integral_const, Measure.real_def]
    simp only [Real.norm_eq_abs, abs_one]
    have hμuniv : μ Set.univ = volume B := by
      change (volume.restrict B) Set.univ = volume B
      exact Measure.restrict_apply_univ B
    rw [hμuniv]
    norm_num
  have hholder' :
      (∫ x in B, |f x| ∂volume) ≤
        (∫ x in B, |f x| ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) *
          (volume B).toReal ^ (1 / 3 : ℝ) := by
    simpa [μ, Real.norm_eq_abs, Measure.real_def, hconst] using hholder
  have hP :
      (∫ x in B, |f x| ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1Constant.toReal *
          ∫ x in B, ‖fderiv ℝ g x‖ ∂volume := by
    simpa [integralAverage, B, f, μ] using poincareSobolevL1_ball x₀ hr g hg
  have hGcont : Continuous fun x : Vec3 => ‖fderiv ℝ g x‖ :=
    (hg.continuous_fderiv (by norm_num)).norm
  have hGint : Integrable (fun x : Vec3 => ‖fderiv ℝ g x‖)
      (volume.restrict B) := by
    exact memLp_one_iff_integrable.1
      (memLp_euclideanBall_of_continuous hr hGcont 1)
  have hEcont : Continuous fun x : Vec3 =>
      vec3EuclideanNorm (classicalGradient g x) := by
    have hc : Continuous fun x : Vec3 => classicalGradient g x := by
      apply continuous_pi
      intro i
      exact (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp hc
  have hEint : Integrable
      (fun x : Vec3 => vec3EuclideanNorm (classicalGradient g x))
      (volume.restrict B) := by
    exact memLp_one_iff_integrable.1
      (memLp_euclideanBall_of_continuous hr hEcont 1)
  have hGle :
      (∫ x in B, ‖fderiv ℝ g x‖ ∂volume) ≤
        Real.sqrt 3 * ∫ x in B,
          vec3EuclideanNorm (classicalGradient g x) ∂volume := by
    rw [← integral_const_mul]
    exact integral_mono hGint (hEint.const_mul (Real.sqrt 3))
      (fun x => fderiv_norm_le_sqrt_three_classicalGradient x)
  have hvol : (volume B).toReal = r ^ 3 * (Real.pi * 4 / 3) := by
    change (volume (euclideanBall x₀ r)).toReal = _
    rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal (by positivity)]
  have hvolroot :
      (volume B).toReal ^ (1 / 3 : ℝ) =
        (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * r := by
    rw [hvol, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast r 3, ← Real.rpow_mul hr.le]
    norm_num
    ring
  have hCnn : 0 ≤ poincareSobolevL1Constant.toReal := ENNReal.toReal_nonneg
  have hVnn : 0 ≤ (volume B).toReal ^ (1 / 3 : ℝ) := by positivity
  have hRight : 0 ≤
      (volume B).toReal ^ (1 / 3 : ℝ) *
        ∫ x in B, vec3EuclideanNorm (classicalGradient g x) ∂volume :=
    mul_nonneg hVnn (integral_nonneg fun x => vec3EuclideanNorm_nonneg _)
  calc
    ∫ x in B, |f x| ∂volume ≤
        (∫ x in B, |f x| ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) *
          (volume B).toReal ^ (1 / 3 : ℝ) := hholder'
    _ ≤ (poincareSobolevL1Constant.toReal *
          ∫ x in B, ‖fderiv ℝ g x‖ ∂volume) *
          (volume B).toReal ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hP hVnn
    _ ≤ (poincareSobolevL1Constant.toReal *
          (Real.sqrt 3 * ∫ x in B,
            vec3EuclideanNorm (classicalGradient g x) ∂volume)) *
          (volume B).toReal ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hGle hCnn) hVnn
    _ = ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * Real.sqrt 3 *
          poincareSobolevL1Constant.toReal) * r *
          ∫ x in B, vec3EuclideanNorm (classicalGradient g x) ∂volume := by
      rw [hvolroot]
      ring
    _ = _ := by
      simp [B]

end CKN
