/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Interior Estimates Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

private lemma basisVec_norm (i : Fin 3) : ‖CKN.basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · rw [Pi.norm_def]
    change (↑(Finset.univ.sup (fun b => ‖CKN.basisVec i b‖₊) : NNReal) : ℝ) ≤
      ↑(1 : NNReal)
    exact_mod_cast (Finset.sup_le fun j hj => by
      by_cases h : j = i
      · subst h
        simp only [CKN.basisVec_apply]
        simp
      · simp only [CKN.basisVec_apply]
        simp [h])
  · have hi' : ‖CKN.basisVec i i‖ ≤ ‖CKN.basisVec i‖ :=
      norm_le_pi_norm _ _
    simpa [CKN.basisVec] using hi'

private lemma eta_gradient_bound (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i : Fin 3) :
    |CKN.spatialDeriv (eta x₀ hρ) i y| ≤ cutoffGradientConstant / ρ := by
  have hg := mollifiedBallCutoff_gradient_bound x₀ hρ y
  have hi := CKN.abs_apply_le_vecEuclideanNorm
    (classicalGradient (mollifiedBallCutoff x₀ hρ) y) i
  have hle := hi.trans hg
  simpa [eta, spatialDeriv, classicalGradient, classicalGradient_apply,
    CKN.basisVec_apply] using hle

private lemma eta_second_derivative_bound (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i j : Fin 3) :
    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have hgrad_diff : DifferentiableAt ℝ
      (classicalGradient (mollifiedBallCutoff x₀ hρ)) y := by
    apply differentiableAt_pi.mpr
    intro k
    change DifferentiableAt ℝ
      (CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) k) y
    exact (CKN.contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) k).differentiable (by norm_num) y
  have hh := mollifiedBallCutoff_second_derivative_bound x₀ hρ y
  have hi := ContinuousLinearMap.le_opNorm
    (fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
    (CKN.basisVec j)
  have hi' : ‖(fderiv ℝ (classicalGradient
      (mollifiedBallCutoff x₀ hρ)) y) (CKN.basisVec j)‖ ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
    calc
      ‖(fderiv ℝ (classicalGradient
          (mollifiedBallCutoff x₀ hρ)) y) (CKN.basisVec j)‖ ≤
          ‖fderiv ℝ (classicalGradient
            (mollifiedBallCutoff x₀ hρ)) y‖ * ‖CKN.basisVec j‖ := hi
      _ = ‖fderiv ℝ (classicalGradient
            (mollifiedBallCutoff x₀ hρ)) y‖ := by rw [basisVec_norm, mul_one]
      _ ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := hh
  have hcoord : (fun z : Vec3 =>
      classicalGradient (mollifiedBallCutoff x₀ hρ) z i) =
      CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i := by
    rfl
  have hcoordfd := congrArg (fun g : Vec3 → ℝ => fderiv ℝ g y) hcoord
  have hcoordapply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec j)) hcoordfd
  have hfdapply := fderiv_apply hgrad_diff i
  have hcoord_le :
      |(fderiv ℝ (fun z : Vec3 =>
          classicalGradient (mollifiedBallCutoff x₀ hρ) z i) y)
          (CKN.basisVec j)| ≤
        ‖(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
          (CKN.basisVec j)‖ := by
    rw [hfdapply]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Real.norm_eq_abs] using
      (norm_le_pi_norm
        ((fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
          (CKN.basisVec j)) i)
  have hi'' : |CKN.spatialDeriv (CKN.spatialDeriv
      (mollifiedBallCutoff x₀ hρ) i) j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
    change |(fderiv ℝ (CKN.spatialDeriv
      (mollifiedBallCutoff x₀ hρ) i) y) (CKN.basisVec j)| ≤ _
    rw [← hcoordapply]
    exact hcoord_le.trans hi'
  simpa [eta] using hi''

lemma eta_spatialDeriv_bound_global (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i : Fin 3) :
    |CKN.spatialDeriv (eta x₀ hρ) i y| ≤ cutoffGradientConstant / ρ :=
  eta_gradient_bound x₀ hρ y i

lemma eta_spatialSecond_bound_global (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i j : Fin 3) :
    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 :=
  eta_second_derivative_bound x₀ hρ y i j

/-- Annulus containing the derivatives of the interior harmonic cutoff. -/
def cutoffAnnulus (x₀ : Vec3) (ρ : ℝ) : Set Vec3 :=
  euclideanBall x₀ (3 * ρ / 4) \ euclideanClosedBall x₀ (13 * ρ / 20)

private lemma cutoff_annulus_distance_for_inner_half
    {x x₀ : Vec3} {ρ R : ℝ} (hρ : 0 < ρ) (hR : R = 4 * ρ / 3)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ R) :
    ρ / 10 < vec3EuclideanNorm (x - y) := by
  have hRpos : 0 < R := by rw [hR]; positivity
  have hx' : vec3EuclideanNorm (x - x₀) < ρ / 2 :=
    by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy' : 13 * R / 20 < vec3EuclideanNorm (y - x₀) := by
    have hnot : y ∉ euclideanClosedBall x₀ (13 * R / 20) := hy.2
    by_contra hle
    apply hnot
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact le_of_not_gt (by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hle)
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (x - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x₀)‖ =
          ‖WithLp.toLp 2 ((y - x) + (x - x₀))‖ := by
            congr 1
            ext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
      _ ≤ ‖WithLp.toLp 2 (y - x)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := norm_add_le _ _
      _ = ‖WithLp.toLp 2 (x - y)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := by
            have hneg : y - x = -(x - y) := by
              ext i
              simp only [Pi.neg_apply, Pi.sub_apply]
              ring
            have hnorm : ‖WithLp.toLp 2 (y - x)‖ =
                ‖WithLp.toLp 2 (x - y)‖ := by
              rw [hneg, WithLp.toLp_neg, norm_neg]
            rw [hnorm]
  have hgap : ρ / 10 < vec3EuclideanNorm (x - y) := by
    rw [hR] at hy'
    nlinarith only [hy', htri, hx', hρ]
  exact hgap

lemma cutoff_annulus_norm_distance_for_inner_half
    {x x₀ : Vec3} {ρ R : ℝ} (hρ : 0 < ρ) (hR : R = 4 * ρ / 3)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ R) :
    ρ / 30 < ‖x - y‖ := by
  have hvec := cutoff_annulus_distance_for_inner_half hρ hR hx hy
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
  have hthree' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  nlinarith only [hvec, hthree', hρ]

lemma eta_derivatives_zero_off_cutoff_annulus
    {x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∉ cutoffAnnulus x₀ ρ) (i j : Fin 3) :
    CKN.spatialDeriv (eta x₀ hρ) i y = 0 ∧
      CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y = 0 := by
  have hv := mollifiedBallCutoff_derivatives_vanish_outside_annulus x₀ hρ hy
  have hgrad : CKN.spatialDeriv (eta x₀ hρ) i y = 0 := by
    simpa [eta, spatialDeriv, classicalGradient, classicalGradient_apply,
      CKN.basisVec_apply] using congrArg (fun v : Vec3 => v i) hv.1
  have hcoord : (fun z : Vec3 =>
      classicalGradient (mollifiedBallCutoff x₀ hρ) z i) =
      CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i := by
    rfl
  have hcoordfd := congrArg (fun g : Vec3 → ℝ => fderiv ℝ g y) hcoord
  have hcoordapply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec j)) hcoordfd
  have hfd := congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (CKN.basisVec j)) hv.2
  have hfd_i := congrArg (fun v : Vec3 => v i) hfd
  have hgrad_diff : DifferentiableAt ℝ
      (classicalGradient (mollifiedBallCutoff x₀ hρ)) y := by
    apply differentiableAt_pi.mpr
    intro k
    change DifferentiableAt ℝ
      (CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) k) y
    exact (CKN.contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) k).differentiable (by norm_num) y
  have hfdapply := fderiv_apply hgrad_diff i
  have hsecond : CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y = 0 := by
    change (fderiv ℝ (CKN.spatialDeriv (eta x₀ hρ) i) y)
      (CKN.basisVec j) = 0
    change (fderiv ℝ (CKN.spatialDeriv
      (mollifiedBallCutoff x₀ hρ) i) y) (CKN.basisVec j) = 0
    rw [← hcoordapply]
    rw [hfdapply]
    simpa using hfd_i
  exact ⟨hgrad, hsecond⟩

lemma eta_spatialDeriv_zero_off_annulus
    {x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∉ cutoffAnnulus x₀ ρ) (i : Fin 3) :
    CKN.spatialDeriv (eta x₀ hρ) i y = 0 :=
  (eta_derivatives_zero_off_cutoff_annulus hρ hy i i).1

lemma eta_spatialSecond_zero_off_annulus
    {x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∉ cutoffAnnulus x₀ ρ) (i j : Fin 3) :
    CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y = 0 :=
  (eta_derivatives_zero_off_cutoff_annulus hρ hy i j).2

private lemma kernel_cutoff_value_bound
    {x x₀ : Vec3} {ρ R : ℝ} (hρ : 0 < ρ) (hR : R = 4 * ρ / 3)
    (hRpos : 0 < R)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ R) (i : Fin 3) :
    |kernelCutoffDerivative (ρ := R) x x₀ hRpos i y| ≤
      (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ * (cutoffGradientConstant / R) := by
  have hdist := cutoff_annulus_norm_distance_for_inner_half hρ hR hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  rw [kernelCutoffDerivative]
  rw [abs_mul]
  have hkernel := newtonianKernel_size_bound hxy
  have hinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
  have heta := eta_gradient_bound x₀ hRpos y i
  have hkernel' : |newtonianKernel (x - y)| ≤
      (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ := by
    calc
      |newtonianKernel (x - y)| ≤ (4 * Real.pi)⁻¹ * ‖x - y‖⁻¹ := hkernel
      _ ≤ (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ := by gcongr
  gcongr

private lemma kernel_cutoff_derivative_bound
    {x x₀ : Vec3} {ρ R : ℝ} (hρ : 0 < ρ) (hR : R = 4 * ρ / 3)
    (hRpos : 0 < R)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ R) (i j : Fin 3) :
    |CKN.spatialDeriv (kernelCutoffDerivative (ρ := R) x x₀ hRpos i) j y| ≤
      (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ * (cutoffGradientConstant / R) +
        (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ *
          (cutoffSecondDerivativeConstant / R ^ 2) := by
  have hdist := cutoff_annulus_norm_distance_for_inner_half hρ hR hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  rw [spatialDeriv_kernelCutoffDerivative_of_ne hRpos hxy]
  calc
    |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y *
          CKN.spatialDeriv (eta x₀ hRpos) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta x₀ hRpos) i) j y| ≤
        |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| *
          |CKN.spatialDeriv (eta x₀ hRpos) i y| +
        |newtonianKernel (x - y)| *
          |CKN.spatialDeriv (CKN.spatialDeriv
            (eta x₀ hRpos) i) j y| := by
              calc
                |_ + _| ≤ |_| + |_| := abs_add_le _ _
                _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ *
          (cutoffGradientConstant / R) +
        (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ *
          (cutoffSecondDerivativeConstant / R ^ 2) := by
            have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
            have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 30) ^ 2)⁻¹ := by
              gcongr
            have heta := eta_gradient_bound x₀ hRpos y i
            have hsecond := eta_second_derivative_bound x₀ hRpos y i j
            have hkernel := newtonianKernel_size_bound hxy
            have hdistinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ := by
              exact (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
            have hderiv' :
                |CKN.spatialDeriv newtonianKernel j (x - y)| ≤
                  (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ := by
              exact hderiv.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
            have hkernel' : |newtonianKernel (x - y)| ≤
                (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ := by
              exact hkernel.trans
                (mul_le_mul_of_nonneg_left hdistinv (by positivity))
            rw [show |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| =
                |CKN.spatialDeriv newtonianKernel j (x - y)| by
                  rw [spatialDeriv_newtonianKernel_shift_eq_neg hxy, abs_neg]
                ]
            gcongr

/-- Coefficient for the cutoff contribution to the interior harmonic value bound. -/
noncomputable def harmonicInteriorValueConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 30 * (3 / 4) * cutoffGradientConstant

/-- Coefficient for first-derivative terms in the interior harmonic representation. -/
noncomputable def harmonicInteriorGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 900 * (3 / 4) * cutoffGradientConstant +
    (4 * Real.pi)⁻¹ * 30 * (9 / 16) * cutoffSecondDerivativeConstant

/-- Coefficient for the Laplacian-cutoff source in the harmonic representation. -/
noncomputable def harmonicInteriorSourceConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 30 * (27 / 16) * cutoffSecondDerivativeConstant

/-- Coefficient for the gradient of the Laplacian-cutoff source term. -/
noncomputable def harmonicInteriorSourceGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 900 * (27 / 16) * cutoffSecondDerivativeConstant

/-- Coefficient for spatial differentiation of the harmonic representation kernel. -/
noncomputable def harmonicInteriorKernelXGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 4 * 27000 * (3 / 4) * cutoffGradientConstant +
    (4 * Real.pi)⁻¹ * 900 * (9 / 16) * cutoffSecondDerivativeConstant

private lemma cutoffGradientConstant_nonneg : 0 ≤ cutoffGradientConstant := by
  have h := mollifiedBallCutoff_gradient_bound (0 : Vec3) (ρ := 1) (by norm_num) 0
  have hn := vecEuclideanNorm_nonneg (classicalGradient
    (mollifiedBallCutoff (ρ := 1) (0 : Vec3) (by norm_num)) 0)
  nlinarith only [h, hn]

private lemma cutoffSecondDerivativeConstant_nonneg :
    0 ≤ cutoffSecondDerivativeConstant := by
  have h := mollifiedBallCutoff_second_derivative_bound
    (0 : Vec3) (ρ := 1) (by norm_num) 0
  nlinarith only [h, norm_nonneg
    (fderiv ℝ (classicalGradient
      (mollifiedBallCutoff (ρ := 1) (0 : Vec3) (by norm_num))) 0)]

lemma cutoffGradientConstant_nonneg_global : 0 ≤ cutoffGradientConstant :=
  cutoffGradientConstant_nonneg

lemma cutoffSecondDerivativeConstant_nonneg_global :
    0 ≤ cutoffSecondDerivativeConstant :=
  cutoffSecondDerivativeConstant_nonneg

private lemma harmonicInteriorValueConstant_nonneg :
    0 ≤ harmonicInteriorValueConstant := by
  dsimp [harmonicInteriorValueConstant]
  have hG := cutoffGradientConstant_nonneg
  positivity

lemma harmonicInteriorGradientConstant_nonneg :
    0 ≤ harmonicInteriorGradientConstant := by
  dsimp [harmonicInteriorGradientConstant]
  have hG := cutoffGradientConstant_nonneg
  have hS := cutoffSecondDerivativeConstant_nonneg
  positivity

lemma harmonicInteriorSourceConstant_nonneg :
    0 ≤ harmonicInteriorSourceConstant := by
  dsimp [harmonicInteriorSourceConstant]
  have hS := cutoffSecondDerivativeConstant_nonneg
  positivity

lemma harmonicInteriorSourceGradientConstant_nonneg :
    0 ≤ harmonicInteriorSourceGradientConstant := by
  dsimp [harmonicInteriorSourceGradientConstant]
  have hS := cutoffSecondDerivativeConstant_nonneg
  positivity

lemma harmonicInteriorKernelXGradientConstant_nonneg :
    0 ≤ harmonicInteriorKernelXGradientConstant := by
  dsimp [harmonicInteriorKernelXGradientConstant]
  have hG := cutoffGradientConstant_nonneg
  have hS := cutoffSecondDerivativeConstant_nonneg
  positivity

private lemma kernel_cutoff_value_bound_scaled
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) (i : Fin 3) :
    |kernelCutoffDerivative (ρ := 4 * ρ / 3) x x₀ (by positivity) i y| ≤
      harmonicInteriorValueConstant * (ρ ^ 2)⁻¹ := by
  have hR : (4 * ρ / 3 : ℝ) = 4 * ρ / 3 := rfl
  have hbase := kernel_cutoff_value_bound hρ hR (by positivity) hx hy i
  dsimp [harmonicInteriorValueConstant]
  convert hbase using 1
  field_simp [hρ.ne']

lemma kernel_cutoff_derivative_bound_scaled
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) (i j : Fin 3) :
    |CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) j y| ≤
      harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
  have hR : (4 * ρ / 3 : ℝ) = 4 * ρ / 3 := rfl
  have hbase := kernel_cutoff_derivative_bound hρ hR (by positivity) hx hy i j
  dsimp [harmonicInteriorGradientConstant]
  convert hbase using 1
  field_simp [hρ.ne']
  ring

private lemma kernel_cutoff_value_zero_off_annulus
    {x x₀ : Vec3} {ρ R : ℝ} (_ : 0 < ρ) (_ : R = 4 * ρ / 3)
    (hRpos : 0 < R) (_ : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∉ cutoffAnnulus x₀ R) (i : Fin 3) :
    kernelCutoffDerivative (ρ := R) x x₀ hRpos i y = 0 := by
  have hz := eta_derivatives_zero_off_cutoff_annulus hRpos hy i i
  simp [kernelCutoffDerivative, hz.1]

lemma kernel_cutoff_derivative_zero_off_annulus
    {x x₀ : Vec3} {ρ R : ℝ} (hρ : 0 < ρ) (hR : R = 4 * ρ / 3)
    (hRpos : 0 < R) (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∉ cutoffAnnulus x₀ R) (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative (ρ := R) x x₀ hRpos i) j y = 0 := by
  by_cases hxy : x - y = 0
  · have hxinner : x ∈ euclideanBall x₀ (13 * R / 20) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      have hxnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by positivity)).1 hx
      have hxnorm' : vec3EuclideanNorm (x - x₀) < ρ / 2 := by
        simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
          using hxnorm
      rw [hR]
      have hmiddle : (ρ / 2 : ℝ) < 13 * (4 * ρ / 3) / 20 := by
        nlinarith only [hρ]
      exact hxnorm.trans hmiddle
    have hzero := spatialDeriv_kernelCutoffDerivative_at_x
      (ρ := R) hRpos hxinner i j
    have hxy' : x = y := sub_eq_zero.mp hxy
    subst y
    exact hzero
  · rw [spatialDeriv_kernelCutoffDerivative_of_ne hRpos hxy]
    have hz := eta_derivatives_zero_off_cutoff_annulus hRpos hy i j
    simp [hz.1, hz.2]

private lemma holder_three_halves_three
    {μ : Measure Vec3} {f g : Vec3 → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hg : MemLp g (ENNReal.ofReal (3 : ℝ)) μ) :
    ∫ x, f x * g x ∂μ ≤
      (eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal *
        (eLpNorm g (ENNReal.ofReal (3 : ℝ)) μ).toReal := by
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (.of_forall hf_nonneg) (.of_forall hg_nonneg) hf hg
  have hf_eq := hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ ∞)
  have hg_eq := hg.eLpNorm_eq_integral_rpow_norm
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ ∞)
  have hfp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
    norm_num
  have hgp : (ENNReal.ofReal (3 : ℝ)).toReal = (3 : ℝ) := by
    norm_num
  rw [hfp] at hf_eq
  rw [hgp] at hg_eq
  have hfa : 0 ≤ (∫ x, ‖f x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (3 / 2 : ℝ)⁻¹ := by
    positivity
  have hga : 0 ≤ (∫ x, ‖g x‖ ^ (3 : ℝ) ∂μ) ^ (3 : ℝ)⁻¹ := by
    positivity
  rw [hf_eq, hg_eq, ENNReal.toReal_ofReal hfa, ENNReal.toReal_ofReal hga]
  have hfnorm : (fun x => ‖f x‖) = f := by
    funext x
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
  have hgnorm : (fun x => ‖g x‖) = g := by
    funext x
    simp only [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg x)]
  simp_rw [show ∀ x, ‖f x‖ = f x from fun x => congrFun hfnorm x]
  simp_rw [show ∀ x, ‖g x‖ = g x from fun x => congrFun hgnorm x]
  simpa only [hfp, hgp, one_div] using h

private lemma eta_laplacian_bound
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (y : Vec3) :
    |CKN.spatialLaplacian (eta x₀ hR) y| ≤
      3 * cutoffSecondDerivativeConstant / R ^ 2 := by
  rw [CKN.spatialLaplacian, Fin.sum_univ_three]
  calc
    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 0) 0 y +
        CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 1) 1 y +
        CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 2) 2 y| ≤
        |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 0) 0 y| +
            |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 1) 1 y| +
          |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 2) 2 y| := by
            calc
              |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 0) 0 y +
                    CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 1) 1 y +
                    CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 2) 2 y| ≤
                  |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 0) 0 y +
                    CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 1) 1 y| +
                    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 2) 2 y| :=
                abs_add_le _ _
              _ ≤
                  (|CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 0) 0 y| +
                    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 1) 1 y|) +
                    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hR) 2) 2 y| :=
                add_le_add_left (abs_add_le _ _) _
              _ = _ := by ring
    _ ≤ 3 * cutoffSecondDerivativeConstant / R ^ 2 := by
      calc
        _ ≤ cutoffSecondDerivativeConstant / R ^ 2 +
            cutoffSecondDerivativeConstant / R ^ 2 +
              cutoffSecondDerivativeConstant / R ^ 2 := by
          exact add_le_add
            (add_le_add (eta_second_derivative_bound x₀ hR y 0 0)
              (eta_second_derivative_bound x₀ hR y 1 1))
            (eta_second_derivative_bound x₀ hR y 2 2)
        _ = 3 * cutoffSecondDerivativeConstant / R ^ 2 := by ring

lemma eta_laplacian_bound_global
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (y : Vec3) :
    |CKN.spatialLaplacian (eta x₀ hR) y| ≤
      3 * cutoffSecondDerivativeConstant / R ^ 2 :=
  eta_laplacian_bound x₀ hR y

lemma eta_laplacian_zero_off_annulus
    {x₀ y : Vec3} {R : ℝ} (hR : 0 < R)
    (hy : y ∉ cutoffAnnulus x₀ R) :
    CKN.spatialLaplacian (eta x₀ hR) y = 0 := by
  have h0 := eta_derivatives_zero_off_cutoff_annulus hR hy
    (0 : Fin 3) (0 : Fin 3)
  have h1 := eta_derivatives_zero_off_cutoff_annulus hR hy
    (1 : Fin 3) (1 : Fin 3)
  have h2 := eta_derivatives_zero_off_cutoff_annulus hR hy
    (2 : Fin 3) (2 : Fin 3)
  rw [CKN.spatialLaplacian, Fin.sum_univ_three]
  simp [h0.2, h1.2, h2.2]

lemma source_kernel_bound_scaled
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) :
    |newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y| ≤
      harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
  have hdist := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  have hkernel := newtonianKernel_size_bound hxy
  have hdistinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
  have hsource := eta_laplacian_bound x₀ (R := 4 * ρ / 3) (by positivity) y
  rw [abs_mul]
  have hkernel' : |newtonianKernel (x - y)| ≤
      (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ := by
    exact hkernel.trans (mul_le_mul_of_nonneg_left hdistinv (by positivity))
  calc
    |newtonianKernel (x - y)| *
        |CKN.spatialLaplacian
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y| ≤
        ((4 * Real.pi)⁻¹ * (ρ / 30)⁻¹) *
          (3 * cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
            gcongr
    _ = harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
      dsimp [harmonicInteriorSourceConstant]
      field_simp [hρ.ne']
      ring

lemma source_kernel_spatialDeriv_bound_scaled
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) (j : Fin 3) :
    |CKN.spatialDeriv newtonianKernel j (x - y) *
        CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y| ≤
      harmonicInteriorSourceGradientConstant * (ρ ^ 4)⁻¹ := by
  have hdist := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
  have hdistinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 30) ^ 2)⁻¹ := by
    gcongr
  have hderiv' : |CKN.spatialDeriv newtonianKernel j (x - y)| ≤
      (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ := by
    exact hderiv.trans (mul_le_mul_of_nonneg_left hdistinv (by positivity))
  have hsource := eta_laplacian_bound x₀ (R := 4 * ρ / 3) (by positivity) y
  rw [abs_mul]
  calc
    |CKN.spatialDeriv newtonianKernel j (x - y)| *
        |CKN.spatialLaplacian
          (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y| ≤
        ((4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹) *
          (3 * cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
            gcongr
    _ = harmonicInteriorSourceGradientConstant * (ρ ^ 4)⁻¹ := by
      dsimp [harmonicInteriorSourceGradientConstant]
      field_simp [hρ.ne']
      ring

lemma kernel_cutoff_x_derivative_bound_scaled
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3))
    (i j : Fin 3) :
    |-CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j (x - y) *
          CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        CKN.spatialDeriv newtonianKernel j (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y| ≤
      harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹ := by
  have hdist := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  have hdist1 : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
  have hdist2 : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 30) ^ 2)⁻¹ := by
    gcongr
  have hdist3 : (‖x - y‖ ^ 3)⁻¹ ≤ ((ρ / 30) ^ 3)⁻¹ := by
    gcongr
  have hess := newtonianKernel_spatialDeriv_second_size_bound hxy i j
  have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
  have hess' : |CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j
      (x - y)| ≤ 4 * (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 3)⁻¹ := by
    exact hess.trans (mul_le_mul_of_nonneg_left hdist3 (by positivity))
  have hderiv' : |CKN.spatialDeriv newtonianKernel j (x - y)| ≤
      (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ := by
    exact hderiv.trans (mul_le_mul_of_nonneg_left hdist2 (by positivity))
  have heta := eta_gradient_bound x₀ (ρ := 4 * ρ / 3) (by positivity) y i
  have hsecond := eta_second_derivative_bound x₀ (ρ := 4 * ρ / 3)
    (by positivity) y i i
  calc
    |-CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j (x - y) *
          CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        CKN.spatialDeriv newtonianKernel j (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y| ≤
        |-CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j (x - y) *
          CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y| +
        |CKN.spatialDeriv newtonianKernel j (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y| := abs_add_le _ _
    _ = |CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j (x - y)| *
          |CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y| +
        |CKN.spatialDeriv newtonianKernel j (x - y)| *
          |CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y| := by
              simp only [abs_mul, abs_neg]
    _ ≤
        (4 * (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 3)⁻¹) *
            (cutoffGradientConstant / (4 * ρ / 3)) +
          ((4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹) *
            (cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
              gcongr
    _ = harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹ := by
      dsimp [harmonicInteriorKernelXGradientConstant]
      field_simp [hρ.ne']
      ring

private lemma euclideanBall_eq_vec3Ball {x₀ : Vec3} {R : ℝ} (hR : 0 < R) :
    euclideanBall x₀ R = vec3Ball x₀ R := by
  ext x
  change x ∈ euclideanBall x₀ R ↔ vec3EuclideanNorm (x - x₀) < R
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hR)

lemma cutoffAnnulus_measurable {x₀ : Vec3} {R : ℝ} (_ : 0 < R) :
    MeasurableSet (cutoffAnnulus x₀ R) := by
  have hopen : IsOpen (euclideanBall x₀ (3 * R / 4)) := by
    apply isOpen_lt
    · exact (contDiff_euclideanSqDist_left x₀).continuous
    · fun_prop
  exact hopen.measurableSet.diff
    (isClosed_euclideanClosedBall x₀ (13 * R / 20)).measurableSet

lemma cutoffAnnulus_subset_outer_ball
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    cutoffAnnulus x₀ (4 * ρ / 3) ⊆ euclideanBall x₀ ρ := by
  intro y hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy.1
  have hy'' : vecEuclideanNorm (y - x₀) < ρ := by
    rw [show 3 * (4 * ρ / 3) / 4 = ρ by ring] at hy'
    exact hy'
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hy''

lemma memLp_of_continuousOn_bound
    {s : Set Vec3} (hs : MeasurableSet s) {f : Vec3 → ℝ}
    (hf : ContinuousOn f s) (C : ℝ)
    (hbound : ∀ x ∈ s, |f x| ≤ C) (p : ENNReal)
    [IsFiniteMeasure (volume.restrict s)] :
    MemLp f p (volume.restrict s) := by
  refine MemLp.of_bound (hf.aestronglyMeasurable hs) C ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  simpa only [Real.norm_eq_abs] using hbound x hx

lemma lpNorm_bound_on
    {s : Set Vec3} (hs : MeasurableSet s)
    {f : Vec3 → ℝ} {p : ENNReal}
    [IsFiniteMeasure (volume.restrict s)]
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ s, ‖f x‖ ≤ C) :
    lpNorm f p (volume.restrict s) ≤
      C * (volume s).toReal ^ p.toReal⁻¹ := by
  let fi : Vec3 → ℝ := s.indicator f
  have hfi : eLpNorm f p (volume.restrict s) = eLpNorm fi p
      (volume.restrict s) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [fi, hx]
  have hconst : MemLp (fun _ : Vec3 => C) p (volume.restrict s) := by
    refine MemLp.of_bound (continuous_const.aestronglyMeasurable) C ?_
    filter_upwards [] with x
    simp [Real.norm_eq_abs, abs_of_nonneg hC]
  have hmono : lpNorm fi p (volume.restrict s) ≤
      lpNorm (fun _ : Vec3 => C) p (volume.restrict s) := by
    apply lpNorm_mono_real hconst
    intro x
    by_cases hx : x ∈ s
    · simp only [hx, indicator_of_mem, Real.norm_eq_abs, fi]
      exact hbound x hx
    · simp only [hx, not_false_eq_true, indicator_of_notMem, norm_zero, fi]
      exact hC
  calc
    lpNorm f p (volume.restrict s) = lpNorm fi p (volume.restrict s) := by
      rw [← MeasureTheory.toReal_eLpNorm, hfi, MeasureTheory.toReal_eLpNorm]
    _ ≤ lpNorm (fun _ : Vec3 => C) p (volume.restrict s) := hmono
    _ = C * (volume s).toReal ^ p.toReal⁻¹ := by
      rw [lpNorm_const' hp0 hptop C]
      simp only [Measure.restrict_apply_univ, Measure.real]
      rw [Real.norm_eq_abs, abs_of_nonneg hC]

lemma volume_root_bound
    {s : Set Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hs : s ⊆ euclideanBall x₀ ρ) :
    (volume s).toReal ^ (1 / (3 : ℝ)) ≤
      ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) := by
  have hball : euclideanBall x₀ ρ = vec3Ball x₀ ρ :=
    euclideanBall_eq_vec3Ball hρ
  have hvol : volume s ≤ volume (vec3Ball x₀ ρ) :=
    measure_mono (hball ▸ hs)
  have hvol' : (volume s).toReal ≤ (volume (vec3Ball x₀ ρ)).toReal := by
    exact ENNReal.toReal_mono (by
      rw [volume_vec3Ball_eq]
      finiteness) hvol
  rw [volume_vec3Ball_eq] at hvol'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_pow] at hvol'
  have hnonneg : 0 ≤ Real.pi * 4 / 3 := by positivity
  rw [ENNReal.toReal_ofReal hnonneg] at hvol'
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ (volume s).toReal)
    hvol' (by positivity : 0 ≤ (1 / (3 : ℝ)))
  calc
    (volume s).toReal ^ (1 / (3 : ℝ)) ≤
        (ρ ^ 3 * (Real.pi * 4 / 3)) ^ (1 / (3 : ℝ)) := hrpow
    _ = ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hnonneg]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num

lemma integral_mul_memLp_bound_on
    {A : Set Vec3} (hAmeas : MeasurableSet A)
    {f k : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A))
    (hk : MemLp k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A))
    (hk_zero : ∀ y, y ∉ A → k y = 0) :
    |∫ y, f y * k y| ≤
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
        lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
  have hholder := holder_three_halves_three
    (μ := volume.restrict A) (fun y => abs_nonneg _) (fun y => abs_nonneg _)
    hf.norm hk.norm
  have hfnorm : lpNorm (fun y => |f y|)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) =
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) := by
    rw [show (fun y => |f y|) = (fun y => ‖f y‖) by
      funext y; simp only [Real.norm_eq_abs],
      MeasureTheory.lpNorm_norm hf.aestronglyMeasurable]
  have hknorm : lpNorm (fun y => |k y|)
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) =
      lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
    rw [show (fun y => |k y|) = (fun y => ‖k y‖) by
      funext y; simp only [Real.norm_eq_abs],
      MeasureTheory.lpNorm_norm hk.aestronglyMeasurable]
  have hholder' : ∫ y, |f y| * |k y| ∂(volume.restrict A) ≤
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
        lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
    rw [← hfnorm, ← hknorm]
    simpa only [MeasureTheory.toReal_eLpNorm] using hholder
  have heq : (fun y => f y * k y) =
      A.indicator (fun y => f y * k y) := by
    funext y
    by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy, hk_zero y hy]
  rw [heq, integral_indicator hAmeas]
  calc
    |∫ y in A, f y * k y| ≤
        ∫ y in A, |f y * k y| := abs_integral_le_integral_abs
    _ = ∫ y, |f y| * |k y| ∂(volume.restrict A) := by
      congr 1
      funext y
      simp [abs_mul]
    _ ≤ _ := hholder'

end CKN.Foundation.Heat
