/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationBasic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Riesz Second L2 Global Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN.Foundation.Euclidean

lemma pressure_potential_tail_bound
    {G : Vec3 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) {R : ℝ} (hR : 0 < R)
    (hSupp : tsupport G ⊆ Metric.closedBall (0 : Vec3) R)
    {x : Vec3} (hx : 2 * R ≤ ‖x‖) :
    |pressureNewtonianPotential G x| ≤
      (2 * (4 * Real.pi)⁻¹ / ‖x‖) * ∫ y, |G y| := by
  have hconv := hGc.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hG.continuous
      (by
        have hbound : ∀ᵐ z : Vec3, ‖-Foundation.Heat.newtonianKernel z‖ ≤
            (4 * Real.pi)⁻¹ * ‖z‖ ^ (-1 : ℝ) := by
          filter_upwards [Measure.ae_ne volume (0 : Vec3)] with z hz
          have hb := Foundation.Heat.newtonianKernel_size_bound hz
          rw [norm_neg, Real.rpow_neg (norm_nonneg _), Real.rpow_one]
          simpa only [Real.norm_eq_abs] using hb
        have hmeas : Measurable
            (fun z : Vec3 => -Foundation.Heat.newtonianKernel z) := by
          have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
            unfold vec3EuclideanNorm
            fun_prop
          have hk : Measurable
              (Foundation.Heat.newtonianKernel : Vec3 → ℝ) := by
            unfold Foundation.Heat.newtonianKernel
            exact measurable_const.div (measurable_const.mul hnorm)
          exact hk.neg
        refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
          (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
          (by norm_num) hbound hmeas.aestronglyMeasurable) x
  have hprod : Integrable
      (fun y => G y * (-Foundation.Heat.newtonianKernel (x-y))) volume := by
    exact hconv.integrable
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx
    linarith only [hx, hR]
  have hpoint : ∀ y,
      |G y * (-Foundation.Heat.newtonianKernel (x-y))| ≤
        (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := by
    intro y
    by_cases hy : y ∈ tsupport G
    · have hy' := hSupp hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy'
      have hxy : x-y ≠ 0 := by
        intro hzero
        have heq : x = y := sub_eq_zero.mp hzero
        rw [heq] at hx
        linarith only [hx, hy', hR]
      have hdist : ‖x‖ / 2 ≤ ‖x-y‖ := by
        have htri : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
          calc
            ‖x‖ = ‖(x-y) + y‖ := by congr 1; abel
            _ ≤ ‖x-y‖ + ‖y‖ := norm_add_le _ _
        linarith only [htri, hy', hx]
      have hinv : ‖x-y‖⁻¹ ≤ (‖x‖ / 2)⁻¹ := by
        exact (inv_le_inv₀ (by positivity) (by positivity)).2 hdist
      have hkernel' : |Foundation.Heat.newtonianKernel (x-y)| ≤
          (4 * Real.pi)⁻¹ * (‖x‖ / 2)⁻¹ := by
        have hb := Foundation.Heat.newtonianKernel_size_bound hxy
        exact hb.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
      rw [abs_mul, abs_neg]
      calc
        |G y| * |Foundation.Heat.newtonianKernel (x-y)| ≤
            |G y| * ((4 * Real.pi)⁻¹ * (‖x‖ / 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hkernel' (abs_nonneg _)
        _ = (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := by
          have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
          field_simp [hnormx, ne_of_gt Real.pi_pos]
    · have hGzero : G y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hGzero]
  have hright : Integrable
      (fun y => (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y|) volume := by
    exact (hG.continuous.norm.integrable_of_hasCompactSupport hGc.norm).const_mul _
  have hpoint' : ∀ y,
      ‖G y * (-Foundation.Heat.newtonianKernel (x-y))‖ ≤
        (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := by
    intro y
    simpa only [Real.norm_eq_abs] using hpoint y
  have hmono := integral_mono hprod.norm hright hpoint'
  calc
    |pressureNewtonianPotential G x| ≤
        ∫ y, |G y * (-Foundation.Heat.newtonianKernel (x-y))| := by
      unfold pressureNewtonianPotential
      simpa only [mul_comm, Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun y => (-Foundation.Heat.newtonianKernel (x-y)) * G y))
    _ ≤ ∫ y, (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := hmono
    _ = (2 * (4 * Real.pi)⁻¹ / ‖x‖) * ∫ y, |G y| := by
      rw [integral_const_mul]

lemma pressure_potential_compact_radius
    {F : Vec3 → ℝ} (hFc : HasCompactSupport F) :
    ∃ R : ℝ, 0 < R ∧ 1 ≤ R ∧
      tsupport F ⊆ Metric.closedBall (0 : Vec3) R := by
  obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.subset_closedBall (0 : Vec3)
  refine ⟨max R 1, by positivity, le_max_right _ _, ?_⟩
  exact hR.trans (Metric.closedBall_subset_closedBall (by simp))

lemma pressure_potential_deriv_tail_bound
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) {R : ℝ} (hR : 0 < R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R)
    (i : Fin 3) {x : Vec3} (hx : 2 * R ≤ ‖x‖) :
    |spatialDeriv (pressureNewtonianPotential F) i x| ≤
      (2 * (4 * Real.pi)⁻¹ / ‖x‖) * ∫ y, |spatialDeriv F i y| := by
  rw [pressureNewtonianPotential_spatialDeriv_convolution hF hFc i x]
  simpa only [pressureNewtonianPotential, mul_comm] using
    (pressure_potential_tail_bound
      (contDiff_spatialDeriv_smooth hF i) (hFc.fderiv_apply (𝕜 := ℝ) (basisVec i))
      hR ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hSupp) hx)

/-- Error produced by applying the Laplacian to a cutoff Newtonian potential. -/
def cutoffError (F : Vec3 → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (x : Vec3) : ℝ :=
  2 * spatialGradDot (mollifiedBallCutoff 0 hρ) (pressureNewtonianPotential F) x +
    pressureNewtonianPotential F x *
      spatialLaplacian (mollifiedBallCutoff 0 hρ) x

lemma cutoffError_smooth {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffError F hρ) := by
  have hw := pressureNewtonianPotential_smooth hF hFc
  have hχ := mollifiedBallCutoff_smooth (0 : Vec3) hρ
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (spatialGradDot (mollifiedBallCutoff 0 hρ)
        (pressureNewtonianPotential F)) :=
    contDiff_spatialGradDot_smooth hχ hw
  have hlap : ContDiff ℝ (⊤ : ℕ∞)
      (spatialLaplacian (mollifiedBallCutoff 0 hρ)) :=
    contDiff_spatialLaplacian_smooth hχ
  unfold cutoffError
  convert (ContDiff.const_smul (𝕜 := ℝ) 2 hgrad).add (hw.mul hlap) using 1
  funext x
  simp

lemma cutoffError_hasCompactSupport {F : Vec3 → ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (cutoffError F hρ) := by
  refine HasCompactSupport.intro
    (isCompact_euclideanClosedBall (0 : Vec3) (by positivity)) ?_
  intro x hx
  have hnot : x ∉ euclideanBall 0 (3 * ρ / 4) \
      euclideanClosedBall 0 (13 * ρ / 20) := by
    intro hxann
    apply hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    have houter := ((mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity)).1 hxann.1).le
    nlinarith only [houter, hρ]
  obtain ⟨hgrad, hhess⟩ := pressure_cutoff_derivatives_vanish 0 hρ hnot
  have hgrad' : spatialGradDot (mollifiedBallCutoff 0 hρ)
      (pressureNewtonianPotential F) x = 0 := by
    simp only [spatialGradDot]
    rw [Finset.sum_eq_zero]
    intro i hi
    simp [hgrad i]
  have hlap : spatialLaplacian (mollifiedBallCutoff 0 hρ) x = 0 := by
    simp only [spatialLaplacian]
    rw [Finset.sum_eq_zero]
    intro i hi
    exact hhess i i
  simp [cutoffError, hgrad', hlap]

/-- Source and first-derivative mass controlling the tail of the Newtonian potential. -/
def potentialTailSize (F : Vec3 → ℝ) : ℝ :=
  2 * (4 * Real.pi)⁻¹ *
    ((∫ y, |F y|) + ∑ i : Fin 3, ∫ y, |spatialDeriv F i y|)

/-- Coefficient bounding the cutoff error in terms of source tail size. -/
def cutoffErrorConstant (F : Vec3 → ℝ) : ℝ :=
  (60 / 13) * potentialTailSize F *
    (6 * cutoffGradientConstant + 3 * cutoffSecondDerivativeConstant)

lemma potentialTailSize_nonneg {F : Vec3 → ℝ} :
    0 ≤ potentialTailSize F := by
  have hFnonneg : 0 ≤ ∫ y, |F y| := integral_nonneg (fun y => abs_nonneg _)
  have hDnonneg (i : Fin 3) : 0 ≤ ∫ y, |spatialDeriv F i y| :=
    integral_nonneg (fun y => abs_nonneg _)
  dsimp [potentialTailSize]
  positivity

lemma cutoffErrorConstant_nonneg {F : Vec3 → ℝ} :
    0 ≤ cutoffErrorConstant F := by
  dsimp [cutoffErrorConstant]
  have htail := potentialTailSize_nonneg (F := F)
  let h₁ : (0 : ℝ) < 1 := by norm_num
  have hgrad' := mollifiedBallCutoff_gradient_bound (0 : Vec3)
    h₁ (0 : Vec3)
  have hgrad : 0 ≤ cutoffGradientConstant := by
    have hn := vecEuclideanNorm_nonneg
      (classicalGradient (mollifiedBallCutoff (0 : Vec3) h₁) 0)
    simpa using le_trans hn hgrad'
  have hsecond' := mollifiedBallCutoff_second_derivative_bound (0 : Vec3)
    h₁ (0 : Vec3)
  have hsecond : 0 ≤ cutoffSecondDerivativeConstant := by
    have hn := norm_nonneg
      (fderiv ℝ (classicalGradient (mollifiedBallCutoff (0 : Vec3) h₁)) 0)
    simpa using le_trans hn hsecond'
  positivity

end CKN.Foundation.Euclidean
