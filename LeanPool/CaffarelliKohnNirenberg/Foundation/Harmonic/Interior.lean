/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorBasic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Interior

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic


/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section

namespace CKN.Foundation.Heat

theorem newtonianKernel_spatialDeriv_second_size_bound {z : Vec3}
    (hz : z ≠ 0) (i j : Fin 3) :
    |CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j z| ≤
      4 * (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ := by
  have hr : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    exact hz ((WithLp.toLp_eq_zero 2).mp hzero)
  have hq3 : q z ^ (-(3 : ℝ) / 2) =
      (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
    rw [q_eq_vec3Norm_sq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  have hq5 : q z ^ (-(3 : ℝ) / 2 - 1) =
      (vec3EuclideanNorm z) ^ (-(5 : ℝ)) := by
    rw [q_eq_vec3Norm_sq, show (-(3 : ℝ) / 2 - 1) = -(5 / 2 : ℝ) by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  have hi : |z i| ≤ vec3EuclideanNorm z := by
    simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
      vec3EuclideanNorm, pow_two] using CKN.abs_apply_le_vecEuclideanNorm z i
  have hj : |z j| ≤ vec3EuclideanNorm z := by
    simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
      vec3EuclideanNorm, pow_two] using CKN.abs_apply_le_vecEuclideanNorm z j
  have hnorm : ‖z‖ ≤ vec3EuclideanNorm z := by
    simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
      CKN.spaceEuclideanNorm, vec3EuclideanNorm, pow_two] using
      CKN.space_norm_le_euclideanNorm z
  have hbase : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hthird : 0 ≤ (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by positivity
  have hfive : 0 ≤ (vec3EuclideanNorm z) ^ (-(5 : ℝ)) := by positivity
  have hprod_i : |z i| *
      (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ)) * |z i|) ≤
      3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ)) *
        (vec3EuclideanNorm z * vec3EuclideanNorm z) := by
    calc
      |z i| * (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ)) * |z i|) =
          (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ))) *
            (|z i| * |z i|) := by ring
      _ ≤ (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ))) *
          (vec3EuclideanNorm z * vec3EuclideanNorm z) := by
        gcongr
  have hprod_ij : |z i| *
      (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ)) * |z j|) ≤
      3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ)) *
        (vec3EuclideanNorm z * vec3EuclideanNorm z) := by
    calc
      |z i| * (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ)) * |z j|) =
          (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ))) *
            (|z i| * |z j|) := by ring
      _ ≤ (3 * (vec3EuclideanNorm z) ^ (-(5 : ℝ))) *
          (vec3EuclideanNorm z * vec3EuclideanNorm z) := by
        gcongr
  have hcomb : (vec3EuclideanNorm z) ^ (-(5 : ℝ)) *
      (vec3EuclideanNorm z * vec3EuclideanNorm z) =
      (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
    rw [show vec3EuclideanNorm z * vec3EuclideanNorm z =
        (vec3EuclideanNorm z) ^ (2 : ℝ) by rw [Real.rpow_two]; ring]
    rw [← Real.rpow_add hr]
    norm_num
  have hmon : (vec3EuclideanNorm z) ^ (-(3 : ℝ)) ≤
      (‖z‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (vec3EuclideanNorm_nonneg _)]
    have hpow3 : (vec3EuclideanNorm z) ^ (3 : ℝ) =
        (vec3EuclideanNorm z) ^ (3 : ℕ) := by norm_num
    rw [hpow3]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 3
  rw [newtonianKernel_spatialDeriv_second_formula hz i j, hq3, hq5]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, abs_mul, abs_neg, abs_of_nonneg hbase]
    simp only [one_mul]
    calc
      (4 * Real.pi)⁻¹ *
          |vec3EuclideanNorm z ^ (-(3 : ℝ)) +
            z i * (-(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * (2 * z i))| ≤
          (4 * Real.pi)⁻¹ *
            (vec3EuclideanNorm z ^ (-(3 : ℝ)) +
              |z i| * (3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * |z i|)) := by
        apply mul_le_mul_of_nonneg_left _ hbase
        calc
          |vec3EuclideanNorm z ^ (-(3 : ℝ)) +
              z i * (-(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * (2 * z i))| ≤
              |vec3EuclideanNorm z ^ (-(3 : ℝ))| +
                |z i * (-(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * (2 * z i))| :=
            abs_add_le _ _
          _ = vec3EuclideanNorm z ^ (-(3 : ℝ)) +
              |z i| * (3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * |z i|) := by
            rw [abs_of_nonneg hthird, abs_mul]
            congr 1
            rw [show -(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
                (2 * z i) = -(3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * z i) by ring,
              abs_neg, abs_mul, abs_mul,
              abs_of_nonneg (by positivity : 0 ≤ (3 : ℝ)),
              abs_of_nonneg hfive]
      _ ≤ (4 * Real.pi)⁻¹ *
          (vec3EuclideanNorm z ^ (-(3 : ℝ)) +
            3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
              (vec3EuclideanNorm z * vec3EuclideanNorm z)) := by
        apply mul_le_mul_of_nonneg_left _ hbase
        calc
          vec3EuclideanNorm z ^ (-(3 : ℝ)) +
              |z i| * (3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * |z i|) =
              |z i| * (3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * |z i|) +
                vec3EuclideanNorm z ^ (-(3 : ℝ)) := by ring
          _ ≤ 3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
                (vec3EuclideanNorm z * vec3EuclideanNorm z) +
                vec3EuclideanNorm z ^ (-(3 : ℝ)) :=
              add_le_add_left hprod_i _
          _ = vec3EuclideanNorm z ^ (-(3 : ℝ)) +
                3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
                  (vec3EuclideanNorm z * vec3EuclideanNorm z) := by ring
      _ = 4 * (4 * Real.pi)⁻¹ *
          (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
        rw [show 3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
            (vec3EuclideanNorm z * vec3EuclideanNorm z) =
            3 * ((vec3EuclideanNorm z) ^ (-(5 : ℝ)) *
              (vec3EuclideanNorm z * vec3EuclideanNorm z)) by ring,
          hcomb]
        ring
      _ ≤ 4 * (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hmon (by positivity)
  · rw [ite_eq_right hij, zero_mul, zero_add, abs_mul, abs_neg, abs_of_nonneg hbase]
    calc
      (4 * Real.pi)⁻¹ *
          |z i * (-(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
            (2 * z j))| ≤
          (4 * Real.pi)⁻¹ *
            (3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
              (vec3EuclideanNorm z * vec3EuclideanNorm z)) := by
        apply mul_le_mul_of_nonneg_left _ hbase
        calc
          |z i * (-(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
              (2 * z j))| =
              |z i| * (3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * |z j|) := by
            rw [abs_mul]
            congr 1
            rw [show -(3 : ℝ) / 2 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
                (2 * z j) = -(3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) * z j) by ring,
              abs_neg, abs_mul, abs_mul,
              abs_of_nonneg (by positivity : 0 ≤ (3 : ℝ)),
              abs_of_nonneg hfive]
          _ ≤ _ := hprod_ij
      _ ≤ 4 * (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ := by
        rw [show 3 * vec3EuclideanNorm z ^ (-(5 : ℝ)) *
            (vec3EuclideanNorm z * vec3EuclideanNorm z) =
            3 * ((vec3EuclideanNorm z) ^ (-(5 : ℝ)) *
              (vec3EuclideanNorm z * vec3EuclideanNorm z)) by ring,
          hcomb]
        have hc : (4 * Real.pi)⁻¹ * 3 ≤ 4 * (4 * Real.pi)⁻¹ := by
          nlinarith only [show 0 ≤ (4 * Real.pi)⁻¹ by positivity]
        calc
          (4 * Real.pi)⁻¹ * (3 * (vec3EuclideanNorm z) ^ (-(3 : ℝ))) ≤
              (4 * (4 * Real.pi)⁻¹) *
                (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
            rw [show (4 * Real.pi)⁻¹ * (3 *
                (vec3EuclideanNorm z) ^ (-(3 : ℝ))) =
                ((4 * Real.pi)⁻¹ * 3) *
                  (vec3EuclideanNorm z) ^ (-(3 : ℝ)) by ring]
            exact mul_le_mul_of_nonneg_right hc hthird
          _ ≤ 4 * (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hmon (by positivity)

theorem newtonianKernel_spatialDeriv_size_bound {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    |CKN.spatialDeriv newtonianKernel i z| ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  have hdirect := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (hasFDerivAt_newtonianKernel hz).fderiv
  change CKN.spatialDeriv newtonianKernel i z = _ at hdirect
  have hformula : CKN.spatialDeriv newtonianKernel i z =
      -(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2) := by
    convert hdirect using 1
    simp [smul_eq_mul, CKN.basisVec_apply]
    ring_nf
  have hr : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    exact hz ((WithLp.toLp_eq_zero 2).mp hzero)
  have hq : q z = vec3EuclideanNorm z ^ 2 := q_eq_vec3Norm_sq z
  have hqi : q z ^ (-(3 : ℝ) / 2) =
      (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
    rw [hq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  have hcoord : |z i| ≤ vec3EuclideanNorm z := by
    simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
      vec3EuclideanNorm, pow_two] using CKN.abs_apply_le_vecEuclideanNorm z i
  rw [hformula]
  have habs : |-(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)| =
      (4 * Real.pi)⁻¹ * |z i| * q z ^ (-(3 : ℝ) / 2) := by
    rw [show -(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2) =
        -((4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)) by ring,
      abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.rpow_nonneg (q_pos hz).le _)]
  rw [habs, hqi]
  have hpow : vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
      vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    calc
      vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
          vec3EuclideanNorm z ^ (1 : ℝ) *
            vec3EuclideanNorm z ^ (-(3 : ℝ)) := by rw [Real.rpow_one]
      _ = vec3EuclideanNorm z ^ ((1 : ℝ) + (-(3 : ℝ))) := by
        rw [← Real.rpow_add hr]
      _ = vec3EuclideanNorm z ^ (-(2 : ℝ)) := by norm_num
  calc
    (4 * Real.pi)⁻¹ * |z i| * vec3EuclideanNorm z ^ (-(3 : ℝ)) ≤
        (4 * Real.pi)⁻¹ * vec3EuclideanNorm z *
          vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
      gcongr
    _ = (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
      rw [show (4 * Real.pi)⁻¹ * vec3EuclideanNorm z *
          vec3EuclideanNorm z ^ (-(3 : ℝ)) =
          (4 * Real.pi)⁻¹ *
            (vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ))) by ring,
        hpow]
    _ ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-(2 : ℝ)) := by
      have hspace : ‖z‖ ≤ vec3EuclideanNorm z := by
        simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
          CKN.spaceEuclideanNorm, vec3EuclideanNorm, pow_two] using
          CKN.space_norm_le_euclideanNorm z
      have hinv : (vec3EuclideanNorm z) ^ (-(2 : ℝ)) ≤ ‖z‖ ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (vec3EuclideanNorm_nonneg _),
          Real.rpow_neg (norm_nonneg _)]
        apply (inv_le_inv₀ (by positivity) (by positivity)).2
        rw [Real.rpow_two, Real.rpow_two]
        exact (sq_le_sq₀ (norm_nonneg _) (vec3EuclideanNorm_nonneg _)).2 hspace
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
      rw [show (-(2 : ℝ)) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (norm_nonneg _), Real.rpow_two]

theorem spatialDeriv_newtonianKernel_shift_eq_neg
    {x y : Vec3} (hxy : x - y ≠ 0) (i : Fin 3) :
    CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) i y =
      -CKN.spatialDeriv newtonianKernel i (x - y) := by
  rw [spatialDeriv_newtonianKernel_shift hxy]
  have hdirect := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (hasFDerivAt_newtonianKernel hxy).fderiv
  change CKN.spatialDeriv newtonianKernel i (x - y) = _ at hdirect
  rw [hdirect]
  simp [smul_eq_mul, CKN.basisVec_apply]
  ring_nf

theorem spatialDeriv_kernelCutoffDerivative_at_x
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) j x = 0 := by
  have heq : kernelCutoffDerivative x x₀ hρ i =ᶠ[𝓝 x]
      (fun _ : Vec3 => (0 : ℝ)) := by
    exact spatialDeriv_eta_eventually_zero x x₀ hρ hx i |>.mono fun z hz => by
      simp [kernelCutoffDerivative, hz]
  have hfd := heq.fderiv_eq (𝕜 := ℝ)
  change (fderiv ℝ (kernelCutoffDerivative x x₀ hρ i) x)
      (CKN.basisVec j) = 0
  rw [hfd]
  simp

theorem spatialDeriv_kernelCutoffDerivative_of_ne
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (hxy : x - y ≠ 0)
    (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) j y =
      CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) j y *
          CKN.spatialDeriv (eta x₀ hρ) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y := by
  have hsub : HasFDerivAt (fun z : Vec3 => x - z)
      (-ContinuousLinearMap.id ℝ Vec3) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub
      (hasFDerivAt_id (𝕜 := ℝ) y)
  have hkernel := (hasFDerivAt_newtonianKernel hxy).comp y hsub
  have heta0 : ContDiff ℝ (↑(⊤ : ℕ∞)) (eta x₀ hρ) := by
    simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ
  have heta_diff : DifferentiableAt ℝ
      (CKN.spatialDeriv (eta x₀ hρ) i) y :=
    (contDiff_spatialDeriv_two heta0 i).differentiable (by norm_num) y
  have hrule := CKN.spatialDeriv_mul hkernel.differentiableAt heta_diff j
  change CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z) *
      CKN.spatialDeriv (eta x₀ hρ) i z) j y = _
  simpa only [Function.comp_def] using hrule

theorem kernelCutoffDerivative_contDiff_one (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) := by
  exact kernelCutoffDerivative_contDiff x x₀ hρ hx i

theorem kernelCutoffDerivative_hasCompactSupport_global (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) := by
  exact kernelCutoffDerivative_hasCompactSupport x x₀ hρ i

theorem kernelCutoffDerivative_integrable_mul_right_global
    {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y)
      volume := by
  exact kernelCutoffDerivative_integrable_mul_right hh x x₀ hρ hx i

theorem eta_spatialDeriv_contDiff_two_global (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    ContDiff ℝ (2 : ℕ) (spatialDeriv (eta x₀ hρ) i) := by
  exact contDiff_spatialDeriv_two
    (by simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ) i

theorem eta_spatialSecond_continuous_global (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    Continuous (spatialDeriv (spatialDeriv (eta x₀ hρ) i) i) := by
  exact (eta_spatialDeriv_contDiff_two_global x₀ hρ i).continuous_fderiv
    (by norm_num) |>.clm_apply continuous_const

/-- A smooth harmonic function is represented in an inner ball by the
annular terms obtained from the Newtonian representation and a mollified
ball cutoff. -/
theorem smooth_harmonic_annular_representation_on_outer {H : Vec3 → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hHarm : ∀ y ∈ euclideanBall x₀ (3 * ρ / 4),
      CKN.spatialLaplacian H y = 0)
    {x : Vec3} (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) :
    H x =
      (-∫ y : Vec3, newtonianKernel (x - y) *
          (H y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3,
          H y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (eta x₀ hρ) := by
    simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ
  have hηc : HasCompactSupport (eta x₀ hρ) := by
    simpa only [eta] using mollifiedBallCutoff_hasCompactSupport x₀ hρ
  have hηouter : tsupport (eta x₀ hρ) ⊆ euclideanBall x₀ (3 * ρ / 4) := by
    simpa only [eta] using mollifiedBallCutoff_tsupport_subset_outer x₀ hρ
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => eta x₀ hρ y * H y) :=
    hη.mul hH
  have hprodSupport : HasCompactSupport (fun y : Vec3 => eta x₀ hρ y * H y) :=
    hηc.mul_right (f' := H)
  have hxinner : x ∈ euclideanBall x₀ (13 * ρ / 20) := hx
  have hηx : eta x₀ hρ x = 1 := by
    simpa only [eta] using mollifiedBallCutoff_eq_one_on_inner x₀ hρ hxinner
  let Cfun : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) *
      CKN.spatialLaplacian (fun z : Vec3 => eta x₀ hρ z * H z) y
  let Bfun : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) * CKN.spatialGradDot (eta x₀ hρ) H y
  let Afun : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) *
      (H y * CKN.spatialLaplacian (eta x₀ hρ) y)
  have hCcont : Continuous
      (CKN.spatialLaplacian (fun z : Vec3 => eta x₀ hρ z * H z)) :=
    (CKN.contDiff_spatialLaplacian_smooth hprod).continuous
  have hCcompact : HasCompactSupport
      (CKN.spatialLaplacian (fun z : Vec3 => eta x₀ hρ z * H z)) :=
    laplacian_compact_support hprodSupport
  have hCint : Integrable Cfun volume := by
    exact newtonianKernel_mul_compact_integrable hCcont hCcompact x
  have hBi : ∀ i : Fin 3, Integrable (fun y : Vec3 =>
      newtonianKernel (x - y) * CKN.spatialDeriv (eta x₀ hρ) i y *
        CKN.spatialDeriv H i y) volume := by
    intro i
    have hi := kernelCutoffDerivative_integrable_mul_left hH x x₀ hρ hx i
    simpa [kernelCutoffDerivative, eta, mul_assoc, mul_left_comm, mul_comm] using hi
  have hBint : Integrable Bfun volume := by
    have hsum : Integrable (fun y : Vec3 =>
        ∑ i : Fin 3, newtonianKernel (x - y) *
          CKN.spatialDeriv (eta x₀ hρ) i y * CKN.spatialDeriv H i y) volume := by
      simpa only [Fin.sum_univ_three] using
        (integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
          (fun i _hi => hBi i))
    have hrewrite : Bfun = fun y : Vec3 => ∑ i : Fin 3,
        newtonianKernel (x - y) * CKN.spatialDeriv (eta x₀ hρ) i y *
          CKN.spatialDeriv H i y := by
      funext y
      simp only [Bfun, CKN.spatialGradDot, Finset.mul_sum, mul_assoc]
    exact hrewrite ▸ hsum
  have hharm_eta : ∀ y : Vec3,
      (eta x₀ hρ y) * CKN.spatialLaplacian H y = 0 := by
    intro y
    by_cases hy : y ∈ tsupport (eta x₀ hρ)
    · rw [hHarm y (hηouter hy), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hprod_rule : ∀ y : Vec3,
      CKN.spatialLaplacian (fun z : Vec3 => eta x₀ hρ z * H z) y =
        eta x₀ hρ y * CKN.spatialLaplacian H y +
          2 * CKN.spatialGradDot (eta x₀ hρ) H y +
          H y * CKN.spatialLaplacian (eta x₀ hρ) y := by
    intro y
    exact congrFun (CKN.spatialLaplacian_mul_smooth hη hH) y
  have hCeq : Cfun = fun y => Afun y + 2 * Bfun y := by
    funext y
    rw [show Cfun y = newtonianKernel (x - y) *
        CKN.spatialLaplacian (fun z : Vec3 => eta x₀ hρ z * H z) y by rfl,
      hprod_rule y, hharm_eta y]
    simp only [Afun, Bfun]
    ring
  have hAint : Integrable Afun volume := by
    have hdiff := hCint.sub (hBint.const_mul 2)
    apply hdiff.congr
    filter_upwards [] with y
    rw [hCeq]
    simp only [Pi.sub_apply]
    ring
  have hrep : H x = -∫ y : Vec3, Cfun y := by
    have h := newtonian_representation_smooth hprod hprodSupport x
    simpa only [Cfun, hηx, one_mul] using h
  have hBsum : (∫ y : Vec3, Bfun y) =
      ∑ i : Fin 3, ∫ y : Vec3,
        newtonianKernel (x - y) * CKN.spatialDeriv (eta x₀ hρ) i y *
          CKN.spatialDeriv H i y := by
    rw [show Bfun = fun y : Vec3 => ∑ i : Fin 3,
        newtonianKernel (x - y) * CKN.spatialDeriv (eta x₀ hρ) i y *
          CKN.spatialDeriv H i y by
      funext y
      simp only [Bfun, CKN.spatialGradDot, Finset.mul_sum, mul_assoc]]
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _hi => hBi i)]
  have hIBP (i : Fin 3) :
      ∫ y : Vec3, CKN.spatialDeriv H i y *
          kernelCutoffDerivative x x₀ hρ i y =
        -∫ y : Vec3, H y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
    have h := integral_h_mul_kernelCutoffDerivative_spatialDeriv hH x x₀ hρ hx i
    linarith only [h]
  have hsum : (∑ i : Fin 3, ∫ y : Vec3, newtonianKernel (x - y) *
        CKN.spatialDeriv (eta x₀ hρ) i y * CKN.spatialDeriv H i y) =
      -∑ i : Fin 3, ∫ y : Vec3, H y *
        CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
    calc
      (∑ i : Fin 3, ∫ y : Vec3, newtonianKernel (x - y) *
          CKN.spatialDeriv (eta x₀ hρ) i y * CKN.spatialDeriv H i y) =
          ∑ i : Fin 3, -(∫ y : Vec3, H y *
            CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ∫ y : Vec3, newtonianKernel (x - y) *
              CKN.spatialDeriv (eta x₀ hρ) i y * CKN.spatialDeriv H i y =
              ∫ y : Vec3, CKN.spatialDeriv H i y *
                kernelCutoffDerivative x x₀ hρ i y := by
                  congr 1
                  funext y
                  simp [kernelCutoffDerivative, eta, mul_comm]
          _ = -(∫ y : Vec3, H y *
              CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) := hIBP i
      _ = -∑ i : Fin 3, ∫ y : Vec3, H y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
        simp
  calc
    H x = -∫ y : Vec3, Cfun y := hrep
    _ = -((∫ y : Vec3, Afun y) + 2 * (∫ y : Vec3, Bfun y)) := by
      rw [hCeq, integral_add hAint (hBint.const_mul 2), integral_const_mul]
    _ = -((∫ y : Vec3, Afun y) + 2 *
        (∑ i : Fin 3, ∫ y : Vec3, newtonianKernel (x - y) *
          CKN.spatialDeriv (eta x₀ hρ) i y * CKN.spatialDeriv H i y)) := by
      rw [hBsum]
    _ = (-∫ y : Vec3, newtonianKernel (x - y) *
          (H y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3, H y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
      rw [hsum]
      simp only [Afun]
      ring

theorem smooth_harmonic_annular_representation {H : Vec3 → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hHarm : ∀ y ∈ euclideanBall x₀ ρ, CKN.spatialLaplacian H y = 0)
    {x : Vec3} (hx : x ∈ euclideanBall x₀ (ρ / 4)) :
    H x =
      (-∫ y : Vec3, newtonianKernel (x - y) *
          (H y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3,
          H y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
  apply smooth_harmonic_annular_representation_on_outer hH hρ
  · intro y hy
    exact hHarm y (by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      have hnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt
        (x₀ := x₀) (x := y) (by positivity)).mp hy
      nlinarith only [hρ, hnorm])
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (x₀ := x₀) (x := x) (by positivity)).mp hx
    nlinarith only [hρ, hnorm]

end CKN.Foundation.Heat
