/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicInterior
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarSobolev
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Scaling the actual Laplacian and harmonic interior estimates on R³. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit
open scoped ContDiff

theorem laplacian_comp_const_smul (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (x : Space) : Δ (fun y => f (a • y)) x = a^2 * Δ f (a • x) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ),
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  rw [iteratedFDeriv_comp_const_smul a (hf.of_le (by simp))]
  simp only [smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Half scale, defined pointwise by `f ((1/2 : ℝ) • x)`. -/
def halfScale (f : Space → ℝ) : Space → ℝ := fun x => f ((1/2 : ℝ) • x)

theorem halfScale_smooth (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (halfScale f) := by
  exact hf.comp (contDiff_id.const_smul (1/2 : ℝ))

theorem halfScale_memLp (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) : MemLp (halfScale f) 2 volume := by
  apply (memLp_two_iff_integrable_sq (halfScale_smooth f hf).continuous.aestronglyMeasurable).2
  exact ((memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).1 hLp).comp_smul
    (R := (1/2 : ℝ)) (by norm_num)

theorem halfScale_energy (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) :
    lpNorm (halfScale f) 2 volume ^ 2 = 8 * lpNorm f 2 volume ^ 2 := by
  rw [lpNorm_sq_eq_integral_sq _ (halfScale_memLp f hf hLp),
    lpNorm_sq_eq_integral_sq _ hLp]
  change (∫ x, f ((1/2 : ℝ) • x) ^ 2) = _
  rw [Measure.integral_comp_smul volume (fun x => f x ^ 2) (1/2 : ℝ)]
  norm_num [Space, smul_eq_mul]

theorem halfScale_harmonic (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hharmonic : ∀ x ∈ Metric.ball 0 (1 / 2 : ℝ), Δ f x = 0) :
    ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ (halfScale f) x = 0 := by
  intro x hx
  change Δ (fun y => f ((1/2 : ℝ) • y)) x = 0
  rw [laplacian_comp_const_smul f hf]
  have hx' : (1/2 : ℝ) • x ∈ Metric.ball (0 : Space) (1/2 : ℝ) := by
    simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (1/2 : ℝ))]
    linarith
  rw [hharmonic _ hx', mul_zero]

/-- Harmonic quarter ball constant, given by `8 * harmonicInteriorConstant ^ 2`. -/
def harmonicQuarterBallConstant : ℝ := 8 * harmonicInteriorConstant ^ 2

theorem harmonicQuarterBallConstant_nonneg : 0 ≤ harmonicQuarterBallConstant := by
  unfold harmonicQuarterBallConstant
  positivity

/-- A squared pointwise bound with room for a compact mollifier near the boundary. -/
theorem harmonic_pointwise_quarterBall_sq (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 / 2 : ℝ), Δ f x = 0)
    (x : Space) (hx : x ∈ Metric.closedBall 0 (1 / 4 : ℝ)) :
    f x ^ 2 ≤ harmonicQuarterBallConstant * lpNorm f 2 volume ^ 2 := by
  have hx' : (2 : ℝ) • x ∈ Metric.closedBall (0 : Space) (1/2 : ℝ) := by
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    linarith
  have H := harmonic_pointwise_halfBall (halfScale f) (halfScale_smooth f hf)
    (halfScale_memLp f hf hLp) (halfScale_harmonic f hf hharmonic) ((2 : ℝ) • x) hx'
  have heval : halfScale f ((2 : ℝ) • x) = f x := by
    simp [halfScale, smul_smul]
  rw [heval] at H
  have H2 := pow_le_pow_left₀ (abs_nonneg (f x)) H 2
  rw [sq_abs, mul_pow, halfScale_energy f hf hLp] at H2
  unfold harmonicQuarterBallConstant
  nlinarith

end EulerMeanHarmonic
