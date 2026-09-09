/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicSmallBall
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section

/-! Actual compact mollification on R³ is smooth and contractive on scalar L². -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit
open scoped ContDiff Convolution

def scalarMollification (φ : ContDiffBump (0 : Space)) (f : Space → ℝ) : Space → ℝ :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem scalarMollification_smooth (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (scalarMollification φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (hf.locallyIntegrable (by norm_num))

/-- The elementary variance inequality for the actual normalized convolution. -/
theorem scalarMollification_sq_le (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume) (x : Space) :
    scalarMollification φ f x ^ 2 ≤ scalarMollification φ (fun y => f y ^ 2) x := by
  let m := scalarMollification φ f x
  have hi : Integrable (fun y => φ.normed volume y * f (x-y)) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous (hf.locallyIntegrable (by norm_num)) x
  have hf2 : Integrable (fun y => f y ^ 2) volume :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hi2 : Integrable (fun y => φ.normed volume y * f (x-y)^2) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous hf2.locallyIntegrable x
  have hi0 := φ.integrable_normed (μ := (volume : Measure Space))
  have H : (∫ y, (2*m) * (φ.normed volume y * f (x-y)) -
      m^2 * φ.normed volume y) ≤ ∫ y, φ.normed volume y * f (x-y)^2 := by
    apply integral_mono ((hi.const_mul (2*m)).sub (hi0.const_mul (m^2))) hi2
    intro y
    change (2*m) * (φ.normed volume y * f (x-y)) -
      m^2 * φ.normed volume y ≤ φ.normed volume y * f (x-y)^2
    have h := mul_nonneg (φ.nonneg_normed (μ := (volume : Measure Space)) y)
      (sq_nonneg (f (x-y)-m))
    nlinarith
  rw [integral_sub (hi.const_mul (2*m)) (hi0.const_mul (m^2)),
    integral_const_mul, integral_const_mul, φ.integral_normed] at H
  have hm : (∫ y, φ.normed volume y * f (x-y)) = m := rfl
  rw [hm] at H
  change m^2 ≤ ∫ y, φ.normed volume y * f (x-y)^2
  nlinarith

theorem scalarMollification_sq_integrable (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => scalarMollification φ f x ^ 2) volume := by
  have hf2 : Integrable (fun y => f y ^ 2) volume :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hc : Integrable (scalarMollification φ (fun y => f y ^ 2)) volume :=
    φ.integrable_normed.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf2
  apply hc.mono' ((scalarMollification_smooth φ f hf).continuous.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖scalarMollification φ f x ^ 2‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scalarMollification φ f x))] using
    scalarMollification_sq_le φ f hf x

theorem scalarMollification_memLp (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume) :
    MemLp (scalarMollification φ f) 2 volume :=
  (memLp_two_iff_integrable_sq
    (scalarMollification_smooth φ f hf).continuous.aestronglyMeasurable).2
    (scalarMollification_sq_integrable φ f hf)

theorem scalarMollification_energy_le (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume) :
    lpNorm (scalarMollification φ f) 2 volume ^ 2 ≤ lpNorm f 2 volume ^ 2 := by
  rw [lpNorm_sq_eq_integral_sq _ (scalarMollification_memLp φ f hf),
    lpNorm_sq_eq_integral_sq _ hf]
  have hf2 : Integrable (fun y => f y ^ 2) volume :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  calc
    _ ≤ ∫ x, scalarMollification φ (fun y => f y ^ 2) x :=
      integral_mono (scalarMollification_sq_integrable φ f hf)
        (φ.integrable_normed.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf2)
        (scalarMollification_sq_le φ f hf)
    _ = _ := by
      rw [scalarMollification, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        φ.integrable_normed hf2, φ.integral_normed]
      simp only [ContinuousLinearMap.lsmul_apply, one_smul]

theorem scalarMollification_norm_le (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume) :
    lpNorm (scalarMollification φ f) 2 volume ≤ lpNorm f 2 volume :=
  (sq_le_sq₀ lpNorm_nonneg lpNorm_nonneg).1 (scalarMollification_energy_le φ f hf)

end EulerMeanHarmonic
