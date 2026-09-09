/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-! The scalar R³ H² estimate used for harmonic interior control. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus EulerSobolev
  EulerSmoothSobolev
open scoped ContDiff ENNReal SchwartzMap LineDeriv

theorem partialDerivative_twice (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (x : Space) :
    partialDerivative (partialDerivative f i) i x =
      iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => EuclideanSpace.single i 1) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  rw [iteratedFDeriv_two_apply]
  change (fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x)
    (EuclideanSpace.single i 1) = _
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

theorem complex_eLpNorm_toReal (f : Space → ℝ) (hf : AEStronglyMeasurable f volume) :
    (eLpNorm (fun x => (f x : ℂ)) 2 volume).toReal = lpNorm f 2 volume := by
  have he : eLpNorm (fun x => (f x : ℂ)) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
  rw [he, toReal_eLpNorm hf]

/-- This is the existing Fourier Sobolev estimate applied to the actual scalar
function and its actual twofold coordinate derivatives, with no embedding
estimate supplied as a hypothesis. -/
theorem scalar_pointwise_le_H2 (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : Space) :
    |f x| ≤ embeddingConstant 3 2 (by norm_num) *
      (lpNorm f 2 volume + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin 3, lpNorm (partialDerivative (partialDerivative f i) i) 2 volume) := by
  have hcF : HasCompactSupport (Complex.ofRealCLM ∘ f) :=
    hc.comp_left (g := Complex.ofRealCLM) (by simp)
  have hsF : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ f) := Complex.ofRealCLM.contDiff.comp hf
  let F : 𝓢(Space, ℂ) := hcF.toSchwartzMap hsF
  have hF (y : Space) : F y = (f y : ℂ) := rfl
  have hnorm : ‖F.toLp 2‖ = lpNorm f 2 volume := by
    rw [SchwartzMap.norm_toLp]
    change (eLpNorm (fun y => (f y : ℂ)) 2 volume).toReal = _
    exact complex_eLpNorm_toReal f hf.continuous.aestronglyMeasurable
  have hder (i : Fin 3) (y : Space) :
      pureDerivative 3 2 (EuclideanSpace.single i 1) F y =
        (partialDerivative (partialDerivative f i) i y : ℂ) := by
    rw [pureDerivative, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    change iteratedFDeriv ℝ 2 (Complex.ofRealCLM ∘ f) y
      (fun _ : Fin 2 => EuclideanSpace.single i 1) = _
    rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
    rw [partialDerivative_twice f hf i y]
    rfl
  have hnormDer (i : Fin 3) :
      ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) F).toLp 2‖ =
        lpNorm (partialDerivative (partialDerivative f i) i) 2 volume := by
    rw [SchwartzMap.norm_toLp]
    have heq : (pureDerivative 3 2 (EuclideanSpace.single i 1) F : Space → ℂ) =
        fun y => (partialDerivative (partialDerivative f i) i y : ℂ) := funext (hder i)
    rw [heq]
    exact complex_eLpNorm_toReal _
      (contDiff_partialDerivative _ (contDiff_partialDerivative f hf i)
        i).continuous.aestronglyMeasurable
  have h := pointwise_le_L2_second_derivatives F x
  rw [hnorm, hF] at h
  simp_rw [hnormDer] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

theorem lpNorm_sq_eq_integral_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (f : Space → V)
    (hf : MemLp f 2 volume) : (lpNorm f 2 volume) ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hn : ‖hf.toLp f‖ = lpNorm f 2 volume := by
    rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable]
  rw [← hn, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem lpNorm_sq_eq_integral_sq (f : Space → ℝ) (hf : MemLp f 2 volume) :
    (lpNorm f 2 volume) ^ 2 = ∫ x, f x ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using lpNorm_sq_eq_integral_norm_sq f hf

end EulerMeanHarmonic
