/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable

public import LeanPool.NavierStokesAndEuler.ForMathlib.SobolevThreeDimensional
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! A genuine ordinary-space cutoff-curl dual estimate. All spatial norms and
integrals in this file use Lebesgue measure on Euclidean three-space. -/

@[expose] public section


noncomputable section

namespace EulerMeanCutoffCurl

open MeasureTheory EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff ENNReal NNReal

/-- Curl of a vector-valued field, using the existing coordinate curl. -/
def vectorCurl (f : Space → Space) : Space → Space :=
  curl (fun i x => f x i)

/-- The fixed homogeneous Sobolev constant for dimension three and exponent two. -/
def sobolevConstant : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2

/-- The ordinary homogeneous Sobolev inequality, with no dependence on support size. -/
theorem homogeneous_sobolev (f : Space → Space)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    lpNorm f 6 volume ≤ (sobolevConstant : ℝ) * lpNorm (fderiv ℝ f) 2 volume :=
  by
  have h := NavierStokesAndEuler.SobolevThreeDimensional.toReal_eLpNorm_six_le_of_hasCompactSupport
    (hf.of_le (by simp)) hfc
  simpa only [sobolevConstant,
    NavierStokesAndEuler.SobolevThreeDimensional.sobolevConstant,
    toReal_eLpNorm hf.continuous.aestronglyMeasurable,
    toReal_eLpNorm (hf.continuous_fderiv (by simp)).aestronglyMeasurable] using h

/-- A three-vector's Euclidean norm is at most the sum of its component norms. -/
theorem norm_le_sum_coordinates (v : Space) : ‖v‖ ≤ ∑ i : Fin 3, ‖v i‖ := by
  have hv : (∑ i : Fin 3, EuclideanSpace.single i (v i)) = v := by
    ext j
    simp
  calc
    ‖v‖ = ‖∑ i : Fin 3, EuclideanSpace.single i (v i)‖ := by rw [hv]
    _ ≤ ∑ i : Fin 3, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖v i‖ := by simp

/-- The coordinate definition of curl is bounded by six times the full derivative norm. -/
theorem norm_vectorCurl_le (f : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) :
    ‖vectorCurl f x‖ ≤ 6 * ‖fderiv ℝ f x‖ := by
  have hc (i j : Fin 3) :
      ‖partialDerivative (fun y => f y i) j x‖ ≤ ‖fderiv ℝ f x‖ := by
    rw [partialDerivative, fderiv_coordinate f x hf]
    exact (PiLp.norm_apply_le _ i).trans (by
      simpa using ((fderiv ℝ f x).le_opNorm (EuclideanSpace.single j 1)))
  calc
    ‖vectorCurl f x‖ ≤ ∑ i : Fin 3, ‖vectorCurl f x i‖ := norm_le_sum_coordinates _
    _ ≤ ∑ _i : Fin 3, (2 * ‖fderiv ℝ f x‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sub_le _ _).trans (by linarith [hc (i+2) (i+1), hc (i+1) (i+2)])
    _ = 6 * ‖fderiv ℝ f x‖ := by simp; ring

/-- The actual cutoff product rule gives the pointwise bound used in the dual estimate. -/
theorem norm_cutoff_curl_le (ψ : Space → ℝ) (φ : Space → Space) (x : Space)
    (hψ : DifferentiableAt ℝ ψ x) (hφ : DifferentiableAt ℝ φ x) :
    ‖vectorCurl (fun y => ψ y • φ y) x‖ ≤
      6 * (‖ψ x‖ * ‖fderiv ℝ φ x‖ + ‖fderiv ℝ ψ x‖ * ‖φ x‖) := by
  refine (norm_vectorCurl_le _ x (hψ.smul hφ)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [fderiv_smul hψ hφ]
  simpa only [norm_smul, ContinuousLinearMap.norm_smulRight_apply] using
    norm_add_le (ψ x • fderiv ℝ φ x) ((fderiv ℝ ψ x).smulRight (φ x))

/-- Hölder's inequality for the product of the pointwise norms, in real-valued Lp norms. -/
theorem lpNorm_norm_mul_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : Space → E} {g : Space → F} {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hf : MemLp f p volume) (hg : MemLp g q volume) :
    lpNorm (fun x => ‖f x‖ * ‖g x‖) r volume ≤ lpNorm f p volume * lpNorm g q volume := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := p) (q := q) (r := r)
    hf.aestronglyMeasurable hg.aestronglyMeasurable (fun a b => ‖a‖ * ‖b‖) 1
    (Filter.Eventually.of_forall fun x => by simp)
  have hr := ENNReal.toReal_mono (by finiteness [hf.eLpNorm_ne_top, hg.eLpNorm_ne_top]) h
  have hm : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) volume :=
    hf.aestronglyMeasurable.norm.mul hg.aestronglyMeasurable.norm
  simpa [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_one, one_mul,
    toReal_eLpNorm hm,
    toReal_eLpNorm hf.aestronglyMeasurable, toReal_eLpNorm hg.aestronglyMeasurable] using hr

/-- Smooth compactly supported vector fields have square-integrable actual curl. -/
theorem vectorCurl_memLp (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : MemLp (vectorCurl f) 2 volume := by
  have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by simp)).continuous
  have hdm : MemLp (fderiv ℝ f) 2 volume := hd.memLp_of_hasCompactSupport (hfc.fderiv ℝ)
  have hc : ContDiff ℝ ∞ (vectorCurl f) :=
    contDiff_curl _ ((contDiff_piLp 2).mp hf)
  exact hdm.of_le_mul hc.continuous.aestronglyMeasurable_of_secondCountable
    (Filter.Eventually.of_forall fun x =>
      norm_vectorCurl_le f x ((hf.differentiable (by simp)).differentiableAt))

/-- The actual L² cutoff-curl estimate, retaining the two Hölder terms. -/
theorem cutoff_curl_lpNorm_le (ψ : Space → ℝ) (φ : Space → Space)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    lpNorm (vectorCurl (fun x => ψ x • φ x)) 2 volume ≤
      6 * (lpNorm ψ ∞ volume + (sobolevConstant : ℝ) * lpNorm (fderiv ℝ ψ) 3 volume) *
        lpNorm (fderiv ℝ φ) 2 volume := by
  let : ENNReal.HolderTriple 3 6 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
  have hψm : MemLp ψ ∞ volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hφm : MemLp φ 6 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hψd : MemLp (fderiv ℝ ψ) 3 volume :=
    (hψ.fderiv_right (m := ∞) (by simp)).continuous.memLp_of_hasCompactSupport (hψc.fderiv ℝ)
  have hφd : MemLp (fderiv ℝ φ) 2 volume :=
    (hφ.fderiv_right (m := ∞) (by simp)).continuous.memLp_of_hasCompactSupport (hφc.fderiv ℝ)
  let a : Space → ℝ := fun x => ‖ψ x‖ * ‖fderiv ℝ φ x‖
  let b : Space → ℝ := fun x => ‖fderiv ℝ ψ x‖ * ‖φ x‖
  have ha : MemLp a 2 volume := hφd.norm.mul' hψm.norm
  have hb : MemLp b 2 volume := hφm.norm.mul' hψd.norm
  have hg : MemLp (fun x => 6 * (a x + b x)) 2 volume := (ha.add hb).const_mul 6
  calc
    lpNorm (vectorCurl (fun x => ψ x • φ x)) 2 volume ≤
        lpNorm (fun x => 6 * (a x + b x)) 2 volume :=
      lpNorm_mono_real hg (fun x => norm_cutoff_curl_le ψ φ x
        ((hψ.differentiable (by simp)).differentiableAt)
        ((hφ.differentiable (by simp)).differentiableAt))
    _ = 6 * lpNorm (a + b) 2 volume := by
      simpa [Pi.add_apply] using lpNorm_fun_natCast_mul 6 (a + b) 2 volume
    _ ≤ 6 * (lpNorm a 2 volume + lpNorm b 2 volume) :=
      mul_le_mul_of_nonneg_left (lpNorm_add_le ha (by norm_num)) (by norm_num)
    _ ≤ 6 * (lpNorm ψ ∞ volume * lpNorm (fderiv ℝ φ) 2 volume +
        lpNorm (fderiv ℝ ψ) 3 volume * lpNorm φ 6 volume) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (lpNorm_norm_mul_le hψm hφd) (lpNorm_norm_mul_le hψd hφm)) (by norm_num)
    _ ≤ 6 * (lpNorm ψ ∞ volume * lpNorm (fderiv ℝ φ) 2 volume +
        lpNorm (fderiv ℝ ψ) 3 volume *
          ((sobolevConstant : ℝ) * lpNorm (fderiv ℝ φ) 2 volume)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (homogeneous_sobolev φ hφ hφc) lpNorm_nonneg)
    _ = 6 * (lpNorm ψ ∞ volume + (sobolevConstant : ℝ) * lpNorm (fderiv ℝ ψ) 3 volume) *
        lpNorm (fderiv ℝ φ) 2 volume := by ring

/-- The norm of a scalar gradient equals the norm of its Fréchet derivative. -/
theorem norm_gradient_eq_fderiv (ψ : Space → ℝ) (x : Space) :
    ‖gradient ψ x‖ = ‖fderiv ℝ ψ x‖ :=
  (InnerProductSpace.toDual ℝ Space).symm.norm_map _

/-- The L³ cutoff derivative norm can equivalently be written using its actual gradient. -/
theorem lpNorm_gradient_eq_fderiv (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    lpNorm (gradient ψ) 3 volume = lpNorm (fderiv ℝ ψ) 3 volume := by
  have hd : Continuous (fderiv ℝ ψ) := (hψ.fderiv_right (m := ∞) (by simp)).continuous
  have hg : Continuous (gradient ψ) := (InnerProductSpace.toDual ℝ Space).symm.continuous.comp hd
  rw [← lpNorm_norm hg.aestronglyMeasurable, ← lpNorm_norm hd.aestronglyMeasurable]
  congr 1
  funext x
  exact norm_gradient_eq_fderiv ψ x

/-- A dimension-only constant, independent of the cutoff, test field, and support radii. -/
def cutoffCurlConstant : ℝ := 6 * (1 + (sobolevConstant : ℝ))

theorem cutoffCurlConstant_pos : 0 < cutoffCurlConstant := by
  unfold cutoffCurlConstant
  positivity

/-- The source's ordinary-space cutoff-curl bound with the actual gradient L³ norm. -/
theorem cutoff_curl_bound (ψ : Space → ℝ) (φ : Space → Space)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    lpNorm (vectorCurl (fun x => ψ x • φ x)) 2 volume ≤
      cutoffCurlConstant * (lpNorm ψ ∞ volume + lpNorm (gradient ψ) 3 volume) *
        lpNorm (fderiv ℝ φ) 2 volume := by
  rw [lpNorm_gradient_eq_fderiv ψ hψ]
  refine (cutoff_curl_lpNorm_le ψ φ hψ hψc hφ hφc).trans ?_
  apply mul_le_mul_of_nonneg_right _ lpNorm_nonneg
  have ha : 0 ≤ lpNorm ψ ∞ volume := lpNorm_nonneg
  have hb : 0 ≤ lpNorm (fderiv ℝ ψ) 3 volume := lpNorm_nonneg
  have hc : 0 ≤ (sobolevConstant : ℝ) := NNReal.coe_nonneg _
  unfold cutoffCurlConstant
  nlinarith [mul_nonneg hc ha]

/-- The distributional cutoff-curl functional on an arbitrary genuine L² field.
No derivative or divergence condition on `z` is required. -/
theorem integral_cutoff_curl_bound (ψ : Space → ℝ) (φ : Space → Space)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (z : Lp Space 2 (volume : Measure Space)) :
    |∫ x, inner ℝ (z x) (vectorCurl (fun y => ψ y • φ y) x)| ≤
      cutoffCurlConstant * (lpNorm ψ ∞ volume + lpNorm (gradient ψ) 3 volume) *
        ‖z‖ * lpNorm (fderiv ℝ φ) 2 volume := by
  have hprod : ContDiff ℝ ∞ (fun y => ψ y • φ y) := hψ.smul hφ
  have hpc : HasCompactSupport (fun y => ψ y • φ y) := hφc.smul_left (f := ψ)
  have hm : MemLp (vectorCurl (fun y => ψ y • φ y)) 2 volume :=
    vectorCurl_memLp _ hprod hpc
  let v : Lp Space 2 (volume : Measure Space) := hm.toLp _
  have hv : ‖v‖ = lpNorm (vectorCurl (fun y => ψ y • φ y)) 2 volume := by
    rw [Lp.norm_toLp, toReal_eLpNorm hm.aestronglyMeasurable]
  have he : (∫ x, inner ℝ (z x) (vectorCurl (fun y => ψ y • φ y) x)) = inner ℝ z v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [hx]
  calc
    |∫ x, inner ℝ (z x) (vectorCurl (fun y => ψ y • φ y) x)| = |inner ℝ z v| := congrArg abs he
    _ ≤ ‖z‖ * ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) z v
    _ ≤ ‖z‖ * (cutoffCurlConstant * (lpNorm ψ ∞ volume + lpNorm (gradient ψ) 3 volume) *
        lpNorm (fderiv ℝ φ) 2 volume) := by
      rw [hv]
      exact mul_le_mul_of_nonneg_left (cutoff_curl_bound ψ φ hψ hψc hφ hφc) (norm_nonneg z)
    _ = cutoffCurlConstant * (lpNorm ψ ∞ volume + lpNorm (gradient ψ) 3 volume) *
        ‖z‖ * lpNorm (fderiv ℝ φ) 2 volume := by ring

end EulerMeanCutoffCurl
