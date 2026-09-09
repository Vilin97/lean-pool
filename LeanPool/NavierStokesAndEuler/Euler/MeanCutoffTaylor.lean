/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffDifferenceBound
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! Uniform Taylor remainders for the actual smooth compact cutoffs. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanCutoffCurl
open scoped ContDiff ENNReal

-- Fix the canonical structures before forming the third nested operator space.
private local instance : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance

/-- A global second derivative bound gives the quadratic Taylor remainder directly by mean value. -/
theorem norm_linearization_remainder_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) (hf : ContDiff ℝ ∞ f) (M : ℝ) (hM : 0 ≤ M)
    (hD₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (x v : Space) :
    ‖f (x+v) - f x - fderiv ℝ f x v‖ ≤ M * ‖v‖ ^ 2 := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hdifference (y : Space) : ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ M * ‖y-x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (s := Set.univ) (fun z _ => hdf z) (fun z _ => hD₂ z)
      (convex_univ : Convex ℝ (Set.univ : Set Space)) (Set.mem_univ x) (Set.mem_univ y)
  have hbound (y : Space) (hy : y ∈ Metric.closedBall x ‖v‖) :
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ M * ‖v‖ := by
    exact (hdifference y).trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,
      dist_eq_norm] using hy) hM)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (𝕜 := ℝ) (f := f) (s := Metric.closedBall x ‖v‖) (C := M * ‖v‖)
    (φ := fderiv ℝ f x) (x := x) (y := x+v)
    (fun y _ => (hf.differentiable (by simp)) y) hbound (convex_closedBall x ‖v‖)
    (by simp) (by simp [dist_eq_norm])
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using H

/-- Difference quotients converge with a quantitative first-order error. -/
theorem norm_differenceQuotient_remainder_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) (hf : ContDiff ℝ ∞ f) (M : ℝ) (hM : 0 ≤ M)
    (hD₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (a : Space) (h : ℝ) (hh : h ≠ 0) (x : Space) :
    ‖h⁻¹ • (f (x+h•a) - f x) - fderiv ℝ f x a‖ ≤ M * |h| * ‖a‖ ^ 2 := by
  have heq : h⁻¹ • (f (x+h•a) - f x) - fderiv ℝ f x a =
      h⁻¹ • (f (x+h•a) - f x - fderiv ℝ f x (h•a)) := by
    simp only [smul_sub, map_smul, smul_smul, inv_mul_cancel₀ hh, one_smul]
  rw [heq, norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |h|⁻¹ * (M * ‖h•a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_linearization_remainder_le f hf M hM hD₂ x (h•a))
        (inv_nonneg.mpr (abs_nonneg h))
    _ = M * |h| * ‖a‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      field_simp [abs_ne_zero.mpr hh]

def Cutoff.directional (χ : Cutoff) (a : Space) : Cutoff :=
  ⟨fun x => fderiv ℝ χ.field x a,
    (χ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    χ.compact.fderiv_apply ℝ a⟩

theorem Cutoff.directional_fderiv (χ : Cutoff) (a x : Space) :
    fderiv ℝ (χ.directional a).field x = fderiv ℝ (fderiv ℝ χ.field) x a := by
  apply ContinuousLinearMap.ext
  intro v
  change (fderiv ℝ (fun y => fderiv ℝ χ.field y a) x) v = _
  have hd : DifferentiableAt ℝ (fderiv ℝ χ.field) x :=
    ((χ.smooth.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  rw [fderiv_clm_apply hd (differentiableAt_const a)]
  simpa using χ.smooth.contDiffAt.isSymmSndFDerivAt (by simp) v a

theorem Cutoff.directional_support (χ : Cutoff) (a : Space) :
    tsupport (χ.directional a).field ⊆ tsupport χ.field := tsupport_fderiv_apply_subset ℝ a

theorem Cutoff.sub_support (χ ψ : Cutoff) (K : Set Space) (hK : IsClosed K)
    (hχ : tsupport χ.field ⊆ K) (hψ : tsupport ψ.field ⊆ K) : tsupport (χ.sub ψ).field ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have h₁ : χ.field x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hn (hχ ht))
  have h₂ : ψ.field x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hn (hψ ht))
  apply hx
  change χ.field x - ψ.field x = 0
  rw [h₁, h₂, sub_self]

/-- A compactly supported cutoff is bounded in the exact duality norm by pointwise data. -/
theorem cutoffBound_le_of_support (χ : Cutoff) (R M₀ M₁ : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ x, ‖χ.field x‖ ≤ M₀) (hdb : ∀ x, ‖fderiv ℝ χ.field x‖ ≤ M₁) :
    cutoffBound χ ≤ 3 * cutoffCurlConstant *
      (M₀ + M₁ * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ)) := by
  have hK := (isCompact_closedBall (0 : Space) R).measure_ne_top (μ := (volume : Measure Space))
  have h₀ := lpNorm_le_bound_volume χ.field χ.smooth.continuous.aestronglyMeasurable _ hK
    M₀ hM₀ hb (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))) (∞ : ℝ≥0∞)
  simp only [ENNReal.toReal_top, div_zero, Real.rpow_zero, mul_one] at h₀
  have h₁ := lpNorm_le_bound_volume (fderiv ℝ χ.field)
    (χ.smooth.fderiv_right (m := ∞) (by simp)).continuous.aestronglyMeasurable _ hK M₁ hM₁ hdb
    (fun x hx => fderiv_of_notMem_tsupport ℝ (fun ht => hx (hs ht))) 3
  norm_num only [ENNReal.toReal_ofNat] at h₁
  unfold cutoffBound
  rw [lpNorm_gradient_eq_fderiv _ χ.smooth]
  exact mul_le_mul_of_nonneg_left (add_le_add h₀ h₁)
    (mul_nonneg (by norm_num) cutoffCurlConstant_pos.le)

def Cutoff.differenceError (χ : Cutoff) (a : Space) (h : ℝ) : Cutoff :=
  (χ.differenceQuotient a h).sub (χ.directional a)

theorem Cutoff.differenceError_support (χ : Cutoff) (R : ℝ)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (a : Space) (h : ℝ) (hstep : ‖h • a‖ ≤ 1) :
    tsupport (χ.differenceError a h).field ⊆ Metric.closedBall (0 : Space) (R+1) := by
  apply Cutoff.sub_support _ _ _ Metric.isClosed_closedBall
  · exact differenceQuotient_support χ R hs a h hstep
  · intro x hx
    have ht := hs (Cutoff.directional_support χ a hx)
    simp only [Metric.mem_closedBall, dist_zero_right] at ht ⊢
    linarith

theorem Cutoff.differenceError_fderiv (χ : Cutoff) (a : Space) (h : ℝ) (x : Space) :
    fderiv ℝ (χ.differenceError a h).field x =
      h⁻¹ • (fderiv ℝ χ.field (x+h•a) - fderiv ℝ χ.field x) -
        fderiv ℝ (fderiv ℝ χ.field) x a := by
  change fderiv ℝ ((χ.differenceQuotient a h).field - (χ.directional a).field) x = _
  rw [fderiv_sub (f := (χ.differenceQuotient a h).field) (g := (χ.directional a).field)
    ((χ.differenceQuotient a h).smooth.differentiable (by simp) x)
    ((χ.directional a).smooth.differentiable (by simp) x),
    differenceQuotient_fderiv, Cutoff.directional_fderiv]

/-- The cutoff difference quotient converges in precisely the norm controlling the boundary operator. -/
theorem cutoffBound_differenceError (χ : Cutoff) (R M₂ M₃ : ℝ)
    (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hD₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ.field) x‖ ≤ M₂)
    (hD₃ : ∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field)) x‖ ≤ M₃)
    (a : Space) (h : ℝ) (hh : h ≠ 0) (hstep : ‖h • a‖ ≤ 1) :
    cutoffBound (χ.differenceError a h) ≤ cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2 := by
  have hb (x : Space) : ‖(χ.differenceError a h).field x‖ ≤ M₂ * |h| * ‖a‖ ^ 2 :=
    norm_differenceQuotient_remainder_le χ.field χ.smooth M₂ hM₂ hD₂ a h hh x
  have hdb (x : Space) : ‖fderiv ℝ (χ.differenceError a h).field x‖ ≤ M₃ * |h| * ‖a‖ ^ 2 := by
    rw [Cutoff.differenceError_fderiv]
    exact norm_differenceQuotient_remainder_le (fderiv ℝ χ.field)
      (χ.smooth.fderiv_right (m := ∞) (by simp)) M₃ hM₃ hD₃ a h hh x
  have H := cutoffBound_le_of_support (χ.differenceError a h) (R+1)
    (M₂ * |h| * ‖a‖ ^ 2) (M₃ * |h| * ‖a‖ ^ 2)
    (mul_nonneg (mul_nonneg hM₂ (abs_nonneg h)) (sq_nonneg _))
    (mul_nonneg (mul_nonneg hM₃ (abs_nonneg h)) (sq_nonneg _))
    (Cutoff.differenceError_support χ R hs a h hstep) hb hdb
  refine H.trans_eq ?_
  unfold cutoffDifferenceConstant
  ring

end EulerMeanBoundary
