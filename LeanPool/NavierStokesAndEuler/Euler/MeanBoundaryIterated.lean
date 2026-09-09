/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryFrechet
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Genuine all-order derivatives of the cutoff operators, with a fixed support-volume factor. -/

noncomputable section


namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl
open scoped ContDiff

/-- Differentiation of a smooth cutoff in one fixed direction has the expected tensor bound. -/
theorem Cutoff.norm_iteratedFDeriv_directional (χ : Cutoff) (v x : Space) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (χ.directional v).field x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n+1) χ.field x‖ := by
  have H := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ χ.field) (c := v) (n := n) (x := x)
    (χ.smooth.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)
  simpa only [Cutoff.directional, norm_iteratedFDeriv_fderiv] using H

section LinearCutoffOperation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every actual higher derivative moves one direction onto the cutoff itself. -/
theorem cutoffOperation_iteratedFDeriv_succ (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ)
    (χ : Cutoff) (a : Space) (n : ℕ) (m : Fin (n+1) → Space) :
    iteratedFDeriv ℝ (n+1) (fun b : Space => L (χ.translate b)) a m =
      iteratedFDeriv ℝ n
        (fun b : Space => L ((χ.directional (m (Fin.last n))).translate b)) a (Fin.init m) := by
  let F : Space → E := fun b => L (χ.translate b)
  have hF : ContDiff ℝ ∞ F := cutoffOperation_contDiff L hadd hsmul hsub hbound χ
  have hDF : fderiv ℝ F = fun b => cutoffDirectionalMap L hadd hsmul (χ.translate b) :=
    funext fun b => (cutoffOperation_hasFDerivAt L hadd hsmul hsub hbound χ b).fderiv
  have H := (ContinuousLinearMap.apply ℝ E (m (Fin.last n))).iteratedFDeriv_comp_left
    (hF.fderiv_right (m := ∞) (by simp)).contDiffAt (x := a) (i := n) (by simp)
  have He := congrArg (fun G => G (Fin.init m)) H
  change iteratedFDeriv ℝ n (fun b => fderiv ℝ F b (m (Fin.last n))) a (Fin.init m) =
    iteratedFDeriv ℝ n (fderiv ℝ F) a (Fin.init m) (m (Fin.last n)) at He
  change iteratedFDeriv ℝ (n+1) F a m = _
  rw [iteratedFDeriv_succ_apply_right, ← He, hDF]
  simp only [cutoffDirectionalMap_apply, Cutoff.directional_translate]

/-- Uniform pointwise bounds of orders n and n+1 control the actual operator-norm derivative.
The support-volume factor is independent of n. -/
theorem cutoffOperation_iteratedFDeriv_bound (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ)
    (n : ℕ) (χ : Cutoff) (R M₀ M₁ : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (h₀ : ∀ x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ M₀)
    (h₁ : ∀ x, ‖iteratedFDeriv ℝ (n+1) χ.field x‖ ≤ M₁) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => L (χ.translate b)) a‖ ≤
      3 * cutoffCurlConstant *
        (M₀ + M₁ * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ)) := by
  induction n generalizing χ M₀ M₁ with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have H := (hbound (χ.translate a)).trans_eq (cutoffBound_translate χ a)
    apply H.trans
    apply cutoffBound_le_of_support χ R M₀ M₁ hM₀ hM₁ hs
    · simpa only [norm_iteratedFDeriv_zero] using h₀
    · intro x
      have hx := h₁ x
      change ‖iteratedFDeriv ℝ 1 χ.field x‖ ≤ M₁ at hx
      rwa [norm_iteratedFDeriv_one] at hx
  | succ n ih =>
    have hC : 0 ≤ 3 * cutoffCurlConstant := mul_nonneg (by norm_num) cutoffCurlConstant_pos.le
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro m
    rw [cutoffOperation_iteratedFDeriv_succ L hadd hsmul hsub hbound]
    have H := ih (χ.directional (m (Fin.last n)))
      (‖m (Fin.last n)‖ * M₀) (‖m (Fin.last n)‖ * M₁)
      (mul_nonneg (norm_nonneg _) hM₀) (mul_nonneg (norm_nonneg _) hM₁)
      ((χ.directional_support _).trans hs)
      (fun x => (χ.norm_iteratedFDeriv_directional (m (Fin.last n)) x n).trans
        (mul_le_mul_of_nonneg_left (h₀ x) (norm_nonneg _)))
      (fun x => (χ.norm_iteratedFDeriv_directional (m (Fin.last n)) x (n+1)).trans
        (mul_le_mul_of_nonneg_left (h₁ x) (norm_nonneg _)))
    calc
      _ ≤ ‖iteratedFDeriv ℝ n
          (fun b : Space => L ((χ.directional (m (Fin.last n))).translate b)) a‖ *
            ∏ i, ‖(Fin.init m) i‖ :=
          (iteratedFDeriv ℝ n
            (fun b : Space => L ((χ.directional (m (Fin.last n))).translate b)) a).le_opNorm
              (Fin.init m)
      _ ≤ (3 * cutoffCurlConstant *
          (‖m (Fin.last n)‖ * M₀ + ‖m (Fin.last n)‖ * M₁ *
            (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ))) *
          ∏ i, ‖(Fin.init m) i‖ := mul_le_mul_of_nonneg_right H (by positivity)
      _ = _ := by
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.init_def]
        ring

end LinearCutoffOperation

theorem cutoffCurl_iteratedFDeriv_bound (n : ℕ) (χ : Cutoff) (R M₀ M₁ : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (h₀ : ∀ x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ M₀)
    (h₁ : ∀ x, ‖iteratedFDeriv ℝ (n+1) χ.field x‖ ≤ M₁) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => cutoffCurl (χ.translate b)) a‖ ≤
      3 * cutoffCurlConstant *
        (M₀ + M₁ * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ)) :=
  cutoffOperation_iteratedFDeriv_bound cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le n χ R M₀ M₁ hM₀ hM₁ hs h₀ h₁ a

theorem weakPotential_iteratedFDeriv_bound (n : ℕ) (χ : Cutoff) (R M₀ M₁ : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (h₀ : ∀ x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ M₀)
    (h₁ : ∀ x, ‖iteratedFDeriv ℝ (n+1) χ.field x‖ ≤ M₁) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => weakPotential (χ.translate b)) a‖ ≤
      3 * cutoffCurlConstant *
        (M₀ + M₁ * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ)) :=
  cutoffOperation_iteratedFDeriv_bound weakPotential weakPotential_add weakPotential_scale
    weakPotential_sub
    weakPotential_operatorNorm_le n χ R M₀ M₁ hM₀ hM₁ hs h₀ h₁ a

end EulerMeanBoundary
