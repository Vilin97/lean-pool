/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryDerivative
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section

/-! Full spatial-parameter smoothness of the actual localized Newtonian operators. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  Filter
open scoped ContDiff Topology

theorem Cutoff.translate_add (χ : Cutoff) (a b : Space) :
    (χ.translate a).translate b = χ.translate (a+b) := by
  apply Cutoff.ext
  funext x
  change χ.field ((x+b)+a) = χ.field (x+(a+b))
  congr 1
  abel

theorem Cutoff.directional_translate (χ : Cutoff) (a b : Space) :
    (χ.translate b).directional a = (χ.directional a).translate b := by
  apply Cutoff.ext
  funext x
  change (fderiv ℝ (fun y => χ.field (y+b)) x) a = (fderiv ℝ χ.field (x+b)) a
  rw [fderiv_comp_add_right]

theorem Cutoff.directional_add (χ : Cutoff) (a b : Space) :
    χ.directional (a+b) = (χ.directional a).add (χ.directional b) := by
  apply Cutoff.ext
  exact funext fun x => (fderiv ℝ χ.field x).map_add a b

theorem Cutoff.directional_smul (χ : Cutoff) (c : ℝ) (a : Space) :
    χ.directional (c • a) = (χ.directional a).scale c := by
  apply Cutoff.ext
  exact funext fun x => (fderiv ℝ χ.field x).map_smul c a

section LinearCutoffOperation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative with respect to a translation parameter of an operation linear in the cutoff. -/
def cutoffDirectionalMap (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ) (χ : Cutoff) : Space →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => L (χ.directional a)
      map_add' := fun a b => by rw [Cutoff.directional_add, hadd]
      map_smul' := fun c a => by rw [Cutoff.directional_smul, hsmul]; rfl }

@[simp] theorem cutoffDirectionalMap_apply (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ) (χ : Cutoff) (a : Space) :
    cutoffDirectionalMap L hadd hsmul χ a = L (χ.directional a) := rfl

theorem cutoffOperation_differenceError (L : Cutoff → E)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ) (χ : Cutoff) (a b : Space) :
    L ((χ.translate a).differenceError (b-a) 1) =
      L (χ.translate b) - L (χ.translate a) - L ((χ.translate a).directional (b-a)) := by
  rw [Cutoff.differenceError, hsub, Cutoff.differenceQuotient, hsmul, hsub]
  simp only [inv_one, one_smul, Cutoff.translate_add, add_sub_cancel]

/-- The proved cutoff dual norm and a genuine Taylor remainder give the full Fréchet derivative. -/
theorem cutoffOperation_hasFDerivAt (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ) (χ : Cutoff) (a : Space) :
    HasFDerivAt (fun b : Space => L (χ.translate b))
      (cutoffDirectionalMap L hadd hsmul (χ.translate a)) a := by
  obtain ⟨R, M₂, M₃, hM₂, hM₃, hs, h₂, h₃⟩ := (χ.translate a).exists_taylor_controls
  have hstep : ∀ᶠ b : Space in 𝓝 a, ‖b-a‖ ≤ 1 := by
    have hc : ContinuousAt (fun b : Space => ‖b-a‖) a := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simp : ‖a-a‖ < 1))).mono (fun _ h => h.le)
  have hrem (b : Space) (hb : ‖b-a‖ ≤ 1) :
      ‖L (χ.translate b) - L (χ.translate a) -
        cutoffDirectionalMap L hadd hsmul (χ.translate a) (b-a)‖ ≤
          cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖^2 := by
    rw [cutoffDirectionalMap_apply, ← cutoffOperation_differenceError L hsmul hsub]
    have H := (hbound _).trans
      (cutoffBound_differenceError (χ.translate a) R M₂ M₃ hM₂ hM₃ hs h₂ h₃
        (b-a) 1 one_ne_zero (by simpa only [one_smul] using hb))
    simpa only [abs_one, mul_one] using H
  apply hasFDerivAt_iff_tendsto.mpr
  refine squeeze_zero' (Eventually.of_forall (fun b =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))) ?_ ?_
      (g := fun b : Space => cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖)
  · filter_upwards [hstep] with b hb
    calc
      _ ≤ ‖b-a‖⁻¹ * (cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖^2) :=
        mul_le_mul_of_nonneg_left (hrem b hb) (inv_nonneg.mpr (norm_nonneg _))
      _ = cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖ := by
        by_cases h : ‖b-a‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun b : Space => cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto a

/-- Induction differentiates the actual cutoff repeatedly, with no smoothness hypothesis on L. -/
theorem cutoffOperation_contDiff (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ) (χ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space => L (χ.translate a)) := by
  have hnat : ∀ n : ℕ, ∀ ψ : Cutoff, ContDiff ℝ n (fun a : Space => L (ψ.translate a)) := by
    intro n
    induction n with
    | zero =>
      intro ψ
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun a => (cutoffOperation_hasFDerivAt L hadd hsmul hsub hbound ψ a).continuousAt))
    | succ n ih =>
      intro ψ
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun a => cutoffDirectionalMap L hadd hsmul (ψ.translate a), ?_,
        fun a => cutoffOperation_hasFDerivAt L hadd hsmul hsub hbound ψ a⟩
      apply contDiff_clm_apply_iff.mpr
      intro b
      simpa only [cutoffDirectionalMap_apply, Cutoff.directional_translate] using ih (ψ.directional
        b)
  exact contDiff_iff_forall_nat_le.mpr (fun n _ => hnat n χ)

end LinearCutoffOperation

/-- Actual Fréchet derivative of the cutoff-curl extension. -/
theorem cutoffCurl_hasFDerivAt (χ : Cutoff) (a : Space) :
    HasFDerivAt (fun b : Space => cutoffCurl (χ.translate b))
      (cutoffDirectionalMap cutoffCurl cutoffCurl_add cutoffCurl_scale (χ.translate a)) a :=
  cutoffOperation_hasFDerivAt cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le χ a

/-- Actual Fréchet derivative of the weak Newtonian potential. -/
theorem weakPotential_hasFDerivAt (χ : Cutoff) (a : Space) :
    HasFDerivAt (fun b : Space => weakPotential (χ.translate b))
      (cutoffDirectionalMap weakPotential weakPotential_add weakPotential_scale (χ.translate a)) a
        :=
  cutoffOperation_hasFDerivAt weakPotential weakPotential_add weakPotential_scale weakPotential_sub
    weakPotential_operatorNorm_le χ a

theorem cutoffCurl_contDiff (χ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space => cutoffCurl (χ.translate a)) :=
  cutoffOperation_contDiff cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le χ

theorem weakPotential_contDiff (χ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space => weakPotential (χ.translate a)) :=
  cutoffOperation_contDiff weakPotential weakPotential_add weakPotential_scale weakPotential_sub
    weakPotential_operatorNorm_le χ

/-- Joint translation of both cutoffs is smooth in the full three-dimensional parameter. -/
theorem mixedBoundaryOperator_contDiff (χ ψ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space =>
      mixedBoundaryOperator (χ.translate a) (ψ.translate a)) :=
  (cutoffCurl_contDiff χ).clm_comp (weakPotential_contDiff ψ)

end EulerMeanBoundary
