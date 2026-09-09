/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryTranslation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Exact spatial difference-quotient commutators with the actual mixed boundary operator. -/

@[expose] public section


noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl
open scoped ENNReal

theorem lpNorm_translated {E : Type*} [NormedAddCommGroup E]
    (f : Space → E) (hf : Continuous f) (a : Space) (p : ℝ≥0∞) :
    lpNorm (fun x => f (x+a)) p volume = lpNorm f p volume := by
  have hm := measurePreserving_add_right (volume : Measure Space) a
  have hfc : AEStronglyMeasurable (fun x => f (x+a)) volume :=
    hf.aestronglyMeasurable.comp_measurePreserving hm
  rw [← toReal_eLpNorm hfc, ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hm)

theorem cutoffBound_translate (χ : Cutoff) (a : Space) :
    cutoffBound (χ.translate a) = cutoffBound χ := by
  have hgrad : gradient (χ.translate a).field = fun x => gradient χ.field (x+a) :=
    funext fun x => gradient_translated a χ.field x
  unfold cutoffBound
  rw [hgrad]
  change 3 * cutoffCurlConstant *
    (lpNorm (fun x => χ.field (x+a)) ∞ volume + lpNorm (fun x => gradient χ.field (x+a)) 3 volume)
        = _
  rw [lpNorm_translated χ.field χ.smooth.continuous,
    lpNorm_translated (gradient χ.field) (contDiff_gradient χ.smooth).continuous]

/-- The genuine directional spatial difference quotient, defined also at h = 0. -/
def spatialDifference (a : Space) (h : ℝ) : L2 →L[ℝ] L2 :=
  h⁻¹ • ((translation (h • a)).toContinuousLinearMap - ContinuousLinearMap.id ℝ L2)

theorem spatialDifference_apply (a : Space) (h : ℝ) (z : L2) :
    spatialDifference a h z = h⁻¹ • (translation (h • a) z - z) := rfl

/-- Difference quotient, given by `((χ.translate (h • a)).sub χ).scale h⁻¹`. -/
def Cutoff.differenceQuotient (χ : Cutoff) (a : Space) (h : ℝ) : Cutoff :=
  ((χ.translate (h • a)).sub χ).scale h⁻¹

theorem Cutoff.differenceQuotient_field (χ : Cutoff) (a : Space) (h : ℝ) (x : Space) :
    (χ.differenceQuotient a h).field x = h⁻¹ * (χ.field (x + h • a) - χ.field x) := rfl

theorem spatialDifference_commutator (a : Space) (h : ℝ) (A : L2 →L[ℝ] L2) :
    (spatialDifference a h).comp A - A.comp (spatialDifference a h) =
      h⁻¹ • translationCommutator (h • a) A := by
  unfold spatialDifference translationCommutator
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id, smul_sub]
  abel

/-- Exact two-position derivative splitting for an actual spatial difference quotient. -/
theorem mixedBoundaryOperator_differenceCommutator (a : Space) (h : ℝ) (χ ψ : Cutoff) :
    (spatialDifference a h).comp (mixedBoundaryOperator χ ψ) -
        (mixedBoundaryOperator χ ψ).comp (spatialDifference a h) =
      (mixedBoundaryOperator (χ.differenceQuotient a h) (ψ.translate (h • a)) +
        mixedBoundaryOperator χ (ψ.differenceQuotient a h)).comp
          (translation (h • a)).toContinuousLinearMap := by
  rw [spatialDifference_commutator, mixedBoundaryOperator_translationCommutator]
  unfold Cutoff.differenceQuotient
  rw [mixedBoundaryOperator_scale_left, mixedBoundaryOperator_scale_right]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, smul_add]

/-- The commutator is bounded by the actual two cutoff difference quotients. -/
theorem mixedBoundaryOperator_differenceCommutator_norm_le
    (a : Space) (h : ℝ) (χ ψ : Cutoff) :
    ‖(spatialDifference a h).comp (mixedBoundaryOperator χ ψ) -
        (mixedBoundaryOperator χ ψ).comp (spatialDifference a h)‖ ≤
      cutoffBound (χ.differenceQuotient a h) * cutoffBound (ψ.translate (h • a)) +
        cutoffBound χ * cutoffBound (ψ.differenceQuotient a h) := by
  rw [mixedBoundaryOperator_differenceCommutator]
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (mul_nonneg (cutoffBound_nonneg _) (cutoffBound_nonneg _))
      (mul_nonneg (cutoffBound_nonneg _) (cutoffBound_nonneg _)))
  intro z
  change ‖mixedBoundaryOperator (χ.differenceQuotient a h) (ψ.translate (h • a))
      (translation (h • a) z) + mixedBoundaryOperator χ (ψ.differenceQuotient a h)
        (translation (h • a) z)‖ ≤ _
  calc
    _ ≤ ‖mixedBoundaryOperator (χ.differenceQuotient a h) (ψ.translate (h • a))
          (translation (h • a) z)‖ +
        ‖mixedBoundaryOperator χ (ψ.differenceQuotient a h) (translation (h • a) z)‖ :=
      norm_add_le _ _
    _ ≤ (cutoffBound (χ.differenceQuotient a h) * cutoffBound (ψ.translate (h • a))) *
          ‖translation (h • a) z‖ +
        (cutoffBound χ * cutoffBound (ψ.differenceQuotient a h)) * ‖translation (h • a) z‖ := by
      apply add_le_add
      · exact ((mixedBoundaryOperator _ _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (mixedBoundaryOperator_norm_le _ _) (norm_nonneg _))
      · exact ((mixedBoundaryOperator _ _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (mixedBoundaryOperator_norm_le _ _) (norm_nonneg _))
    _ = _ := by
      rw [(translation (h • a)).norm_map]
      ring

theorem mixedBoundaryOperator_differenceCommutator_norm_le_invariant
    (a : Space) (h : ℝ) (χ ψ : Cutoff) :
    ‖(spatialDifference a h).comp (mixedBoundaryOperator χ ψ) -
        (mixedBoundaryOperator χ ψ).comp (spatialDifference a h)‖ ≤
      cutoffBound (χ.differenceQuotient a h) * cutoffBound ψ +
        cutoffBound χ * cutoffBound (ψ.differenceQuotient a h) := by
  simpa only [cutoffBound_translate] using mixedBoundaryOperator_differenceCommutator_norm_le a h χ
      ψ

end EulerMeanBoundary
