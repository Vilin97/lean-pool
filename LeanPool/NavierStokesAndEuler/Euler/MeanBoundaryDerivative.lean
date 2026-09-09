/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffTaylor

/-! Genuine directional derivatives of the localized Newtonian operator family in operator norm. -/

@[expose] public section


noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  Filter
open scoped ContDiff Topology

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instMeanBoundaryDerivative1 : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instMeanBoundaryDerivative2 : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ)` instance to shorten
typeclass synthesis. -/
local instance instMeanBoundaryDerivative3 : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instMeanBoundaryDerivative4 : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] ℝ) :=
    inferInstance

@[simp] theorem Cutoff.translate_zero (χ : Cutoff) : χ.translate 0 = χ := by
  apply Cutoff.ext
  exact funext fun x => congrArg χ.field (add_zero x)

theorem cutoffCurl_differenceError (χ : Cutoff) (a : Space) (h : ℝ) :
    cutoffCurl (χ.differenceError a h) =
      h⁻¹ • (cutoffCurl (χ.translate (h • a)) - cutoffCurl χ) - cutoffCurl (χ.directional a) := by
  rw [Cutoff.differenceError, cutoffCurl_sub, Cutoff.differenceQuotient,
    cutoffCurl_scale, cutoffCurl_sub]

theorem Cutoff.exists_taylor_controls (χ : Cutoff) :
    ∃ R M₂ M₃ : ℝ, 0 ≤ M₂ ∧ 0 ≤ M₃ ∧
      tsupport χ.field ⊆ Metric.closedBall (0 : Space) R ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ χ.field) x‖ ≤ M₂) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field)) x‖ ≤ M₃) := by
  obtain ⟨R, hR⟩ := χ.compact.isBounded.subset_closedBall (0 : Space)
  have hs₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ χ.field)) :=
    (χ.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hs₃ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field))) :=
    hs₂.fderiv_right (m := ∞) (by simp)
  obtain ⟨M₂, h₂⟩ := ((χ.compact.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hs₂.continuous
  obtain ⟨M₃, h₃⟩ := (((χ.compact.fderiv ℝ).fderiv ℝ).fderiv ℝ).exists_bound_of_continuous
      hs₃.continuous
  exact ⟨R, M₂, M₃, (norm_nonneg _).trans (h₂ 0), (norm_nonneg _).trans (h₃ 0), hR, h₂, h₃⟩

/-- Translating the actual cutoff differentiates the bounded cutoff-curl map in operator norm. -/
theorem cutoffCurl_hasDerivAt_zero (χ : Cutoff) (a : Space) :
    HasDerivAt (fun t : ℝ => cutoffCurl (χ.translate (t • a)))
      (cutoffCurl (χ.directional a)) 0 := by
  obtain ⟨R, M₂, M₃, hM₂, hM₃, hs, h₂, h₃⟩ := χ.exists_taylor_controls
  have hstep : ∀ᶠ h : ℝ in 𝓝 0, ‖h • a‖ ≤ 1 := by
    have hc : ContinuousAt (fun h : ℝ => ‖h • a‖) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simp : ‖(0 : ℝ) • a‖ < 1))).mono (fun _ hh => hh.le)
  apply (hasDerivAt_iff_tendsto_slope_zero
    (f := fun t : ℝ => cutoffCurl (χ.translate (t • a)))
    (f' := cutoffCurl (χ.directional a)) (x := 0)).mpr
  simp only [zero_add, zero_smul, Cutoff.translate_zero]
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm'
    (f := fun h : ℝ => h⁻¹ • (cutoffCurl (χ.translate (h • a)) - cutoffCurl χ) -
      cutoffCurl (χ.directional a))
    (t₀ := 𝓝[≠] (0 : ℝ))
    (a := fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2)
  · filter_upwards [self_mem_nhdsWithin, hstep.filter_mono nhdsWithin_le_nhds] with h hh hsmall
    have hne : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
    rw [← cutoffCurl_differenceError]
    exact (cutoffCurl_norm_le _).trans (cutoffBound_differenceError χ R M₂ M₃ hM₂ hM₃ hs h₂ h₃ a h
        hne hsmall)
  · have hc : Continuous (fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2) := by
      fun_prop
    simpa only [abs_zero, mul_zero, zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem weakPotential_differenceError (χ : Cutoff) (a : Space) (h : ℝ) :
    weakPotential (χ.differenceError a h) =
      h⁻¹ • (weakPotential (χ.translate (h • a)) - weakPotential χ) - weakPotential (χ.directional
          a) := by
  calc
    _ = weakPotential (χ.differenceQuotient a h) - weakPotential (χ.directional a) :=
      weakPotential_sub _ _
    _ = h⁻¹ • weakPotential ((χ.translate (h • a)).sub χ) - weakPotential (χ.directional a) :=
      congrArg (fun B : L2 →L[ℝ] homogeneousSpace => B - weakPotential (χ.directional a))
        (weakPotential_scale ((χ.translate (h • a)).sub χ) h⁻¹)
    _ = _ := congrArg (fun B : L2 →L[ℝ] homogeneousSpace => h⁻¹ • B - weakPotential (χ.directional
        a))
      (weakPotential_sub (χ.translate (h • a)) χ)

theorem weakPotential_operatorNorm_le (χ : Cutoff) : ‖weakPotential χ‖ ≤ cutoffBound χ := by
  change ‖(cutoffCurl χ).adjoint‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact cutoffCurl_norm_le χ

/-- The represented weak potential differentiates with the same actual cutoff derivative. -/
theorem weakPotential_hasDerivAt_zero (χ : Cutoff) (a : Space) :
    HasDerivAt (fun t : ℝ => weakPotential (χ.translate (t • a)))
      (weakPotential (χ.directional a)) 0 := by
  obtain ⟨R, M₂, M₃, hM₂, hM₃, hs, h₂, h₃⟩ := χ.exists_taylor_controls
  have hstep : ∀ᶠ h : ℝ in 𝓝 0, ‖h • a‖ ≤ 1 := by
    have hc : ContinuousAt (fun h : ℝ => ‖h • a‖) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simp : ‖(0 : ℝ) • a‖ < 1))).mono (fun _ hh => hh.le)
  apply (hasDerivAt_iff_tendsto_slope_zero
    (f := fun t : ℝ => weakPotential (χ.translate (t • a)))
    (f' := weakPotential (χ.directional a)) (x := 0)).mpr
  simp only [zero_add, zero_smul, Cutoff.translate_zero]
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm'
    (f := fun h : ℝ => h⁻¹ • (weakPotential (χ.translate (h • a)) - weakPotential χ) -
      weakPotential (χ.directional a))
    (t₀ := 𝓝[≠] (0 : ℝ))
    (a := fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2)
  · filter_upwards [self_mem_nhdsWithin, hstep.filter_mono nhdsWithin_le_nhds] with h hh hsmall
    have hne : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
    rw [← weakPotential_differenceError]
    exact (weakPotential_operatorNorm_le _).trans (cutoffBound_differenceError χ R M₂ M₃ hM₂ hM₃ hs
        h₂ h₃ a h hne hsmall)
  · have hc : Continuous (fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2) := by
      fun_prop
    simpa only [abs_zero, mul_zero, zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Both cutoff positions contribute to the actual operator-norm derivative. -/
theorem mixedBoundaryOperator_hasDerivAt_zero (χ ψ : Cutoff) (a : Space) :
    HasDerivAt (fun t : ℝ => mixedBoundaryOperator (χ.translate (t • a)) (ψ.translate (t • a)))
      (mixedBoundaryOperator (χ.directional a) ψ + mixedBoundaryOperator χ (ψ.directional a)) 0 :=
          by
  have h := (cutoffCurl_hasDerivAt_zero χ a).clm_comp (weakPotential_hasDerivAt_zero ψ a)
  simpa only [zero_smul, Cutoff.translate_zero, mixedBoundaryOperator] using h

/-- The corresponding differential commutator has the source's duality bound. -/
theorem mixedBoundaryOperator_derivative_norm_le (χ ψ : Cutoff) (a : Space) :
    ‖mixedBoundaryOperator (χ.directional a) ψ + mixedBoundaryOperator χ (ψ.directional a)‖ ≤
      cutoffBound (χ.directional a) * cutoffBound ψ + cutoffBound χ * cutoffBound (ψ.directional a)
          :=
  (norm_add_le _ _).trans (add_le_add (mixedBoundaryOperator_norm_le _ _)
      (mixedBoundaryOperator_norm_le _ _))

end EulerMeanBoundary
