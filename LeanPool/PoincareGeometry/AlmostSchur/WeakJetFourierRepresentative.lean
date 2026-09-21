/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakJetFourierEstimate
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Identifying the Fourier regularity endpoint almost everywhere

This file uses test-function uniqueness, not pointwise continuity of the input,
to identify a classical inverse Fourier integral with its integrable input.
The local weak-jet to weighted Fourier estimate is a separate outstanding step.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped Topology ContDiff FourierTransform SchwartzMap
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Fourier self-adjointness for two integrable complex functions. -/
theorem integral_fourier_mul_integrable {f g : E → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner hf hg

/-- Inverse Fourier self-adjointness for two integrable complex functions. -/
theorem integral_fourierInv_mul_integrable {f g : E → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  simpa [Real.fourierInv_eq, VectorFourier.fourierIntegral, real_inner_comm] using!
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := -innerₗ E)
      Real.continuous_fourierChar continuous_inner.neg hf hg

/-- Fourier inversion almost everywhere needs no continuity hypothesis on
the input. Identification is proved by testing against compact smooth fields. -/
theorem ae_fourierInv_fourier_of_integrable {u : E → ℂ}
    (hu : Integrable u volume) (hF : Integrable (𝓕 u) volume) :
    (𝓕⁻ (𝓕 u)) =ᵐ[volume] u := by
  have hc : Continuous (𝓕⁻ (𝓕 u)) := by
    rw [← Real.Lp.fourierTransformInv_toLp (memLp_one_iff_integrable.mpr hF)]
    exact BoundedContinuousFunction.continuous _
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable hu.locallyIntegrable
  intro φ hφ hcφ
  let ψ : 𝓢(E, ℂ) :=
    (hcφ.comp_left (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have hψ : (ψ : E → ℂ) = fun x => (φ x : ℂ) := rfl
  have he₁ := integral_fourierInv_mul_integrable hF ψ.integrable
  have he₂ := integral_fourier_mul_integrable hu (𝓕⁻ ψ).integrable
  have hinv : ((𝓕⁻ ψ : 𝓢(E, ℂ)) : E → ℂ) = 𝓕⁻ (ψ : E → ℂ) :=
    SchwartzMap.fourierInv_coe ψ
  have hback : 𝓕 (𝓕⁻ (ψ : E → ℂ)) = ψ := by
    rw [← hinv, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rw [hinv, hback] at he₂
  calc
    (∫ x, φ x • (𝓕⁻ (𝓕 u)) x) = ∫ x, (𝓕⁻ (𝓕 u)) x * ψ x := by
      congr 1
      funext x
      simp [hψ, Complex.real_smul, mul_comm]
    _ = ∫ x, 𝓕 u x * 𝓕⁻ (ψ : E → ℂ) x := he₁
    _ = ∫ x, u x * ψ x := he₂
    _ = ∫ x, φ x • u x := by
      congr 1
      funext x
      simp [hψ, Complex.real_smul, mul_comm]

/-- Weighted Fourier L² control above the sharp dimension/order threshold
produces an actual C^k representative of an integrable input. No pointwise
regularity of the input, or pre-existing representative, is a hypothesis. -/
theorem exists_contDiff_representative_of_weighted_fourier
    {u : E → ℂ} (hu : Integrable u volume) {s : ℝ} (k : ℕ)
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - k))
    (hw : MemLp (fun x => (1 + ‖x‖) ^ s * ‖𝓕 u x‖) 2 volume) :
    ∃ g : E → ℂ, ContDiff ℝ k g ∧ g =ᵐ[volume] u := by
  have hFc : Continuous (𝓕 u) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hu)]
    exact BoundedContinuousFunction.continuous _
  have hs0 : (Module.finrank ℝ E : ℝ) < 2 * (s - (0 : ℕ)) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    norm_num only [Nat.cast_zero, sub_zero]
    linarith
  have hi : Integrable (𝓕 u) volume := by
    apply (integrable_norm_iff hFc.aestronglyMeasurable).mp
    simpa using integrable_fourier_moment_of_weightedL2 hFc.aestronglyMeasurable 0 hs0 hw
  exact ⟨𝓕⁻ (𝓕 u), contDiff_fourierInv_of_weightedL2 hFc.aestronglyMeasurable k hs hw,
    ae_fourierInv_fourier_of_integrable hu hi⟩

/-- A single inverse Fourier integral is smooth if the input has sufficient
weighted Fourier L² control for every finite order. Representatives are not
chosen independently for different orders. -/
theorem exists_smooth_representative_of_all_weighted_fourier
    {u : E → ℂ} (hu : Integrable u volume)
    (hw : ∀ k : ℕ, ∃ s : ℝ, (Module.finrank ℝ E : ℝ) < 2 * (s - k) ∧
      MemLp (fun x => (1 + ‖x‖) ^ s * ‖𝓕 u x‖) 2 volume) :
    ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ g =ᵐ[volume] u := by
  have hFc : Continuous (𝓕 u) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hu)]
    exact BoundedContinuousFunction.continuous _
  refine ⟨𝓕⁻ (𝓕 u), contDiff_infty.mpr ?_, ?_⟩
  · intro k
    obtain ⟨s, hs, hws⟩ := hw k
    exact contDiff_fourierInv_of_weightedL2 hFc.aestronglyMeasurable k hs hws
  · obtain ⟨s, hs, hws⟩ := hw 0
    apply ae_fourierInv_fourier_of_integrable hu
    apply (integrable_norm_iff hFc.aestronglyMeasurable).mp
    simpa using integrable_fourier_moment_of_weightedL2 hFc.aestronglyMeasurable 0 hs hws

/-- On L¹ ∩ L², the pointwise Fourier integral is the genuine Plancherel L²
transform almost everywhere. This allows later weak-derivative Fourier
identities to yield L² frequency estimates. -/
theorem ae_fourier_integral_eq_L2_fourier
    (u : Lp ℂ 2 (volume : Measure E)) (hu : Integrable (u : E → ℂ) volume) :
    𝓕 (u : E → ℂ) =ᵐ[volume] ((𝓕 u : Lp ℂ 2 (volume : Measure E)) : E → ℂ) := by
  have hc : Continuous (𝓕 (u : E → ℂ)) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hu)]
    exact BoundedContinuousFunction.continuous _
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    ((Lp.memLp (𝓕 u)).locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  let ψ : 𝓢(E, ℂ) :=
    (hcφ.comp_left (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have hψ : (ψ : E → ℂ) = fun x => (φ x : ℂ) := rfl
  have he := congrArg (fun T : TemperedDistribution E ℂ => T ψ)
    (Lp.fourier_toTemperedDistribution_eq u)
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.fourier_apply,
    SchwartzMap.fourier_coe, smul_eq_mul] at he
  have hp := integral_fourier_mul_integrable ψ.integrable hu
  calc
    (∫ x, φ x • 𝓕 (u : E → ℂ) x) = ∫ x, ψ x * 𝓕 (u : E → ℂ) x := by
      congr 1
    _ = ∫ x, 𝓕 (ψ : E → ℂ) x * u x := hp.symm
    _ = ∫ x, ψ x * (𝓕 u : Lp ℂ 2 (volume : Measure E)) x := he
    _ = ∫ x, φ x • (𝓕 u : Lp ℂ 2 (volume : Measure E)) x := by
      congr 1

/-- The Fourier integral of an L¹ ∩ L² field is L², by Plancherel identification. -/
theorem memLp_fourier_integral_of_integrable_L2
    (u : Lp ℂ 2 (volume : Measure E)) (hu : Integrable (u : E → ℂ) volume) :
    MemLp (𝓕 (u : E → ℂ)) 2 volume :=
  (Lp.memLp (𝓕 u)).ae_eq (ae_fourier_integral_eq_L2_fourier u hu).symm

end AlmostSchur
