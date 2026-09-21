/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.SpectralBridge
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.Sylvester.Bounded
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.RCLikeSpectralBridge

/-! # Spectral Bridge -/

open TauCeti.DavisKahan.Sylvester

/-!
# Open obligations of the bounded spectral bridge

The definitions now live in `DavisKahan.SinTheta.SpectralBridge`; the four
estimates below remain unresolved.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Spectral inclusion in an interval gives the centered operator-norm bound. -/
theorem norm_sub_midpoint_le_of_spectrumIn_Icc
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {β α : ℝ} (hβα : β ≤ α)
    (hσ : SpectrumInRealSet A (Set.Icc β α)) :
    ‖A - (((β + α) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E‖
      ≤ (α - β) / 2 := by
  let c : ℝ := (β + α) / 2
  let ρ : ℝ := (α - β) / 2
  have hρ : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hspectrum :
      spectrum 𝕜
          (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ⊆
        Metric.closedBall 0 ρ := by
    intro z hz
    obtain ⟨r, hrA, rfl⟩ :=
      RCLikeSpectralBridge.exists_mem_boundedRealSpectrum_of_mem_spectrum_sub_real_scalar
        hA hz
    obtain ⟨hrβ, hrα⟩ := Set.mem_Icc.mp (hσ hrA)
    rw [Metric.mem_closedBall, dist_zero_right, RCLike.norm_ofReal]
    exact abs_le.mpr ⟨by dsimp [c, ρ] at *; linarith,
      by dsimp [c, ρ] at *; linarith⟩
  have hcenterSelf :
      (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E).IsSymmetric :=
    hA.sub (isSymmetric_real_smul_id c)
  exact RCLikeSpectralBridge.norm_le_of_selfAdjoint_spectrum_subset_closedBall
    hcenterSelf hρ hspectrum

/-- Exterior spectral inclusion makes the centered operator invertible. -/
theorem centered_isUnit_of_spectrumOutside
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hσ : SpectrumInRealSet A {x | x ≤ β - δ ∨ α + δ ≤ x}) :
    ∃ hInv : BoundedInverseData
      (A - (((β + α) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E),
      ‖hInv.inv‖ ≤ ((α - β) / 2 + δ)⁻¹ := by
  let c : ℝ := (β + α) / 2
  let γ : ℝ := (α - β) / 2 + δ
  have hγ : 0 < γ := by dsimp [γ]; linarith
  let T : E →L[𝕜] E :=
    A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  have hTself : T.IsSymmetric :=
    hA.sub (isSymmetric_real_smul_id c)
  have hdist : ∀ z ∈ spectrum 𝕜 T, γ ≤ ‖z‖ := by
    intro z hz
    obtain ⟨r, hrA, rfl⟩ :=
      RCLikeSpectralBridge.exists_mem_boundedRealSpectrum_of_mem_spectrum_sub_real_scalar
        hA hz
    have hr := hσ hrA
    rw [RCLike.norm_ofReal]
    rcases hr with hr | hr
    · rw [abs_of_nonpos (by dsimp [c]; linarith)]
      dsimp [γ, c]
      linarith
    · rw [abs_of_nonneg (by dsimp [c]; linarith)]
      dsimp [γ, c]
      linarith
  have hzero : (0 : 𝕜) ∉ spectrum 𝕜 T := by
    intro h0
    have := hdist 0 h0
    rw [norm_zero] at this
    exact absurd this (not_le_of_gt hγ)
  have hunit : IsUnit T :=
    not_not.mp fun hnu => hzero ((spectrum.zero_mem_iff 𝕜).mpr hnu)
  let hInv := boundedInverseDataOfIsUnit hunit
  refine ⟨hInv, ?_⟩
  have hinvSpectrum :
      spectrum 𝕜 hInv.inv =
        (fun z : 𝕜 => z⁻¹) '' spectrum 𝕜 T :=
    RCLikeSpectralBridge.spectrum_inverse_of_isUnit hunit
  have hinvBound : ∀ z ∈ spectrum 𝕜 hInv.inv, ‖z‖ ≤ γ⁻¹ := by
    intro z hz
    obtain ⟨w, hwT, rfl⟩ := hinvSpectrum ▸ hz
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hγ (hdist w hwT)
  have hInvSelf : (hInv.inv).IsSymmetric :=
    RCLikeSpectralBridge.inverse_isSymmetric hTself hunit
  have hinvBall : spectrum 𝕜 hInv.inv ⊆ Metric.closedBall 0 γ⁻¹ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hinvBound w hw
  simpa [γ] using
    RCLikeSpectralBridge.norm_le_of_selfAdjoint_spectrum_subset_closedBall
      hInvSelf (inv_nonneg.mpr hγ.le) hinvBall

/-- The bounded spectral theorem supplies centered norm/inverse data. -/
noncomputable def centeredIntervalExteriorWitness_of_gap
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B β α δ) :
    CenteredIntervalExteriorWitness A B β α δ := by
  by_cases hL : SpectrumInRealSet A (Set.Icc β α) ∧
      SpectrumInRealSet B {x | x ≤ β - δ ∨ α + δ ≤ x}
  · obtain ⟨hAin, hBout⟩ := hL
    exact .intervalOnLeft
      (norm_sub_midpoint_le_of_spectrumIn_Icc hA hβα hAin)
      (centered_isUnit_of_spectrumOutside hB hβα hδ hBout).choose
      (centered_isUnit_of_spectrumOutside hB hβα hδ hBout).choose_spec
  · obtain ⟨hBin, hAout⟩ := hgap.resolve_left hL
    exact .intervalOnRight
      (norm_sub_midpoint_le_of_spectrumIn_Icc hB hβα hBin)
      (centered_isUnit_of_spectrumOutside hA hβα hδ hAout).choose
      (centered_isUnit_of_spectrumOutside hA hβα hδ hAout).choose_spec

/-- Interval/exterior Sylvester estimate in every rectangular ideal family. -/
theorem sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    {X C : F →L[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B β α δ)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  let c : ℝ := (β + α) / 2
  let ρ : ℝ := (α - β) / 2
  have hρ : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hcenter := centered_sylvester_equation A B X C c hEq
  cases centeredIntervalExteriorWitness_of_gap hA hB hβα hδ hgap with
  | intervalOnLeft hAbound hBinv hBinvBound =>
      exact sylvester_mem_and_gauge_le_of_bound_inverse_swapped
        N hBinv
        (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)
        hρ hδ (by simpa [c, ρ] using hBinvBound)
        (by simpa [c, ρ] using hAbound)
        (by simpa [c] using hcenter) hC
  | intervalOnRight hBbound hAinv hAinvBound =>
      exact sylvester_mem_and_gauge_le_of_bound_inverse
        N hAinv
        (B - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F)
        hρ hδ (by simpa [c, ρ] using hAinvBound)
        (by simpa [c, ρ] using hBbound)
        (by simpa [c] using hcenter) hC

end ExactSinTheta
end DavisKahan
end TauCeti
