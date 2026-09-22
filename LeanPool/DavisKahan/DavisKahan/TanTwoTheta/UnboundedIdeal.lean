/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.Unbounded
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Unbounded Ideal -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Ideal-gauge unbounded tangent two theta

The existing unbounded ideal theorem controls the reflected complementary
sine-two-theta overlap block.  At ideal scope that block, rather than the
functional-calculus sine operator itself, is the object whose membership has
been established.  We therefore define its tangent companion by composing on
the right with the inverse extended double-angle cosine.

This construction gives genuine rectangular-ideal membership and the expected
quarter-acute gauge denominator.  It does not claim an unavailable equality
between this reflected-overlap companion and `directedTanTwoAngleOperatorC`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ideal-theoretic tangent-two-theta companion of the reflected
complementary overlap block. -/
noncomputable def tanTwoThetaIdealBlock
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) : H →L[ℂ] H :=
  sinTwoThetaIdealBlock U V ∘L
    (cosTwoAngleExtendedCEquiv U V hquarter).symm.toContinuousLinearMap

/-- Right composition with the inverse extended double-angle cosine preserves
rectangular ideal membership and introduces only the quarter-angle cosine
denominator in the gauge. -/
theorem tanTwoThetaIdealBlock_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V)
    (hsin : N.Mem (sinTwoThetaIdealBlock U V)) :
    N.Mem (tanTwoThetaIdealBlock U V hquarter) ∧
      N.gaugeReal (tanTwoThetaIdealBlock U V hquarter) ≤
        N.gaugeReal (sinTwoThetaIdealBlock U V) /
          (1 - 2 * U.directedProjectionGap V ^ 2) := by
  let R : H →L[ℂ] H :=
    (cosTwoAngleExtendedCEquiv U V hquarter).symm.toContinuousLinearMap
  have hRnorm : ‖R‖ ≤ (1 - 2 * U.directedProjectionGap V ^ 2)⁻¹ := by
    simpa only [R] using
      norm_cosTwoAngleExtendedCEquiv_symm_le U V hquarter
  have hmem : N.Mem (sinTwoThetaIdealBlock U V ∘L R) :=
    N.comp_right_mem R hsin
  have hgauge :
      N.gaugeReal (sinTwoThetaIdealBlock U V ∘L R) ≤
        N.gaugeReal (sinTwoThetaIdealBlock U V) * ‖R‖ :=
    N.gaugeReal_comp_right_le_mul R hsin
  refine ⟨?_, ?_⟩
  · simpa only [tanTwoThetaIdealBlock, R] using hmem
  · change N.gaugeReal (sinTwoThetaIdealBlock U V ∘L R) ≤ _
    calc
      N.gaugeReal (sinTwoThetaIdealBlock U V ∘L R) ≤
          N.gaugeReal (sinTwoThetaIdealBlock U V) * ‖R‖ := hgauge
      _ ≤ N.gaugeReal (sinTwoThetaIdealBlock U V) *
          (1 - 2 * U.directedProjectionGap V ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hRnorm (N.gaugeReal_nonneg hsin)
      _ = N.gaugeReal (sinTwoThetaIdealBlock U V) /
          (1 - 2 * U.directedProjectionGap V ^ 2) := by
        rw [div_eq_mul_inv]

/-- Canonical bounded-perturbation unbounded tangent-two-theta theorem at
rectangular ideal-gauge scope, under explicit quarter-acuteness. -/
theorem tanTwoTheta_addBounded_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ∧
      δ * N.gaugeReal (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ≤
        (2 * N.gaugeReal E) /
          (1 - 2 * Submodule.directedProjectionGap
            (selfAdjointSpectralSubspace A hA B hB)
            (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
              (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let V := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
    (addBounded_isSelfAdjoint A hA E hE) S hS
  have hsin := sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec hEmem
  have htan := tanTwoThetaIdealBlock_mem_and_gauge_le
    N U V hquarter hsin.1
  have hden : 0 < 1 - 2 * U.directedProjectionGap V ^ 2 :=
    doubleCosineDenominator_pos U V hquarter
  refine ⟨htan.1, ?_⟩
  calc
    δ * N.gaugeReal (tanTwoThetaIdealBlock U V hquarter) ≤
        δ * (N.gaugeReal (sinTwoThetaIdealBlock U V) /
          (1 - 2 * U.directedProjectionGap V ^ 2)) :=
      mul_le_mul_of_nonneg_left htan.2 hδ.le
    _ = (δ * N.gaugeReal (sinTwoThetaIdealBlock U V)) /
          (1 - 2 * U.directedProjectionGap V ^ 2) := by ring
    _ ≤ (2 * N.gaugeReal E) /
          (1 - 2 * U.directedProjectionGap V ^ 2) :=
      div_le_div_of_nonneg_right hsin.2 hden.le

/-- Set-localized rectangular ideal-gauge form of unbounded tangent two theta. -/
theorem tanTwoTheta_addBounded_gauge_of_intervalExterior
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ∧
      δ * N.gaugeReal (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ≤
        (2 * N.gaugeReal E) /
          (1 - 2 * Submodule.directedProjectionGap
            (selfAdjointSpectralSubspace A hA B hB)
            (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
              (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  obtain ⟨hBlow, hBhigh⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hBcomplSpec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA Bᶜ hB.compl hBcomplDisj
  exact tanTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec
      hEmem hquarter

/-- Source-facing unitary-invariant-family wrapper for the spectrum-gap ideal
form. -/
theorem tanTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ∧
      δ * N.gauge (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ≤
        (2 * N.gauge E) /
          (1 - 2 * Submodule.directedProjectionGap
            (selfAdjointSpectralSubspace A hA B hB)
            (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
              (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  exact tanTwoTheta_addBounded_gauge_of_spectrum_gap
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBlow hBhigh hBcomplSpec hEmem hquarter

/-- Source-facing unitary-invariant-family wrapper for the set-localized ideal
form. -/
theorem tanTwoTheta_addBounded_unitaryInvariant_of_intervalExterior
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ∧
      δ * N.gauge (tanTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter) ≤
        (2 * N.gauge E) /
          (1 - 2 * Submodule.directedProjectionGap
            (selfAdjointSpectralSubspace A hA B hB)
            (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
              (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  exact tanTwoTheta_addBounded_gauge_of_intervalExterior
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBsub hBcomplDisj hEmem hquarter

end DavisKahan
end TauCeti
