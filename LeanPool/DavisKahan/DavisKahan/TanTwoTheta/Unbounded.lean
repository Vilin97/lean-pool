/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.BoundedOffDiagonal
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Unbounded -/

open TauCeti.DavisKahan.Angle


/-!
# Unbounded tangent two theta at operator-norm scope

This leaf combines the unbounded bounded-perturbation sine-two-theta theorem
with the quarter-acute inversion estimate for the complex double-angle cosine.
The conclusion is an operator-norm tangent bound with the explicit cosine
denominator.

This is the first unbounded tangent-two-theta endpoint.  It deliberately keeps
quarter-acuteness as a hypothesis and does not claim the sharper selected
Riccati estimate or an ideal-gauge analogue.
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

omit [CompleteSpace H] in
/-- Quarter-acuteness makes the double-angle cosine denominator strictly
positive: `1 - 2 * directedGap U V ^ 2 > 0`.

Stated non-privately because the ideal-theoretic companion in
`TanTwoTheta/UnboundedIdeal.lean` needs exactly this fact, and `private` had
previously forced a byte-identical copy there. -/
theorem doubleCosineDenominator_pos
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    0 < 1 - 2 * U.directedProjectionGap V ^ 2 := by
  have hglt : U.directedProjectionGap V < Real.sqrt 2 / 2 :=
    lt_of_le_of_lt (Submodule.directedProjectionGap_le_projectionGap U V) hquarter
  have hg0 : 0 ≤ U.directedProjectionGap V := by
    rw [show U.directedProjectionGap V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- Canonical unbounded operator-norm tangent-two-theta estimate for a bounded
self-adjoint perturbation, under an explicit quarter-acuteness hypothesis. -/
theorem tanTwoTheta_addBounded_of_spectrum_gap
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
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    ‖directedTanTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter‖ ≤
      (2 * ‖E‖ / δ) /
        (1 - 2 * Submodule.directedProjectionGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let V := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
    (addBounded_isSelfAdjoint A hA E hE) S hS
  have hsin : δ * ‖directedSinTwoAngleOperatorC U V‖ ≤ 2 * ‖E‖ :=
    sinTwoTheta_addBounded_of_spectrum_gap
      A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec
  have hsinDiv : ‖directedSinTwoAngleOperatorC U V‖ ≤ 2 * ‖E‖ / δ := by
    rw [le_div_iff₀ hδ]
    simpa only [mul_comm] using hsin
  have hden : 0 < 1 - 2 * U.directedProjectionGap V ^ 2 :=
    doubleCosineDenominator_pos U V hquarter
  calc
    ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤
        ‖directedSinTwoAngleOperatorC U V‖ /
          (1 - 2 * U.directedProjectionGap V ^ 2) :=
      norm_directedTanTwoAngleOperatorC_le_sine_div_doubleCosine U V hquarter
    _ ≤ (2 * ‖E‖ / δ) /
          (1 - 2 * U.directedProjectionGap V ^ 2) :=
      div_le_div_of_nonneg_right hsinDiv hden.le

/-- Set-localized form of the unbounded operator-norm tangent-two-theta
estimate. -/
theorem tanTwoTheta_addBounded_of_intervalExterior
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    ‖directedTanTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter‖ ≤
      (2 * ‖E‖ / δ) /
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
  exact tanTwoTheta_addBounded_of_spectrum_gap
    A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec hquarter

end DavisKahan
end TauCeti
