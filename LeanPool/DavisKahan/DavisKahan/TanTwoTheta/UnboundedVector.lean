/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.Unbounded
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Unbounded Vector -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Per-vector unbounded tangent two theta

The operator-norm unbounded tangent-two-theta theorem immediately controls the
image of every ambient vector.  This leaf records that consequence separately,
matching the package split between vector and operator-norm statements.

Quarter-acuteness remains explicit.  The sharper continuation-selected result
belongs to the branch-dependent theory.
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

/-- Per-vector unbounded tangent-two-theta estimate for a bounded self-adjoint
perturbation under an explicit spectral gap and quarter-acuteness hypothesis. -/
theorem norm_directedTanTwoAngleOperatorC_apply_le_addBounded_of_spectrum_gap
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
        (addBounded_isSelfAdjoint A hA E hE) S hS))
    (x : H) :
    ‖directedTanTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter x‖ ≤
      ((2 * ‖E‖ / δ) /
        (1 - 2 * Submodule.directedProjectionGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2)) * ‖x‖ := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let V := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
    (addBounded_isSelfAdjoint A hA E hE) S hS
  have hop : ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤
      (2 * ‖E‖ / δ) /
        (1 - 2 * U.directedProjectionGap V ^ 2) :=
    tanTwoTheta_addBounded_of_spectrum_gap
      A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec hquarter
  calc
    ‖directedTanTwoAngleOperatorC U V hquarter x‖ ≤
        ‖directedTanTwoAngleOperatorC U V hquarter‖ * ‖x‖ :=
      (directedTanTwoAngleOperatorC U V hquarter).le_opNorm x
    _ ≤ ((2 * ‖E‖ / δ) /
          (1 - 2 * U.directedProjectionGap V ^ 2)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hop (norm_nonneg x)

/-- Set-localized per-vector form of the unbounded tangent-two-theta estimate. -/
theorem norm_directedTanTwoAngleOperatorC_apply_le_addBounded_of_intervalExterior
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS))
    (x : H) :
    ‖directedTanTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)
        hquarter x‖ ≤
      ((2 * ‖E‖ / δ) /
        (1 - 2 * Submodule.directedProjectionGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2)) * ‖x‖ := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let V := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
    (addBounded_isSelfAdjoint A hA E hE) S hS
  have hop : ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤
      (2 * ‖E‖ / δ) /
        (1 - 2 * U.directedProjectionGap V ^ 2) :=
    tanTwoTheta_addBounded_of_intervalExterior
      A hA E hE B S hB hS hβα hδ hBsub hBcomplDisj hquarter
  calc
    ‖directedTanTwoAngleOperatorC U V hquarter x‖ ≤
        ‖directedTanTwoAngleOperatorC U V hquarter‖ * ‖x‖ :=
      (directedTanTwoAngleOperatorC U V hquarter).le_opNorm x
    _ ≤ ((2 * ‖E‖ / δ) /
          (1 - 2 * U.directedProjectionGap V ^ 2)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hop (norm_nonneg x)

end DavisKahan
end TauCeti
