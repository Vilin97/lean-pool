/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
public import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.UnboundedIdeal
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm

/-!
# Davis--Kahan 1970, Section 7, at arbitrary rectangular ideal-gauge scope

Section 7 carries the double-angle theorems to an unbounded ambient operator.
These two statements are the `sin 2Theta` and `tan 2Theta` conclusions at the
paper's norm scope -- an arbitrary rectangular ideal gauge rather than the
operator norm -- with the residual taken against a trial subspace of the
domain.
-/

@[expose] public section

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open DavisKahanExt

universe u v

section DoubleAngleSourceWrappers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Source-numbered residual and perturbation form of the sine-double-angle
theorem at arbitrary rectangular ideal-gauge scope. -/
theorem section7_sinTwoTheta_ideal
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
    delta * N.gaugeReal (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
      2 * N.gaugeReal E := by
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem

/-- Source-numbered tangent-double-angle theorem after Section 8 selects the
strict quarter-acute branch.

The bound carries the positive double-cosine denominator
`1 - 2 * directedGap ^ 2` (positive under the quarter-acute hypothesis).  This
factor is intrinsic to `tanTwoThetaIdealBlock = sinTwoThetaIdealBlock ∘L cos⁻¹`;
a bare `2 * N.gaugeReal E` on the right is strictly stronger than the tangent
construction supports, so the denominator is a required part of the statement,
not an artifact. -/
theorem section7_tanTwoTheta_ideal
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
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
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ∧
    delta * N.gaugeReal (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ≤
      (2 * N.gaugeReal E) /
        (1 - 2 * Submodule.directedProjectionGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  exact tanTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem hquarter

end DoubleAngleSourceWrappers
end DavisKahan1970
end TauCeti
