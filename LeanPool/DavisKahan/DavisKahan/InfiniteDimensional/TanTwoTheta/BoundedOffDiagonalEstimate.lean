/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalRiccati
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Estimate -/

open TauCeti.DavisKahan.Sylvester

/-!
# Sharp Riccati estimate in ambient off-diagonal coordinates

This leaf composes the quarter-acute graph/Riccati bridge with the sharp
centered quadratic-form estimate.  Once the two diagonal compressions of the
unperturbed operator satisfy an ordered form gap of width `d`, the coordinate
angular operator satisfies the sharp contractive Riccati inequality with the
ambient perturbation norm on the right.

The remaining bounded `tan 2Theta` work is geometric: obtain these form bounds
from `OrderedInternalGap`, then identify the scalar Riccati expression with the
implemented double-angle operator.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The quarter-acute coordinate graph satisfies the sharp Riccati inequality
under an ordered centered quadratic-form gap for the two diagonal
compressions. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_form_gap
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {c d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : U,
      RCLike.re ⟪compressOperator U A z, z⟫_ℂ ≤ c * ‖z‖ ^ 2)
    (hA1 : ∀ z : Uᗮ,
      (c + d) * ‖z‖ ^ 2 ≤
        RCLike.re ⟪compressOperator Uᗮ A z, z⟫_ℂ)
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAH : (A + H).IsSymmetric := by
    have h := hA.add hH
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  let B : BlockOperatorData (𝕜 := ℂ) (E0 := U) (E1 := Uᗮ) :=
    subspaceBlockOperatorData (A + H) U hAH
  let X : U →L[ℂ] Uᗮ := quarterAcuteAngularCoordinate U V hquarter
  have hsolve : SolvesRiccati B X := by
    simpa [B, X] using
      quarterAcuteAngularCoordinate_solvesRiccati A H hA hH U V hV hquarter
  have hB0 : B.A0 = compressOperator U A := by
    simpa [B] using
      subspaceBlockOperatorData_A0_add_offDiagonal A H U hAH hoff
  have hB1 : B.A1 = compressOperator Uᗮ A := by
    simpa [B] using
      subspaceBlockOperatorData_A1_add_offDiagonal A H U hAH hoff
  have hB01 : B.B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL := by
    simpa [B] using
      subspaceBlockOperatorData_B01_add_of_reduces A H U hAH hU
  have hB0form : ∀ z : U,
      RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2 := by
    intro z
    rw [hB0]
    exact hA0 z
  have hB1form : ∀ z : Uᗮ,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ := by
    intro z
    rw [hB1]
    exact hA1 z
  have hXcontractive : ‖X‖ < 1 := by
    simpa [X] using norm_quarterAcuteAngularCoordinate_lt_one U V hquarter
  have hsharp : d * ‖X‖ ≤ ‖B.B01‖ * (1 - ‖X‖ ^ 2) :=
    sharp_riccati_norm_bound_of_form_gap B hd.le hB0form hB1form
      hsolve hXcontractive
  have hcoupling : ‖B.B01‖ ≤ ‖H‖ := by
    rw [hB01]
    exact norm_upperRightSubspaceCompression_le U H
  have hfactor : 0 ≤ 1 - ‖X‖ ^ 2 := by
    nlinarith [norm_nonneg X, hXcontractive]
  calc
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ = d * ‖X‖ := by rfl
    _ ≤ ‖B.B01‖ * (1 - ‖X‖ ^ 2) := hsharp
    _ ≤ ‖H‖ * (1 - ‖X‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcoupling hfactor
    _ = ‖H‖ *
        (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by rfl

end DavisKahanExt
end TauCeti
