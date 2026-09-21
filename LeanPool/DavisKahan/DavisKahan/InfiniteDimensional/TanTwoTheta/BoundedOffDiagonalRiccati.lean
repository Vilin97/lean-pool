/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessOffDiagonal
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedRiccatiShift

/-! # Bounded Off Diagonal Riccati -/

open TauCeti.DavisKahan.Sylvester

/-!
# Riccati coordinates for an arbitrary quarter-acute reducing graph

This leaf is the geometric-to-analytic bridge for the bounded off-diagonal
`tan 2Theta` theorem.  A quarter-acute pair has a unique contractive ambient
angular operator.  When the target subspace reduces the perturbed operator,
its compressed coordinate solves the bounded Riccati equation.  Reduction of
the unperturbed operator and off-diagonality of the perturbation then identify
the four block entries with the canonical diagonal and cross compressions.

The leaf remains over complex Hilbert spaces, matching the proved bounded
Riccati estimate and operator-angle implementation.  Scalar-generic public
integration is a later compatibility step.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The unique contractive ambient angular operator whose graph is `V`, chosen
from quarter-acuteness of `U` and `V`. -/
noncomputable def quarterAcuteAngularOperator
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    E →L[ℂ] E :=
  Classical.choose
    (existsUnique_contractiveAngularOperator_of_isQuarterAcute U V hquarter)

/-- The chosen quarter-acute graph operator is angular over `U`. -/
theorem quarterAcuteAngularOperator_isAngularOperator
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    IsAngularOperator U (quarterAcuteAngularOperator U V hquarter) :=
  (Classical.choose_spec
    (existsUnique_contractiveAngularOperator_of_isQuarterAcute U V hquarter)).1.1

/-- The graph of the chosen quarter-acute angular operator is exactly `V`. -/
theorem graphSubspace_quarterAcuteAngularOperator
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    graphSubspace U (quarterAcuteAngularOperator U V hquarter) = V :=
  (Classical.choose_spec
    (existsUnique_contractiveAngularOperator_of_isQuarterAcute U V hquarter)).1.2.1

/-- The chosen quarter-acute angular operator is strictly contractive. -/
theorem norm_quarterAcuteAngularOperator_lt_one
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    ‖quarterAcuteAngularOperator U V hquarter‖ < 1 :=
  (Classical.choose_spec
    (existsUnique_contractiveAngularOperator_of_isQuarterAcute U V hquarter)).1.2.2

/-- Coordinate form of the chosen quarter-acute angular operator. -/
noncomputable def quarterAcuteAngularCoordinate
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    U →L[ℂ] Uᗮ :=
  subspaceAngularCoordinate U (quarterAcuteAngularOperator U V hquarter)

omit [CompleteSpace E] in
/-- Compression of an ambient angular operator to `U → Uᗮ` cannot increase its
operator norm. -/
theorem norm_subspaceAngularCoordinate_le
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (X : E →L[ℂ] E) :
    ‖subspaceAngularCoordinate U X‖ ≤ ‖X‖ := by
  have houter := ContinuousLinearMap.opNorm_comp_le
    Uᗮ.orthogonalProjectionOnto (X ∘L U.subtypeL)
  have hinner := ContinuousLinearMap.opNorm_comp_le X U.subtypeL
  calc
    ‖subspaceAngularCoordinate U X‖ =
        ‖Uᗮ.orthogonalProjectionOnto ∘L X ∘L U.subtypeL‖ := rfl
    _ ≤ ‖Uᗮ.orthogonalProjectionOnto‖ * ‖X ∘L U.subtypeL‖ := houter
    _ ≤ ‖Uᗮ.orthogonalProjectionOnto‖ * (‖X‖ * ‖U.subtypeL‖) :=
      mul_le_mul_of_nonneg_left hinner
        (norm_nonneg Uᗮ.orthogonalProjectionOnto)
    _ ≤ 1 * (‖X‖ * ‖U.subtypeL‖) :=
      mul_le_mul_of_nonneg_right Uᗮ.orthogonalProjectionOnto_norm_le
        (mul_nonneg (norm_nonneg X) (norm_nonneg U.subtypeL))
    _ ≤ 1 * (‖X‖ * 1) := by
      gcongr
      exact U.norm_subtypeL_le
    _ = ‖X‖ := by ring

/-- The quarter-acute coordinate angular operator is strictly contractive. -/
theorem norm_quarterAcuteAngularCoordinate_lt_one
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    ‖quarterAcuteAngularCoordinate U V hquarter‖ < 1 :=
  lt_of_le_of_lt
    (norm_subspaceAngularCoordinate_le U
      (quarterAcuteAngularOperator U V hquarter))
    (norm_quarterAcuteAngularOperator_lt_one U V hquarter)

/-- A quarter-acute reducing target supplies a contractive bounded Riccati
solution for the perturbed operator in `U ⊕ Uᗮ` coordinates. -/
theorem quarterAcuteAngularCoordinate_solvesRiccati
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hV : ContinuousLinearMap.Reduces (A + H) V) (hquarter : IsQuarterAcute U V) :
    SolvesRiccati
      (subspaceBlockOperatorData (A + H) U (by
        have h := hA.add hH
        rwa [← ContinuousLinearMap.toLinearMap_add] at h))
      (quarterAcuteAngularCoordinate U V hquarter) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAH : (A + H).IsSymmetric := by
    have h := hA.add hH
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  have hgraphReduces : ContinuousLinearMap.Reduces (A + H)
      (graphSubspace U (quarterAcuteAngularOperator U V hquarter)) := by
    rw [graphSubspace_quarterAcuteAngularOperator U V hquarter]
    exact hV
  exact subspaceAngularCoordinate_solvesRiccati_of_graph_reduces
    (A + H) U hAH
    (quarterAcuteAngularOperator U V hquarter)
    (quarterAcuteAngularOperator_isAngularOperator U V hquarter)
    hgraphReduces

omit [CompleteSpace E] in
/-- The upper-right coordinate compression of an ambient operator has norm at
most the ambient operator norm. -/
theorem norm_upperRightSubspaceCompression_le
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (H : E →L[ℂ] E) :
    ‖U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL‖ ≤ ‖H‖ := by
  have houter := ContinuousLinearMap.opNorm_comp_le
    U.orthogonalProjectionOnto (H ∘L Uᗮ.subtypeL)
  have hinner := ContinuousLinearMap.opNorm_comp_le H Uᗮ.subtypeL
  calc
    ‖U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL‖ ≤
        ‖U.orthogonalProjectionOnto‖ * ‖H ∘L Uᗮ.subtypeL‖ := houter
    _ ≤ ‖U.orthogonalProjectionOnto‖ * (‖H‖ * ‖Uᗮ.subtypeL‖) :=
      mul_le_mul_of_nonneg_left hinner
        (norm_nonneg U.orthogonalProjectionOnto)
    _ ≤ 1 * (‖H‖ * ‖Uᗮ.subtypeL‖) :=
      mul_le_mul_of_nonneg_right U.orthogonalProjectionOnto_norm_le
        (mul_nonneg (norm_nonneg H) (norm_nonneg Uᗮ.subtypeL))
    _ ≤ 1 * (‖H‖ * 1) := by
      gcongr
      exact Uᗮ.norm_subtypeL_le
    _ = ‖H‖ := by ring

/-- Canonical block identities for an off-diagonal perturbation relative to a
reducing subspace of the unperturbed operator. -/
theorem subspaceBlockOperatorData_add_offDiagonal_components
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : A.Reduces U) (hoff : Submodule.IsOffDiagonal U H) :
    let hAH : (A + H).IsSymmetric := by
      have h := hA.add hH
      rwa [← ContinuousLinearMap.toLinearMap_add] at h
    (subspaceBlockOperatorData (A + H) U hAH).A0 = compressOperator U A ∧
    (subspaceBlockOperatorData (A + H) U hAH).A1 = compressOperator Uᗮ A ∧
    (subspaceBlockOperatorData (A + H) U hAH).B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL ∧
    (subspaceBlockOperatorData (A + H) U hAH).B10 =
      Uᗮ.orthogonalProjectionOnto ∘L H ∘L U.subtypeL := by
  dsimp only
  have hAH : (A + H).IsSymmetric := by
    have h := hA.add hH
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  exact ⟨
    subspaceBlockOperatorData_A0_add_offDiagonal A H U hAH hoff,
    subspaceBlockOperatorData_A1_add_offDiagonal A H U hAH hoff,
    subspaceBlockOperatorData_B01_add_of_reduces A H U hAH hU,
    subspaceBlockOperatorData_B10_add_of_reduces A H U hAH hU⟩

/-- The upper-right block of the canonical off-diagonal coordinate data is
controlled by the perturbation norm. -/
theorem norm_subspaceBlockOperatorData_B01_add_offDiagonal_le
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : A.Reduces U) :
    let hAH : (A + H).IsSymmetric := by
      have h := hA.add hH
      rwa [← ContinuousLinearMap.toLinearMap_add] at h
    ‖(subspaceBlockOperatorData (A + H) U hAH).B01‖ ≤ ‖H‖ := by
  dsimp only
  have hAH : (A + H).IsSymmetric := by
    have h := hA.add hH
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  rw [subspaceBlockOperatorData_B01_add_of_reduces A H U hAH hU]
  exact norm_upperRightSubspaceCompression_le U H

end DavisKahanExt
end TauCeti
