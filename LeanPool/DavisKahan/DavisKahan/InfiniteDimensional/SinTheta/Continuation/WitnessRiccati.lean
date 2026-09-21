/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessGraph
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedReduction
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum

/-! # Witness Riccati -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Riccati coordinates of the continuation-selected graph

A continuation witness selects an ambient angular operator on the source
spectral subspace.  The bounded Riccati theory, however, is formulated on the
Hilbert direct sum of a subspace and its orthogonal complement.  This leaf
constructs the corresponding compressed block data and proves the coordinate
Riccati equation directly from reduction of the ambient graph.

The proof deliberately avoids first proving a global unitary equivalence
between the ambient space and the `WithLp` direct sum.  Instead it applies the
ambient operator to a graph vector, uses graph invariance, and projects the
result onto the two orthogonal coordinates.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan

open scoped InnerProductSpace

universe v

section AmbientBlockCoordinates

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The bounded self-adjoint block data of an ambient self-adjoint operator
relative to `U ⊕ Uᗮ`. -/
noncomputable def subspaceBlockOperatorData
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) :
    BlockOperatorData (𝕜 := ℂ) (E0 := U) (E1 := Uᗮ) := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact
    { A0 := compressOperator U T
      A1 := compressOperator Uᗮ T
      B01 := U.orthogonalProjectionOnto ∘L T ∘L Uᗮ.subtypeL
      B10 := Uᗮ.orthogonalProjectionOnto ∘L T ∘L U.subtypeL
      selfAdjoint0 := by
        exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (isSelfAdjoint_compressOperator
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT) U)
      selfAdjoint1 := by
        exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (isSelfAdjoint_compressOperator
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT) Uᗮ)
      offDiagonalAdjoint := by
        intro x y
        change
          ⟪U.starProjection (T (y : H)), (x : H)⟫_ℂ =
            ⟪(y : H), Uᗮ.starProjection (T (x : H))⟫_ℂ
        calc
          ⟪U.starProjection (T (y : H)), (x : H)⟫_ℂ =
              ⟪T (y : H), U.starProjection (x : H)⟫_ℂ :=
            U.inner_starProjection_left_eq_right (T (y : H)) (x : H)
          _ = ⟪T (y : H), (x : H)⟫_ℂ := by
            rw [Submodule.starProjection_eq_self_iff.mpr x.property]
          _ = ⟪(y : H), T (x : H)⟫_ℂ := hT (y : H) (x : H)
          _ = ⟪Uᗮ.starProjection (y : H), T (x : H)⟫_ℂ := by
            rw [Submodule.starProjection_eq_self_iff.mpr y.property]
          _ = ⟪(y : H), Uᗮ.starProjection (T (x : H))⟫_ℂ :=
            Uᗮ.inner_starProjection_left_eq_right (y : H) (T (x : H)) }

/-- Coordinate form `U → Uᗮ` of an ambient angular operator. -/
noncomputable def subspaceAngularCoordinate
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (X : H →L[ℂ] H) : U →L[ℂ] Uᗮ :=
  Uᗮ.orthogonalProjectionOnto ∘L X ∘L U.subtypeL

omit [CompleteSpace H] in
/-- The angular coordinate of an angular operator agrees with `X` on underlying vectors. -/
@[simp]
theorem coe_subspaceAngularCoordinate_apply
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (X : H →L[ℂ] H) (hX : IsAngularOperator U X) (u : U) :
    (((subspaceAngularCoordinate U X) u : Uᗮ) : H) = X (u : H) := by
  have hPX : U.starProjection (X (u : H)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using
      ContinuousLinearMap.ext_iff.mp hX.2 (u : H)
  have hmem : X (u : H) ∈ Uᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff U).mp hPX
  change Uᗮ.starProjection (X (u : H)) = X (u : H)
  exact Submodule.starProjection_eq_self_iff.mpr hmem

omit [CompleteSpace H] in
/-- Membership in an angular graph is equivalent to the complementary
coordinate being the angular operator applied to the base coordinate. -/
theorem starProjection_orthogonal_eq_of_mem_graphSubspace
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (X : H →L[ℂ] H) (hX : IsAngularOperator U X)
    {z : H} (hz : z ∈ graphSubspace U X) :
    Uᗮ.starProjection z = X (U.starProjection z) := by
  rw [graphSubspace_eq_range U hX] at hz
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
  change U.starProjection w + X (U.starProjection w) = z at hw
  have hPidem : U.starProjection (U.starProjection w) = U.starProjection w :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem w)
  have hPX : U.starProjection (X (U.starProjection w)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using
      ContinuousLinearMap.ext_iff.mp hX.2 (U.starProjection w)
  have hQPw : Uᗮ.starProjection (U.starProjection w) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply, hPidem, sub_self]
  have hQX : Uᗮ.starProjection (X (U.starProjection w)) =
      X (U.starProjection w) := by
    rw [Submodule.starProjection_orthogonal_apply, hPX, sub_zero]
  rw [← hw, map_add, map_add, hQPw, hQX, hPidem, hPX, zero_add, add_zero]

/-- If an ambient angular graph reduces a bounded self-adjoint operator, then
its compressed coordinate operator solves the bounded Riccati equation for the
corresponding subspace block data. -/
theorem subspaceAngularCoordinate_solvesRiccati_of_graph_reduces
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric)
    (X : H →L[ℂ] H) (hX : IsAngularOperator U X)
    (hred : T.Reduces (graphSubspace U X)) :
    SolvesRiccati (subspaceBlockOperatorData T U hT)
      (subspaceAngularCoordinate U X) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  refine (solvesRiccati_iff_pointwise
    (subspaceBlockOperatorData T U hT)
    (subspaceAngularCoordinate U X)).2 ?_
  intro u
  have hgraph : (u : H) + X (u : H) ∈ graphSubspace U X := by
    rw [graphSubspace_eq_range U hX]
    apply LinearMap.mem_range.mpr
    refine ⟨(u : H), ?_⟩
    change U.starProjection (u : H) + X (U.starProjection (u : H)) =
      (u : H) + X (u : H)
    rw [Submodule.starProjection_eq_self_iff.mpr u.property]
  have hout : T ((u : H) + X (u : H)) ∈ graphSubspace U X :=
    hred.1 _ hgraph
  have hcoord := starProjection_orthogonal_eq_of_mem_graphSubspace
    U X hX hout
  apply Subtype.ext
  simp only [subspaceBlockOperatorData, compressOperator,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.coe_add,
    Submodule.coe_orthogonalProjectionOnto_apply,
    coe_subspaceAngularCoordinate_apply U X hX, map_add]
  simpa only [map_add] using hcoord

end AmbientBlockCoordinates

section WitnessRiccati

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

namespace SpectralContinuationWitness

/-- The coordinate compression of the witness-selected endpoint angular
operator solves the bounded Riccati equation for `A + V` relative to the source
selected spectral splitting. -/
theorem selectedEndpointAngularCoordinate_solvesRiccati
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    SolvesRiccati
      (subspaceBlockOperatorData (A + V) C.sourceSelectedSpectralSubspace
        C.targetSeparatingContour.selfAdjoint)
      (subspaceAngularCoordinate C.sourceSelectedSpectralSubspace
        (C.selectedEndpointAngularOperator hsmall)) := by
  let : CompleteSpace C.sourceSelectedSpectralSubspace :=
    (C.sourceSelectedSpectralSubspace.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace
      (C.sourceSelectedSpectralSubspaceᗮ : Submodule ℂ H) :=
    (C.sourceSelectedSpectralSubspaceᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact subspaceAngularCoordinate_solvesRiccati_of_graph_reduces
    (A + V) C.sourceSelectedSpectralSubspace
    C.targetSeparatingContour.selfAdjoint
    (C.selectedEndpointAngularOperator hsmall)
    (C.selectedEndpointAngularOperator_isAngularOperator hsmall)
    (C.selectedEndpointAngularOperator_graph_reduces hsmall)

end SpectralContinuationWitness

end WitnessRiccati

end DavisKahanExt
end TauCeti
