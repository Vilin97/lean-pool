/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessRiccati

/-! # Witness Off Diagonal -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Off-diagonal block coordinates of the continuation-selected Riccati equation

The witness-selected endpoint graph already yields a contractive bounded
Riccati solution for the full perturbed operator `A + V`.  For the
Davis--Kahan application, the source selected spectral subspace reduces `A`
and `V` is off-diagonal relative to that splitting.  Consequently the four
compressed blocks separate cleanly: the diagonal blocks come from `A`, and
the cross blocks come from `V`.

This leaf proves those identities without identifying whole
`BlockOperatorData` structures.  Keeping the field equalities separate avoids
transport through proof-valued self-adjointness fields and gives downstream
norm and spectral estimates direct rewrite lemmas.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan

open Set
open scoped InnerProductSpace

universe v

section OffDiagonalCompression

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- The selected diagonal projection of an off-diagonal operator vanishes on
vectors in the selected subspace. -/
theorem starProjection_map_eq_zero_of_isOffDiagonal
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (V : H →L[ℂ] H) (hoff : Submodule.IsOffDiagonal U V)
    {u : H} (hu : u ∈ U) :
    U.starProjection (V u) = 0 := by
  change U.diagonalPart V = 0 at hoff
  have hdiag := congrArg (fun T : H →L[ℂ] H => T u) hoff
  have hQu : Uᗮ.starProjection u = 0 := by
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr hu, sub_self]
  simpa only [Submodule.diagonalPart, ContinuousLinearMap.comp_apply,
    add_apply, zero_apply, Submodule.starProjection_eq_self_iff.mpr hu,
    hQu, map_zero, add_zero] using hdiag

omit [CompleteSpace H] in
/-- The complementary diagonal projection of an off-diagonal operator
vanishes on vectors in the orthogonal complement. -/
theorem starProjection_orthogonal_map_eq_zero_of_isOffDiagonal
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (V : H →L[ℂ] H) (hoff : Submodule.IsOffDiagonal U V)
    {w : H} (hw : w ∈ Uᗮ) :
    Uᗮ.starProjection (V w) = 0 := by
  change U.diagonalPart V = 0 at hoff
  have hdiag := congrArg (fun T : H →L[ℂ] H => T w) hoff
  have hPw : U.starProjection w = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).2 hw
  have hQw : Uᗮ.starProjection w = w :=
    Submodule.starProjection_eq_self_iff.mpr hw
  simpa only [Submodule.diagonalPart, ContinuousLinearMap.comp_apply,
    add_apply, zero_apply, hPw, hQw, map_zero, zero_add] using hdiag

/-- In the source subspace, the diagonal block of `A + V` is just the
compression of `A` when `V` is off-diagonal. -/
theorem subspaceBlockOperatorData_A0_add_offDiagonal
    (A V : H →L[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection]
    (hAV : (A + V).IsSymmetric)
    (hoff : Submodule.IsOffDiagonal U V) :
    (subspaceBlockOperatorData (A + V) U hAV).A0 =
      compressOperator U A := by
  change compressOperator U (A + V) = compressOperator U A
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  simp only [compressOperator, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_add,
    Submodule.coe_orthogonalProjectionOnto_apply, add_apply, map_add]
  rw [starProjection_map_eq_zero_of_isOffDiagonal U V hoff u.property,
    add_zero]

/-- In the complementary subspace, the diagonal block of `A + V` is just the
compression of `A` when `V` is off-diagonal. -/
theorem subspaceBlockOperatorData_A1_add_offDiagonal
    (A V : H →L[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection]
    (hAV : (A + V).IsSymmetric)
    (hoff : Submodule.IsOffDiagonal U V) :
    (subspaceBlockOperatorData (A + V) U hAV).A1 =
      compressOperator Uᗮ A := by
  change compressOperator Uᗮ (A + V) = compressOperator Uᗮ A
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  simp only [compressOperator, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_add,
    Submodule.coe_orthogonalProjectionOnto_apply, add_apply, map_add]
  rw [starProjection_orthogonal_map_eq_zero_of_isOffDiagonal
    U V hoff w.property, add_zero]

/-- The upper-right block of `A + V` is the upper-right block of `V` when `U`
reduces `A`. -/
theorem subspaceBlockOperatorData_B01_add_of_reduces
    (A V : H →L[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection]
    (hAV : (A + V).IsSymmetric)
    (hU : A.Reduces U) :
    (subspaceBlockOperatorData (A + V) U hAV).B01 =
      U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL := by
  change
    U.orthogonalProjectionOnto ∘L (A + V) ∘L Uᗮ.subtypeL =
      U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  have hAw : A (w : H) ∈ Uᗮ := hU.2 (w : H) w.property
  have hPAw : U.starProjection (A (w : H)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).2 hAw
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.coe_add,
    Submodule.coe_orthogonalProjectionOnto_apply, add_apply, map_add,
    hPAw, zero_add]

/-- The lower-left block of `A + V` is the lower-left block of `V` when `U`
reduces `A`. -/
theorem subspaceBlockOperatorData_B10_add_of_reduces
    (A V : H →L[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection]
    (hAV : (A + V).IsSymmetric)
    (hU : A.Reduces U) :
    (subspaceBlockOperatorData (A + V) U hAV).B10 =
      Uᗮ.orthogonalProjectionOnto ∘L V ∘L U.subtypeL := by
  change
    Uᗮ.orthogonalProjectionOnto ∘L (A + V) ∘L U.subtypeL =
      Uᗮ.orthogonalProjectionOnto ∘L V ∘L U.subtypeL
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  have hAu : A (u : H) ∈ U := hU.1 (u : H) u.property
  have hQAu : Uᗮ.starProjection (A (u : H)) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr hAu, sub_self]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.coe_add,
    Submodule.coe_orthogonalProjectionOnto_apply, add_apply, map_add,
    hQAu, zero_add]

end OffDiagonalCompression

section WitnessOffDiagonal

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

namespace SpectralContinuationWitness

/-- The source selected spectral subspace reduces the unperturbed operator. -/
theorem sourceSelectedSpectralSubspace_reduces
    (C : SpectralContinuationWitness A V s) :
    A.Reduces C.sourceSelectedSpectralSubspace := by
  unfold sourceSelectedSpectralSubspace
  exact boundedSelfAdjointSpectralSubspace_reduces A
    C.sourceSeparatingContour.selfAdjoint s
    C.sourceSeparatingContour.measurable_selected

/-- The selected endpoint block data has the unperturbed source compression as
its first diagonal block. -/
theorem selectedEndpointBlockData_A0_eq
    (C : SpectralContinuationWitness A V s)
    (hoff : Submodule.IsOffDiagonal C.sourceSelectedSpectralSubspace V) :
    (subspaceBlockOperatorData (A + V) C.sourceSelectedSpectralSubspace
      C.targetSeparatingContour.selfAdjoint).A0 =
      compressOperator C.sourceSelectedSpectralSubspace A :=
  subspaceBlockOperatorData_A0_add_offDiagonal A V
    C.sourceSelectedSpectralSubspace
    C.targetSeparatingContour.selfAdjoint hoff

/-- The selected endpoint block data has the unperturbed complementary
compression as its second diagonal block. -/
theorem selectedEndpointBlockData_A1_eq
    (C : SpectralContinuationWitness A V s)
    (hoff : Submodule.IsOffDiagonal C.sourceSelectedSpectralSubspace V) :
    (subspaceBlockOperatorData (A + V) C.sourceSelectedSpectralSubspace
      C.targetSeparatingContour.selfAdjoint).A1 =
      compressOperator C.sourceSelectedSpectralSubspaceᗮ A :=
  subspaceBlockOperatorData_A1_add_offDiagonal A V
    C.sourceSelectedSpectralSubspace
    C.targetSeparatingContour.selfAdjoint hoff

/-- The selected endpoint upper-right block is the corresponding compression
of the off-diagonal perturbation. -/
theorem selectedEndpointBlockData_B01_eq
    (C : SpectralContinuationWitness A V s) :
    (subspaceBlockOperatorData (A + V) C.sourceSelectedSpectralSubspace
      C.targetSeparatingContour.selfAdjoint).B01 =
      C.sourceSelectedSpectralSubspace.orthogonalProjectionOnto ∘L V ∘L
        C.sourceSelectedSpectralSubspaceᗮ.subtypeL :=
  subspaceBlockOperatorData_B01_add_of_reduces A V
    C.sourceSelectedSpectralSubspace
    C.targetSeparatingContour.selfAdjoint
    C.sourceSelectedSpectralSubspace_reduces

/-- The selected endpoint lower-left block is the corresponding compression
of the off-diagonal perturbation. -/
theorem selectedEndpointBlockData_B10_eq
    (C : SpectralContinuationWitness A V s) :
    (subspaceBlockOperatorData (A + V) C.sourceSelectedSpectralSubspace
      C.targetSeparatingContour.selfAdjoint).B10 =
      C.sourceSelectedSpectralSubspaceᗮ.orthogonalProjectionOnto ∘L V ∘L
        C.sourceSelectedSpectralSubspace.subtypeL :=
  subspaceBlockOperatorData_B10_add_of_reduces A V
    C.sourceSelectedSpectralSubspace
    C.targetSeparatingContour.selfAdjoint
    C.sourceSelectedSpectralSubspace_reduces

/-- Canonical off-diagonal coordinate form of the Riccati equation solved by
the continuation-selected angular operator. -/
theorem selectedEndpointAngularCoordinate_offDiagonal_riccati
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2)
    (hoff : Submodule.IsOffDiagonal C.sourceSelectedSpectralSubspace V) :
    ∀ u : C.sourceSelectedSpectralSubspace,
      (C.sourceSelectedSpectralSubspaceᗮ.orthogonalProjectionOnto ∘L V ∘L
          C.sourceSelectedSpectralSubspace.subtypeL) u +
          compressOperator C.sourceSelectedSpectralSubspaceᗮ A
            ((subspaceAngularCoordinate C.sourceSelectedSpectralSubspace
              (C.selectedEndpointAngularOperator hsmall)) u) =
        (subspaceAngularCoordinate C.sourceSelectedSpectralSubspace
          (C.selectedEndpointAngularOperator hsmall))
          (compressOperator C.sourceSelectedSpectralSubspace A u +
            (C.sourceSelectedSpectralSubspace.orthogonalProjectionOnto ∘L V ∘L
              C.sourceSelectedSpectralSubspaceᗮ.subtypeL)
              ((subspaceAngularCoordinate C.sourceSelectedSpectralSubspace
                (C.selectedEndpointAngularOperator hsmall)) u)) := by
  let : CompleteSpace C.sourceSelectedSpectralSubspace :=
    (C.sourceSelectedSpectralSubspace.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace
      (C.sourceSelectedSpectralSubspaceᗮ : Submodule ℂ H) :=
    (C.sourceSelectedSpectralSubspaceᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  intro u
  have hpoint := (solvesRiccati_iff_pointwise
    (subspaceBlockOperatorData (A + V) C.sourceSelectedSpectralSubspace
      C.targetSeparatingContour.selfAdjoint)
    (subspaceAngularCoordinate C.sourceSelectedSpectralSubspace
      (C.selectedEndpointAngularOperator hsmall))).1
    (C.selectedEndpointAngularCoordinate_solvesRiccati hsmall) u
  rw [C.selectedEndpointBlockData_A0_eq hoff,
    C.selectedEndpointBlockData_A1_eq hoff,
    C.selectedEndpointBlockData_B01_eq,
    C.selectedEndpointBlockData_B10_eq] at hpoint
  exact hpoint

end SpectralContinuationWitness

end WitnessOffDiagonal

end DavisKahanExt
end TauCeti
