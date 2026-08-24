/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Fourier transport from Zhou's actual compact dual to the raw coordinate Haar
model. This is the kernel part of the §3 crossed-product bridge. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.FourierAction
import LeanPool.ConnesRigidity.Paper.Section3.DualShearMeasure

/-!
The fourier coordinates component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperFourierCoordinates

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualHaar
open PaperDualTopology
open PaperFactorIsomorphism
open PaperFourier
open PaperFourierAction

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates
/--
The `CharacterL2` construction used in the Connes rigidity formalization.
-/
abbrev CharacterL2 := Lp ℂ 2 paperCharacterHaar
/--
The `CoordinateL2` construction used in the Connes rigidity formalization.
-/
abbrev CoordinateL2 := Lp ℂ 2 coordinatesHaar

/--
The `paperDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperDDecidableEq : DecidableEq D := Classical.decEq D
/--
The `paperMultiplicativeDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _

/- The algebraic coordinate equivalence with its Borel inverse. Paper: §3.
-/
/--
The `characterCoordinatesMeasurableEquiv` construction used in the Connes rigidity formalization.
-/
def characterCoordinatesMeasurableEquiv : CharacterSpace ≃ᵐ Coordinates where
  toEquiv := PaperDualHaar.characterCoordinatesEquiv.toEquiv
  measurable_toFun := characterCoordinatesHomeomorph.continuous.measurable
  measurable_invFun := characterCoordinatesHomeomorph.symm.continuous.measurable

/-- Transport of normalized Haar from the compact dual to Zhou coordinates.
Paper: §3. -/
theorem characterCoordinates_measurePreserving :
    MeasurePreserving characterCoordinatesMeasurableEquiv
      paperCharacterHaar coordinatesHaar := by
  let μ := paperCharacterHaar
  let _ : Measure.IsAddHaarMeasure μ := by
    dsimp [μ, paperCharacterHaar]
    infer_instance
  have _ : Measure.IsAddHaarMeasure
      (Measure.map characterCoordinatesMeasurableEquiv μ) :=
    AddEquiv.isAddHaarMeasure_map μ PaperDualHaar.characterCoordinatesEquiv
      characterCoordinatesHomeomorph.continuous
      characterCoordinatesHomeomorph.symm.continuous
  have _ : IsProbabilityMeasure
      (Measure.map characterCoordinatesMeasurableEquiv μ) :=
    μ.isProbabilityMeasure_map
      characterCoordinatesHomeomorph.continuous.measurable.aemeasurable
  refine ⟨characterCoordinatesMeasurableEquiv.measurable, ?_⟩
  change Measure.map characterCoordinatesMeasurableEquiv μ = coordinatesHaar
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_unique Coordinates
    (Measure.map characterCoordinatesMeasurableEquiv μ)

/- The L² pullback along the character/coordinate equivalence. Paper: §3.
-/
/--
The `characterCoordinatesLpEquiv` construction used in the Connes rigidity formalization.
-/
def characterCoordinatesLpEquiv : CharacterL2 ≃ₗᵢ[ℂ] CoordinateL2 where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving
        (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
        (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
          characterCoordinates_measurePreserving)
      invFun := Lp.compMeasurePreserving
        characterCoordinatesMeasurableEquiv characterCoordinates_measurePreserving
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
            characterCoordinates_measurePreserving)
          characterCoordinates_measurePreserving
        simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply,
          show (fun z : CharacterSpace ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          characterCoordinates_measurePreserving
          (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
            characterCoordinates_measurePreserving)
        simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply,
          show (fun z : Coordinates ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add
          (Lp.compMeasurePreserving
            (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
            (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
              characterCoordinates_measurePreserving)) f g
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ
            (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
            (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
              characterCoordinates_measurePreserving)) c f }
  norm_map' := fun f => Lp.norm_compMeasurePreserving f
    (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
      characterCoordinates_measurePreserving)

@[simp] theorem characterCoordinatesLpEquiv_apply (f : CharacterL2) :
    characterCoordinatesLpEquiv f =
      Lp.compMeasurePreserving
        (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
        (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
          characterCoordinates_measurePreserving) f := rfl

/-- The paper Fourier transform with target in Zhou coordinates. Paper: §3.
-/
def paperFourierCoordinateUnitary :
    GroupL2 (Multiplicative D) ≃ₗᵢ[ℂ] CoordinateL2 :=
  paperFourierUnitary.trans characterCoordinatesLpEquiv

/--
The `coordinateCharacterL2` construction used in the Connes rigidity formalization.
-/
def coordinateCharacterL2 (d : D) : CoordinateL2 :=
  characterCoordinatesLpEquiv (characterL2 d)

@[simp] theorem paperFourierCoordinateUnitary_single (d : D) :
    paperFourierCoordinateUnitary
        (lp.single 2 (Multiplicative.ofAdd d) (1 : ℂ)) =
      coordinateCharacterL2 d := by
  exact congrArg characterCoordinatesLpEquiv
    (paperFourierUnitary_single d)

/-- The transported kernel multiplier in raw coordinates. Paper: §3.
-/
def coordinateCharacterMultiplier (d : D) :
    CoordinateL2 →L[ℂ] CoordinateL2 :=
  characterCoordinatesLpEquiv.conjStarAlgEquiv
    (characterMultiplier (complexCharacter d))

/- Kernel regular translations become the transported Zhou-coordinate
multiplier. Paper: §3. -/
theorem paperFourierCoordinate_conjugates_regular (d : D) :
    paperFourierCoordinateUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)) =
      coordinateCharacterMultiplier d := by
  change (characterCoordinatesLpEquiv.conjStarAlgEquiv
      (paperFourierUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)))) = _
  rw [paperFourier_conjugates_regular]
  rfl

end
end PaperFourierCoordinates
end Connes
