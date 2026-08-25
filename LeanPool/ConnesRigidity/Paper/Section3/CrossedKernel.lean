/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The proved kernel slice of Zhou's crossed-product model. The discrete kernel
Fourier transform is lifted fiberwise over the acting group. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.FourierCoordinates
import LeanPool.ConnesRigidity.Paper.Section3.CrossedHaar

/-!
The crossed kernel component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperCrossedKernel

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualTopology
open PaperFactorIsomorphism
open PaperFourier
open PaperFourierAction
open PaperFourierCoordinates
open PaperCrossedHaar
open CrossedProduct

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates
/--
The `CoordinateL2` construction used in the Connes rigidity formalization.
-/
abbrev CoordinateL2 := Lp ℂ 2 coordinatesHaar
/--
The `X` construction used in the Connes rigidity formalization.
-/
abbrev X := paperHaarActionOne
/--
The `CrossedL2` construction used in the Connes rigidity formalization.
-/
abbrev CrossedL2 := crossedHilbert X
/--
The `FiberL2` construction used in the Connes rigidity formalization.
-/
abbrev FiberL2 := GroupL2 (Multiplicative D)
/--
The `ProductL2` construction used in the Connes rigidity formalization.
-/
abbrev ProductL2 := lp (fun _ : H ↦ FiberL2) 2

/--
The `paperDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperDDecidableEq : DecidableEq D := Classical.decEq D
/--
The `paperMultiplicativeDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _

/- The coordinate form of a compact-dual kernel character. Paper: §3.
-/
/--
The `coordinateComplexCharacter` construction used in the Connes rigidity formalization.
-/
def coordinateComplexCharacter (d : D) : C(Coordinates, ℂ) where
  toFun p := complexCharacter d (characterCoordinatesHomeomorph.symm p)
  continuous_toFun := (complexCharacter d).continuous.comp
    characterCoordinatesHomeomorph.symm.continuous

@[simp] theorem coordinateComplexCharacter_apply (d : D) (p : Coordinates) :
    coordinateComplexCharacter d p =
      complexCharacter d (characterCoordinatesHomeomorph.symm p) := rfl

/-- The bounded coefficient used by the crossed base multiplier. Paper: §3.
-/
def coordinateCharacterCoefficient (d : D) : crossedCoefficient X :=
  ContinuousMap.toLp ⊤ coordinatesHaar ℂ (coordinateComplexCharacter d)

theorem coordinateCharacterCoefficient_apply_ae (d : D) :
    coordinateCharacterCoefficient d =ᵐ[coordinatesHaar]
      coordinateComplexCharacter d :=
  (coordinateComplexCharacter d).coeFn_toLp (p := ⊤) (𝕜 := ℂ) coordinatesHaar

/-- The transported multiplier is the concrete crossed-base multiplier. Paper:
§3. -/
theorem coordinateCharacterMultiplier_eq_baseMultiplier (d : D) :
    coordinateCharacterMultiplier d =
      crossedBaseMultiplier X (coordinateCharacterCoefficient d) := by
  let e := characterCoordinatesMeasurableEquiv
  let he := characterCoordinates_measurePreserving
  let hei := MeasurePreserving.symm e he
  let q := complexCharacter d
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  have hleft := Lp.coeFn_compMeasurePreserving
    (characterMultiplier q (characterCoordinatesLpEquiv.symm ξ)) hei
  have hmul := characterMultiplier_coeFn q
    (characterCoordinatesLpEquiv.symm ξ)
  have hmul' := hei.quasiMeasurePreserving.tendsto_ae hmul
  have hxi := Lp.coeFn_compMeasurePreserving ξ he
  have hxi' := hei.quasiMeasurePreserving.tendsto_ae hxi
  have hcoeff := coordinateCharacterCoefficient_apply_ae d
  have hright := crossedBaseMultiplier_apply_ae X
    (coordinateCharacterCoefficient d) ξ
  filter_upwards [hleft, hmul', hxi', hcoeff, hright]
    with p hleft hmul' hxi' hcoeff hright
  change (characterCoordinatesLpEquiv
      (characterMultiplier q (characterCoordinatesLpEquiv.symm ξ)) :
        Coordinates → ℂ) p = _
  calc
    _ = (characterMultiplier q (characterCoordinatesLpEquiv.symm ξ))
        (characterCoordinatesMeasurableEquiv.symm p) := hleft
    _ = q (characterCoordinatesMeasurableEquiv.symm p) *
        (characterCoordinatesLpEquiv.symm ξ)
          (characterCoordinatesMeasurableEquiv.symm p) := hmul'
    _ = coordinateComplexCharacter d p * ξ p := by
      have hxi'' :
          (characterCoordinatesLpEquiv.symm ξ)
              (characterCoordinatesMeasurableEquiv.symm p) = ξ p := by
        change (Lp.compMeasurePreserving
            characterCoordinatesMeasurableEquiv he ξ)
              (characterCoordinatesMeasurableEquiv.symm p) = ξ p
        change (Lp.compMeasurePreserving
            characterCoordinatesMeasurableEquiv he ξ)
              (e.symm p) = ξ (e (e.symm p)) at hxi'
        simpa only [MeasurableEquiv.apply_symm_apply] using hxi'
      rw [hxi'']
      rfl
    _ = (coordinateCharacterCoefficient d p) * ξ p := by
      rw [hcoeff]
    _ = (crossedBaseMultiplier X
        (coordinateCharacterCoefficient d) ξ : Coordinates → ℂ) p := hright.symm

/- Fiberwise application of the paper Fourier unitary. Paper: §3.
-/
/--
The `paperCrossedKernelFourierUnitary` construction used in the Connes rigidity formalization.
-/
def paperCrossedKernelFourierUnitary : ProductL2 ≃ₗᵢ[ℂ] CrossedL2 :=
  crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary

@[simp] theorem paperCrossedKernelFourierUnitary_apply
    (ξ : ProductL2) (h : H) :
    paperCrossedKernelFourierUnitary ξ h =
      paperFourierCoordinateUnitary (ξ h) := rfl

/-- The kernel translation on the product fiber model. Paper: §3.
-/
def productKernelRegularUnitary (d : D) : ProductL2 ≃ₗᵢ[ℂ] ProductL2 :=
  crossedFiberwiseEquiv (K := H)
    (Unitary.linearIsometryEquiv
      (leftRegularUnitary (Multiplicative.ofAdd d)))

/-- The kernel translation on the concrete crossed base. Paper: §3.
-/
def crossedKernelMultiplier (d : D) : CrossedL2 →L[ℂ] CrossedL2 :=
  crossedMultiplier X (coordinateCharacterCoefficient d)

/- Kernel regular translations become crossed-base multipliers on every fiber.
Paper: §3. -/
theorem paperCrossedKernelFourier_conjugates_regular (d : D) :
    paperCrossedKernelFourierUnitary.conjStarAlgEquiv
        (productKernelRegularUnitary d).toContinuousLinearEquiv.toContinuousLinearMap =
      crossedKernelMultiplier d := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperCrossedKernelFourierUnitary.symm η
  have hη : paperCrossedKernelFourierUnitary ξ = η :=
    paperCrossedKernelFourierUnitary.apply_symm_apply η
  rw [← hη]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      ((leftRegularUnitary (Multiplicative.ofAdd d) :
        FiberL2 →L[ℂ] FiberL2)
        (paperFourierCoordinateUnitary.symm
          (paperFourierCoordinateUnitary (ξ h)))) =
    crossedBaseMultiplier X (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary (ξ h))
  rw [paperFourierCoordinateUnitary.symm_apply_apply]
  have hkernel := congrArg
      (fun T : PaperFourierCoordinates.CoordinateL2 →L[ℂ]
          PaperFourierCoordinates.CoordinateL2 =>
        T (paperFourierCoordinateUnitary (ξ h)))
      (paperFourierCoordinate_conjugates_regular d)
  rw [coordinateCharacterMultiplier_eq_baseMultiplier] at hkernel
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at hkernel
  rw [paperFourierCoordinateUnitary.symm_apply_apply] at hkernel
  exact hkernel

end
end PaperCrossedKernel
end Connes
