/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Fourier covariance for the actual Zhou quotient actions. The algebraic action
is transported from the kernel to its compact dual and then to the coordinate
Haar model. Paper: §§3--4.
-/
import LeanPool.ConnesRigidity.Paper.Section3.CrossedKernel
import LeanPool.ConnesRigidity.Paper.Section3.FourierCoordinates

/-!
The quotient action component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperQuotientAction

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualHaar
open PaperDualTopology
open PaperFourier
open PaperFourierAction
open PaperFourierCoordinates
open PaperCrossedAction
open PaperCrossedHaar
open PaperCrossedKernel
open CrossedProduct

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates
/--
The `CoordinateL2` construction used in the Connes rigidity formalization.
-/
abbrev CoordinateL2 := Lp ℂ 2 coordinatesHaar
/--
The `KernelL2` construction used in the Connes rigidity formalization.
-/
abbrev KernelL2 := GroupL2 (Multiplicative D)

/--
The `paperDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperDDecidableEq : DecidableEq D := Classical.decEq D
/--
The `paperMultiplicativeDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _

/- The additive kernel action underlying the first quotient. Paper: §2.
-/
/--
The `paperThetaOneAddEquiv` construction used in the Connes rigidity formalization.
-/
def paperThetaOneAddEquiv (h : H) : D ≃+ D :=
  (paperThetaOneLinearHom h).toAddEquiv

/-- The additive kernel action underlying the second quotient. Paper: §2.
-/
def paperThetaTwoAddEquiv (h : H) : D ≃+ D :=
  (paperThetaTwoLinearHom h).toAddEquiv

/-- The multiplicative reindexing form used by the group Hilbert space. Paper:
§3.
-/
def paperThetaOneMulEquiv (h : H) : Multiplicative D ≃ Multiplicative D :=
  (additiveEquivToMulAut (paperThetaOneLinearHom h)).toEquiv

/-- The second quotient has the analogous multiplicative reindexing. Paper:
§3.
-/
def paperThetaTwoMulEquiv (h : H) : Multiplicative D ≃ Multiplicative D :=
  (additiveEquivToMulAut (paperThetaTwoLinearHom h)).toEquiv

@[simp] theorem paperThetaOneMulEquiv_ofAdd (h : H) (d : D) :
    paperThetaOneMulEquiv h (Multiplicative.ofAdd d) =
      Multiplicative.ofAdd (paperThetaOneLinearHom h d) := rfl

@[simp] theorem paperThetaTwoMulEquiv_ofAdd (h : H) (d : D) :
    paperThetaTwoMulEquiv h (Multiplicative.ofAdd d) =
      Multiplicative.ofAdd (paperThetaTwoLinearHom h d) := rfl

/- Reindexing sends a scalar point mass to the corresponding point mass. Paper:
§3. -/
private theorem l2Reindex_single
    {α β : Type*} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    (i : α) (c : ℂ) :
    l2Reindex e (lp.single 2 i c) = lp.single 2 (e i) c := by
  ext j
  simp only [OpenAIPort.l2Reindex_apply, lp.single_apply]
  by_cases h : e.symm j = i
  · have hj : j = e i := by
      simpa only [Equiv.apply_symm_apply] using congrArg e h
    simp only [hj, Equiv.symm_apply_apply, Pi.single_eq_same]
  · have hj : j ≠ e i := by
      intro hj
      apply h
      simp only [hj, Equiv.symm_apply_apply]
    simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, hj]

/- Scalar multiples of the Fourier basis vectors are transported linearly.
Paper: §3. -/
private theorem paperFourierCoordinate_single_smul
    (b : D) (c : ℂ) :
    paperFourierCoordinateUnitary
        (lp.single 2 (Multiplicative.ofAdd b) c) =
      c • coordinateCharacterL2 b := by
  have hs : lp.single (E := fun _ : Multiplicative D => ℂ)
      2 (Multiplicative.ofAdd b) c =
      c • lp.single (E := fun _ : Multiplicative D => ℂ)
        2 (Multiplicative.ofAdd b) (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : Multiplicative D => ℂ)
        2 (Multiplicative.ofAdd b) c (1 : ℂ))
  rw [hs, map_smul, paperFourierCoordinateUnitary_single]

/- The character basis transforms according to the inverse-action convention.
Paper: §3. -/
theorem coordinateComplexCharacter_actionOne (h : H) (d : D) (p : Coordinates) :
    coordinateComplexCharacter d (paperCoordinateActionOne h⁻¹ p) =
      coordinateComplexCharacter (paperThetaOneLinearHom h d) p := by
  change complexCharacter d
      (characterCoordinatesHomeomorph.symm (paperCoordinateActionOne h⁻¹ p)) =
    complexCharacter (paperThetaOneLinearHom h d)
      (characterCoordinatesHomeomorph.symm p)
  have htransport := coordinateAction_eq_characterTransport
    paperThetaOneLinearHom h⁻¹ p
  change paperCoordinateActionOne h⁻¹ p = _ at htransport
  rw [htransport]
  have hcoords (χ : CharacterSpace) :
      characterCoordinatesHomeomorph.symm
          (PaperDualHaar.characterCoordinatesEquiv χ) = χ := by
    change PaperDualHaar.characterCoordinatesEquiv.symm
      (PaperDualHaar.characterCoordinatesEquiv χ) = χ
    exact PaperDualHaar.characterCoordinatesEquiv.symm_apply_apply χ
  rw [hcoords]
  change complexCharacter d
      (characterActionOfLinear (paperThetaOneLinearHom h⁻¹)
        (characterCoordinatesHomeomorph.symm p)) = _
  change (Additive.toMul
      (characterActionOfLinear (paperThetaOneLinearHom h⁻¹)
        (characterCoordinatesHomeomorph.symm p))
      (Multiplicative.ofAdd d) : ℂ) = _
  have hlinear := characterLinearEquiv_characterActionOfLinear
    (paperThetaOneLinearHom h⁻¹) (characterCoordinatesHomeomorph.symm p)
  have hvalue := congrArg
    (fun ℓ : Module.Dual k D => ℓ d) hlinear
  calc
    (Additive.toMul
        (characterActionOfLinear (paperThetaOneLinearHom h⁻¹)
          (characterCoordinatesHomeomorph.symm p))
        (Multiplicative.ofAdd d) : ℂ) =
        ((ZMod.toCircle
          ((characterLinearEquiv
            (characterActionOfLinear (paperThetaOneLinearHom h⁻¹)
              (characterCoordinatesHomeomorph.symm p))) d) : Circle) : ℂ) := by
      apply congrArg (fun z : Circle => (z : ℂ))
      change (Additive.toMul
          (characterActionOfLinear (paperThetaOneLinearHom h⁻¹)
            (characterCoordinatesHomeomorph.symm p))
          (Multiplicative.ofAdd d)) =
        ZMod.toCircle
          (BinaryPontryaginDual.characterLinear (M := D)
            (Additive.toMul
              (characterActionOfLinear (paperThetaOneLinearHom h⁻¹)
                (characterCoordinatesHomeomorph.symm p))) d)
      rw [BinaryPontryaginDual.characterLinear_circle]
    _ = ((ZMod.toCircle
        ((PaperDualActions.dualPrecomp (paperThetaOneLinearHom h⁻¹)
          (characterLinearEquiv (characterCoordinatesHomeomorph.symm p))) d) : Circle) : ℂ) := by
      rw [hvalue]
    _ = ((ZMod.toCircle
        ((characterLinearEquiv (characterCoordinatesHomeomorph.symm p))
          ((paperThetaOneLinearHom h⁻¹)⁻¹ d)) : Circle) : ℂ) := by
      rw [dualPrecomp_apply]
    _ = complexCharacter (paperThetaOneLinearHom h d)
        (characterCoordinatesHomeomorph.symm p) := by
      change ((ZMod.toCircle
        (BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul (characterCoordinatesHomeomorph.symm p))
          ((paperThetaOneLinearHom h⁻¹)⁻¹ d)) : Circle) : ℂ) = _
      rw [paperThetaOneLinearHom.map_inv]
      change ((ZMod.toCircle
        (BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul (characterCoordinatesHomeomorph.symm p))
          (paperThetaOneLinearHom h d)) : Circle) : ℂ) = _
      rw [BinaryPontryaginDual.characterLinear_circle]
      rfl

/- The second quotient has the same contragredient character formula. Paper:
§3. -/
theorem coordinateComplexCharacter_actionTwo (h : H) (d : D) (p : Coordinates) :
    coordinateComplexCharacter d (paperCoordinateActionTwo h⁻¹ p) =
      coordinateComplexCharacter (paperThetaTwoLinearHom h d) p := by
  change complexCharacter d
      (characterCoordinatesHomeomorph.symm (paperCoordinateActionTwo h⁻¹ p)) =
    complexCharacter (paperThetaTwoLinearHom h d)
      (characterCoordinatesHomeomorph.symm p)
  have htransport := coordinateAction_eq_characterTransport
    paperThetaTwoLinearHom h⁻¹ p
  change paperCoordinateActionTwo h⁻¹ p = _ at htransport
  rw [htransport]
  have hcoords (χ : CharacterSpace) :
      characterCoordinatesHomeomorph.symm
          (PaperDualHaar.characterCoordinatesEquiv χ) = χ := by
    change PaperDualHaar.characterCoordinatesEquiv.symm
      (PaperDualHaar.characterCoordinatesEquiv χ) = χ
    exact PaperDualHaar.characterCoordinatesEquiv.symm_apply_apply χ
  rw [hcoords]
  change complexCharacter d
      (characterActionOfLinear (paperThetaTwoLinearHom h⁻¹)
        (characterCoordinatesHomeomorph.symm p)) = _
  change (Additive.toMul
      (characterActionOfLinear (paperThetaTwoLinearHom h⁻¹)
        (characterCoordinatesHomeomorph.symm p))
      (Multiplicative.ofAdd d) : ℂ) = _
  have hlinear := characterLinearEquiv_characterActionOfLinear
    (paperThetaTwoLinearHom h⁻¹) (characterCoordinatesHomeomorph.symm p)
  have hvalue := congrArg
    (fun ℓ : Module.Dual k D => ℓ d) hlinear
  calc
    (Additive.toMul
        (characterActionOfLinear (paperThetaTwoLinearHom h⁻¹)
          (characterCoordinatesHomeomorph.symm p))
        (Multiplicative.ofAdd d) : ℂ) =
        ((ZMod.toCircle
          ((characterLinearEquiv
            (characterActionOfLinear (paperThetaTwoLinearHom h⁻¹)
              (characterCoordinatesHomeomorph.symm p))) d) : Circle) : ℂ) := by
      apply congrArg (fun z : Circle => (z : ℂ))
      change (Additive.toMul
          (characterActionOfLinear (paperThetaTwoLinearHom h⁻¹)
            (characterCoordinatesHomeomorph.symm p))
          (Multiplicative.ofAdd d)) =
        ZMod.toCircle
          (BinaryPontryaginDual.characterLinear (M := D)
            (Additive.toMul
              (characterActionOfLinear (paperThetaTwoLinearHom h⁻¹)
                (characterCoordinatesHomeomorph.symm p))) d)
      rw [BinaryPontryaginDual.characterLinear_circle]
    _ = ((ZMod.toCircle
        ((PaperDualActions.dualPrecomp (paperThetaTwoLinearHom h⁻¹)
          (characterLinearEquiv (characterCoordinatesHomeomorph.symm p))) d) : Circle) : ℂ) := by
      rw [hvalue]
    _ = ((ZMod.toCircle
        ((characterLinearEquiv (characterCoordinatesHomeomorph.symm p))
          ((paperThetaTwoLinearHom h⁻¹)⁻¹ d)) : Circle) : ℂ) := by
      rw [dualPrecomp_apply]
    _ = complexCharacter (paperThetaTwoLinearHom h d)
        (characterCoordinatesHomeomorph.symm p) := by
      change ((ZMod.toCircle
        (BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul (characterCoordinatesHomeomorph.symm p))
          ((paperThetaTwoLinearHom h⁻¹)⁻¹ d)) : Circle) : ℂ) = _
      rw [paperThetaTwoLinearHom.map_inv]
      change ((ZMod.toCircle
        (BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul (characterCoordinatesHomeomorph.symm p))
          (paperThetaTwoLinearHom h d)) : Circle) : ℂ) = _
      rw [BinaryPontryaginDual.characterLinear_circle]
      rfl

/- The coordinate character has the expected L² representative. Paper: §3. -/
theorem coordinateCharacterL2_apply_ae (d : D) :
    coordinateCharacterL2 d =ᵐ[coordinatesHaar]
      coordinateComplexCharacter d := by
  let e := characterCoordinatesMeasurableEquiv
  let he := characterCoordinates_measurePreserving
  let hei := MeasurePreserving.symm e he
  have hleft := Lp.coeFn_compMeasurePreserving
    (characterL2 d) hei
  have hchar := (complexCharacter d).coeFn_toLp
    (p := 2) (𝕜 := ℂ) paperCharacterHaar
  have hchar' := hei.quasiMeasurePreserving.tendsto_ae hchar
  filter_upwards [hleft, hchar'] with p hleft hchar'
  change (characterCoordinatesLpEquiv (characterL2 d) : Coordinates → ℂ) p = _
  calc
    _ = characterL2 d (characterCoordinatesMeasurableEquiv.symm p) := hleft
    _ = complexCharacter d (characterCoordinatesMeasurableEquiv.symm p) := hchar'
    _ = coordinateComplexCharacter d p := rfl

/- The first crossed base action transports the character basis. Paper: §3. -/
theorem coordinateCharacterL2_actionOne (h : H) (d : D) :
    crossedActionL2Equiv paperHaarActionOne h (coordinateCharacterL2 d) =
      coordinateCharacterL2 (paperThetaOneLinearHom h d) := by
  apply Lp.ext
  have hleft := Lp.coeFn_compMeasurePreserving
    (coordinateCharacterL2 d)
    (paperCoordinateActionOne_measurePreserving h⁻¹)
  have hsource := coordinateCharacterL2_apply_ae d
  let hp := paperCoordinateActionOne_measurePreserving h⁻¹
  have hsource' := hp.quasiMeasurePreserving.tendsto_ae hsource
  have htarget := coordinateCharacterL2_apply_ae (paperThetaOneLinearHom h d)
  filter_upwards [hleft, hsource', htarget] with p hleft hsource' htarget
  change (Lp.compMeasurePreserving
      (paperCoordinateActionOne h⁻¹)
      (paperCoordinateActionOne_measurePreserving h⁻¹)
      (coordinateCharacterL2 d) : Coordinates → ℂ) p = _
  calc
    _ = coordinateCharacterL2 d (paperCoordinateActionOne h⁻¹ p) := hleft
    _ = coordinateComplexCharacter d (paperCoordinateActionOne h⁻¹ p) :=
      hsource'
    _ = coordinateComplexCharacter (paperThetaOneLinearHom h d) p :=
      coordinateComplexCharacter_actionOne h d p
    _ = coordinateCharacterL2 (paperThetaOneLinearHom h d) p :=
      htarget.symm

/- The second crossed base action transports the same character basis. Paper:
§3. -/
theorem coordinateCharacterL2_actionTwo (h : H) (d : D) :
    crossedActionL2Equiv paperHaarActionTwo h (coordinateCharacterL2 d) =
      coordinateCharacterL2 (paperThetaTwoLinearHom h d) := by
  apply Lp.ext
  have hleft := Lp.coeFn_compMeasurePreserving
    (coordinateCharacterL2 d)
    (paperCoordinateActionTwo_measurePreserving h⁻¹)
  have hsource := coordinateCharacterL2_apply_ae d
  let hp := paperCoordinateActionTwo_measurePreserving h⁻¹
  have hsource' := hp.quasiMeasurePreserving.tendsto_ae hsource
  have htarget := coordinateCharacterL2_apply_ae (paperThetaTwoLinearHom h d)
  filter_upwards [hleft, hsource', htarget] with p hleft hsource' htarget
  change (Lp.compMeasurePreserving
      (paperCoordinateActionTwo h⁻¹)
      (paperCoordinateActionTwo_measurePreserving h⁻¹)
      (coordinateCharacterL2 d) : Coordinates → ℂ) p = _
  calc
    _ = coordinateCharacterL2 d (paperCoordinateActionTwo h⁻¹ p) := hleft
    _ = coordinateComplexCharacter d (paperCoordinateActionTwo h⁻¹ p) :=
      hsource'
    _ = coordinateComplexCharacter (paperThetaTwoLinearHom h d) p :=
      coordinateComplexCharacter_actionTwo h d p
    _ = coordinateCharacterL2 (paperThetaTwoLinearHom h d) p :=
      htarget.symm

/- The first kernel Fourier transform intertwines the quotient action. Paper:
§3. -/
theorem paperFourierCoordinate_actionOne_comp (h : H) (ξ : KernelL2) :
    paperFourierCoordinateUnitary
        (l2Reindex (paperThetaOneMulEquiv h) ξ) =
      crossedActionL2Equiv paperHaarActionOne h
        (paperFourierCoordinateUnitary ξ) := by
  classical
  let F : KernelL2 →L[ℂ] CoordinateL2 :=
    paperFourierCoordinateUnitary.toContinuousLinearEquiv.toContinuousLinearMap
  let R : KernelL2 →L[ℂ] KernelL2 :=
    (l2Reindex (paperThetaOneMulEquiv h)).toContinuousLinearEquiv.toContinuousLinearMap
  let P : CoordinateL2 →L[ℂ] CoordinateL2 :=
    (crossedActionL2Equiv paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap
  have hmaps : F.comp R = P.comp F := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro η
    apply ContinuousLinearMap.ext
    intro c
    change paperFourierCoordinateUnitary
        (l2Reindex (paperThetaOneMulEquiv h) (lp.single 2 η c)) =
      crossedActionL2Equiv paperHaarActionOne h
        (paperFourierCoordinateUnitary (lp.single 2 η c))
    have hsingle :
        (lp.single 2 η c : KernelL2) =
          c • (lp.single 2 η (1 : ℂ) : KernelL2) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : Multiplicative D => ℂ)
          2 η c (1 : ℂ))
    rw [hsingle]
    simp only [map_smul]
    have hη : η = Multiplicative.ofAdd (Multiplicative.toAdd η) := by
      exact (Multiplicative.toAdd : Multiplicative D ≃ D).symm_apply_apply η
    rw [hη, l2Reindex_single, paperThetaOneMulEquiv_ofAdd]
    simp only [paperFourierCoordinateUnitary_single]
    change c • coordinateCharacterL2
        (paperThetaOneLinearHom h (Multiplicative.toAdd η)) =
      P (c • coordinateCharacterL2 (Multiplicative.toAdd η))
    have hP : P (coordinateCharacterL2 (Multiplicative.toAdd η)) =
        coordinateCharacterL2
          (paperThetaOneLinearHom h (Multiplicative.toAdd η)) := by
      change crossedActionL2Equiv paperHaarActionOne h
          (coordinateCharacterL2 (Multiplicative.toAdd η)) =
        coordinateCharacterL2
          (paperThetaOneLinearHom h (Multiplicative.toAdd η))
      exact coordinateCharacterL2_actionOne h (Multiplicative.toAdd η)
    rw [map_smul P, hP]
  exact DFunLike.congr_fun hmaps ξ

/- The second kernel Fourier transform intertwines the second quotient action.
Paper: §3. -/
theorem paperFourierCoordinate_actionTwo_comp (h : H) (ξ : KernelL2) :
    paperFourierCoordinateUnitary
        (l2Reindex (paperThetaTwoMulEquiv h) ξ) =
      crossedActionL2Equiv paperHaarActionTwo h
        (paperFourierCoordinateUnitary ξ) := by
  classical
  let F : KernelL2 →L[ℂ] CoordinateL2 :=
    paperFourierCoordinateUnitary.toContinuousLinearEquiv.toContinuousLinearMap
  let R : KernelL2 →L[ℂ] KernelL2 :=
    (l2Reindex (paperThetaTwoMulEquiv h)).toContinuousLinearEquiv.toContinuousLinearMap
  let P : CoordinateL2 →L[ℂ] CoordinateL2 :=
    (crossedActionL2Equiv paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap
  have hmaps : F.comp R = P.comp F := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro η
    apply ContinuousLinearMap.ext
    intro c
    change paperFourierCoordinateUnitary
        (l2Reindex (paperThetaTwoMulEquiv h) (lp.single 2 η c)) =
      crossedActionL2Equiv paperHaarActionTwo h
        (paperFourierCoordinateUnitary (lp.single 2 η c))
    have hsingle :
        (lp.single 2 η c : KernelL2) =
          c • (lp.single 2 η (1 : ℂ) : KernelL2) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : Multiplicative D => ℂ)
          2 η c (1 : ℂ))
    rw [hsingle]
    simp only [map_smul]
    have hη : η = Multiplicative.ofAdd (Multiplicative.toAdd η) := by
      exact (Multiplicative.toAdd : Multiplicative D ≃ D).symm_apply_apply η
    rw [hη, l2Reindex_single, paperThetaTwoMulEquiv_ofAdd]
    simp only [paperFourierCoordinateUnitary_single]
    change c • coordinateCharacterL2
        (paperThetaTwoLinearHom h (Multiplicative.toAdd η)) =
      P (c • coordinateCharacterL2 (Multiplicative.toAdd η))
    have hP : P (coordinateCharacterL2 (Multiplicative.toAdd η)) =
        coordinateCharacterL2
          (paperThetaTwoLinearHom h (Multiplicative.toAdd η)) := by
      change crossedActionL2Equiv paperHaarActionTwo h
          (coordinateCharacterL2 (Multiplicative.toAdd η)) =
        coordinateCharacterL2
          (paperThetaTwoLinearHom h (Multiplicative.toAdd η))
      exact coordinateCharacterL2_actionTwo h (Multiplicative.toAdd η)
    rw [map_smul P, hP]
  exact DFunLike.congr_fun hmaps ξ

end
end PaperQuotientAction
end Connes
