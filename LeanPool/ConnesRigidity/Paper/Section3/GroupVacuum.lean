/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Vacuum transport for the two concrete Zhou group-factor models.  The
identity fibre is the zero Fourier coefficient, and all other fibres vanish.
Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.GroupQuotient

/-!
The group vacuum component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperGroupVacuum

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperCrossedHaar
open PaperCrossedKernel
open PaperFourier
open PaperFourierCoordinates
open PaperGroupFactor
open PaperQuotientAction
open SemidirectFubini
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
local notation "Γ₁" => PaperKernel.paperGammaCarrier paperThetaOneHom
local notation "Γ₂" => PaperKernel.paperGammaCarrier paperThetaTwoHom

/--
The `paperDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperDDecidableEq : DecidableEq D := Classical.decEq D
/--
The `paperMultiplicativeDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _
/--
The `paperGroupOneDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperGroupOneDecidableEq : DecidableEq Γ₁ := Classical.decEq _
/--
The `paperGroupTwoDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperGroupTwoDecidableEq : DecidableEq Γ₂ := Classical.decEq _
local instance paperHaarActionOneFinite :
    IsFiniteMeasure paperHaarActionOne.measure :=
  ⟨by
    rw [paperHaarActionOne.probability.measure_univ]
    exact ENNReal.one_lt_top⟩
local instance paperHaarActionTwoFinite :
    IsFiniteMeasure paperHaarActionTwo.measure :=
  ⟨by
    rw [paperHaarActionTwo.probability.measure_univ]
    exact ENNReal.one_lt_top⟩

/--
The `paperIdentityOne` construction used in the Connes rigidity formalization.
-/
def paperIdentityOne : GroupL2 Γ₁ :=
  lp.single 2 (1 : Γ₁) (1 : ℂ)

/--
The `paperIdentityTwo` construction used in the Connes rigidity formalization.
-/
def paperIdentityTwo : GroupL2 Γ₂ :=
  lp.single 2 (1 : Γ₂) (1 : ℂ)

/- The zero Fourier character is the constant vector. Paper: §3. -/
theorem coordinateCharacterL2_zero :
    coordinateCharacterL2 (0 : D) =
      Lp.const 2 PaperDualTopology.coordinatesHaar (1 : ℂ) := by
  apply Lp.ext
  have hcharacter := coordinateCharacterL2_apply_ae (0 : D)
  have hconstant := Lp.coeFn_const
    (μ := PaperDualTopology.coordinatesHaar) (p := 2) (1 : ℂ)
  filter_upwards [hcharacter, hconstant] with p hcharacter hconstant
  calc
    coordinateCharacterL2 (0 : D) p = coordinateComplexCharacter (0 : D) p :=
      hcharacter
    _ = 1 := by
      simp [coordinateComplexCharacter, complexCharacter]
    _ = Lp.const 2 PaperDualTopology.coordinatesHaar (1 : ℂ) p := hconstant.symm

private theorem paperCrossedVacuumOne_apply (h : H) :
    crossedVacuum paperHaarActionOne h =
      if h = 1 then
        Lp.const 2 paperHaarActionOne.measure (1 : ℂ)
      else 0 := by
  classical
  let _ : IsProbabilityMeasure paperHaarActionOne.measure :=
    paperHaarActionOne.probability
  let _ : DecidableEq PaperCrossedHaar.H := Classical.decEq _
  unfold crossedVacuum
  by_cases hh : h = (1 : H)
  · subst h
    rw [ite_eq_left rfl]
    exact lp.single_apply_self
      (E := fun _ : PaperCrossedHaar.H => crossedBaseHilbert paperHaarActionOne)
      2 (1 : PaperCrossedHaar.H)
        (Lp.const 2 paperHaarActionOne.measure (1 : ℂ))
  · rw [ite_eq_right hh]
    exact lp.single_apply_ne
      (E := fun _ : PaperCrossedHaar.H => crossedBaseHilbert paperHaarActionOne)
      2 (1 : PaperCrossedHaar.H)
        (Lp.const 2 paperHaarActionOne.measure (1 : ℂ)) hh

private theorem paperCrossedVacuumTwo_apply (h : H) :
    crossedVacuum paperHaarActionTwo h =
      if h = 1 then
        Lp.const 2 paperHaarActionTwo.measure (1 : ℂ)
      else 0 := by
  classical
  let _ : IsProbabilityMeasure paperHaarActionTwo.measure :=
    paperHaarActionTwo.probability
  let _ : DecidableEq PaperCrossedHaar.H := Classical.decEq _
  unfold crossedVacuum
  by_cases hh : h = (1 : H)
  · subst h
    rw [ite_eq_left rfl]
    exact lp.single_apply_self
      (E := fun _ : PaperCrossedHaar.H => crossedBaseHilbert paperHaarActionTwo)
      2 (1 : PaperCrossedHaar.H)
        (Lp.const 2 paperHaarActionTwo.measure (1 : ℂ))
  · rw [ite_eq_right hh]
    exact lp.single_apply_ne
      (E := fun _ : PaperCrossedHaar.H => crossedBaseHilbert paperHaarActionTwo)
      2 (1 : PaperCrossedHaar.H)
        (Lp.const 2 paperHaarActionTwo.measure (1 : ℂ)) hh

/- The identity point mass has only the identity acting-group fibre. Paper:
§3. -/
theorem paperGroupFactorUnitaryOne_vacuum :
    paperGroupFactorUnitaryOne paperIdentityOne =
      crossedVacuum paperHaarActionOne := by
  classical
  let _ : IsProbabilityMeasure paperHaarActionOne.measure :=
    paperHaarActionOne.probability
  apply lp.ext
  funext h
  rw [paperGroupFactorUnitaryOne_apply]
  by_cases hh : h = 1
  · subst h
    have hfiber :
        semidirectFubini (A := Multiplicative D) (K := Construction.H)
            paperThetaOneHom
            paperIdentityOne 1 =
          lp.single 2 (Multiplicative.ofAdd (0 : D)) (1 : ℂ) := by
      ext a
      simp only [paperIdentityOne, semidirectFubini_apply, lp.single_apply,
        Pi.single_apply,
        SemidirectProduct.ext_iff, SemidirectProduct.one_left, ofAdd_zero,
        SemidirectProduct.one_right, and_true]
    rw [hfiber, paperFourierCoordinateUnitary_single,
      coordinateCharacterL2_zero]
    rw [paperCrossedVacuumOne_apply, ite_eq_left rfl]
    change (Lp.const 2 PaperDualTopology.coordinatesHaar (1 : ℂ)) =
      Lp.const 2 PaperDualTopology.coordinatesHaar (1 : ℂ)
    rfl
  · have hfiber :
        semidirectFubini (A := Multiplicative D) (K := Construction.H)
            paperThetaOneHom
            paperIdentityOne h = 0 := by
      ext a
      simp only [paperIdentityOne, semidirectFubini_apply, lp.single_apply,
        Pi.single_apply,
        SemidirectProduct.ext_iff, SemidirectProduct.one_right, hh,
        and_false, ite_false,
        ZeroMemClass.coe_zero, PreLp.zero_apply]
    rw [hfiber, map_zero]
    rw [paperCrossedVacuumOne_apply, ite_eq_right hh]
    rfl

/- The second concrete factor has the same vacuum transport. Paper: §3. -/
theorem paperGroupFactorUnitaryTwo_vacuum :
    paperGroupFactorUnitaryTwo paperIdentityTwo =
      crossedVacuum paperHaarActionTwo := by
  classical
  let _ : IsProbabilityMeasure paperHaarActionTwo.measure :=
    paperHaarActionTwo.probability
  apply lp.ext
  funext h
  rw [paperGroupFactorUnitaryTwo_apply]
  by_cases hh : h = 1
  · subst h
    have hfiber :
        semidirectFubini (A := Multiplicative D) (K := Construction.H)
            paperThetaTwoHom
            paperIdentityTwo 1 =
          lp.single 2 (Multiplicative.ofAdd (0 : D)) (1 : ℂ) := by
      ext a
      simp only [paperIdentityTwo, semidirectFubini_apply, lp.single_apply,
        Pi.single_apply,
        SemidirectProduct.ext_iff, SemidirectProduct.one_left, ofAdd_zero,
        SemidirectProduct.one_right, and_true]
    rw [hfiber, paperFourierCoordinateUnitary_single,
      coordinateCharacterL2_zero]
    rw [paperCrossedVacuumTwo_apply, ite_eq_left rfl]
    change (Lp.const 2 PaperDualTopology.coordinatesHaar (1 : ℂ)) =
      Lp.const 2 PaperDualTopology.coordinatesHaar (1 : ℂ)
    rfl
  · have hfiber :
        semidirectFubini (A := Multiplicative D) (K := Construction.H)
            paperThetaTwoHom
            paperIdentityTwo h = 0 := by
      ext a
      simp only [paperIdentityTwo, semidirectFubini_apply, lp.single_apply,
        Pi.single_apply,
        SemidirectProduct.ext_iff, SemidirectProduct.one_right, hh,
        and_false, ite_false,
        ZeroMemClass.coe_zero, PreLp.zero_apply]
    rw [hfiber, map_zero]
    rw [paperCrossedVacuumTwo_apply, ite_eq_right hh]
    rfl

end
end PaperGroupVacuum
end Connes
