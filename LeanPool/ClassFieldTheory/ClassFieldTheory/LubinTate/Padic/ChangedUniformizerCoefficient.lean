/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.AdicContractingFixedPoint
/-!
# The coefficient source for the p-adic changed-uniformizer intertwiner

Let `k` be an algebraic closure of `ZMod p`.  The Witt ring `W(k)` is the
integer ring of the completed maximal-unramified coefficient field used in
the changed-uniformizer construction. Mathlib's `WittVector.frobeniusRotation` supplies the
actual unit `ε ∈ W(k)ˣ` satisfying

`φ(ε) = ε u`

for every p-adic integer unit `u`.  This is precisely the linear-coefficient
equation for the semilinear changed-uniformizer intertwiner.

No second p-adic integer ring or Frobenius is introduced here: the base map
uses mathlib's equivalence `W(ZMod p) ≃+* ℤ_[p]`, and `φ` is
`WittVector.frobenius`.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The canonical Witt integer ring over an algebraic closure of the
residue field.  This is the coefficient ring used for the mixed-characteristic
completed-unramified descent. -/
abbrev padicCompletedUnramifiedWittRing (p : ℕ) [Fact p.Prime] :=
  WittVector p (AlgebraicClosure (ZMod p))

/-- The canonical inclusion `ℤ_[p] → W(AlgebraicClosure (ZMod p))`. -/
noncomputable def padicIntToCompletedUnramifiedWittRing
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p] →+* padicCompletedUnramifiedWittRing p :=
  (WittVector.map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
    (WittVector.equiv p).symm.toRingHom

/-- Witt Frobenius fixes the canonical p-adic integer coefficients. -/
theorem padicIntToCompletedUnramifiedWittRing_frobenius
    (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) :
    WittVector.frobenius
        (padicIntToCompletedUnramifiedWittRing p z) =
      padicIntToCompletedUnramifiedWittRing p z := by
  apply WittVector.ext
  intro n
  simp only [padicIntToCompletedUnramifiedWittRing,
    RingHom.comp_apply, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

/-- The chosen valuation ring of `ℚ_[p]` maps canonically into the
completed-unramified Witt ring. -/
noncomputable def padicValuationSubringToCompletedUnramifiedWittRing
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).valuationSubring →+*
      padicCompletedUnramifiedWittRing p := by
  change (padicDVRValuation p).valuationSubring →+*
    padicCompletedUnramifiedWittRing p
  exact
    (padicIntToCompletedUnramifiedWittRing p).comp
      (padicIntEquivValuationSubring p).symm.toRingHom

/-- The canonical map from the valuation ring of `ℚ_[p]` sends its standard
uniformizer to the Witt-vector prime. -/
theorem padicValuationSubringToCompletedUnramifiedWittRing_uniformizer
    (p : ℕ) [Fact p.Prime] :
    padicValuationSubringToCompletedUnramifiedWittRing p
        (padicIntEquivValuationSubring p (p : ℤ_[p])) =
      (p : padicCompletedUnramifiedWittRing p) := by
  change
    padicIntToCompletedUnramifiedWittRing p
        ((padicIntEquivValuationSubring p).symm
          (padicIntEquivValuationSubring p (p : ℤ_[p]))) =
      (p : padicCompletedUnramifiedWittRing p)
  rw [RingEquiv.symm_apply_apply, map_natCast]

/-- Witt Frobenius fixes the chosen p-adic valuation-ring coefficients. -/
theorem padicValuationSubringToCompletedUnramifiedWittRing_frobenius
    (p : ℕ) [Fact p.Prime]
    (z : (padicLocalField p).valuationSubring) :
    WittVector.frobenius
        (padicValuationSubringToCompletedUnramifiedWittRing p z) =
      padicValuationSubringToCompletedUnramifiedWittRing p z := by
  change
    WittVector.frobenius
        (padicIntToCompletedUnramifiedWittRing p
          ((padicIntEquivValuationSubring p).symm z)) =
      padicIntToCompletedUnramifiedWittRing p
        ((padicIntEquivValuationSubring p).symm z)
  exact
    padicIntToCompletedUnramifiedWittRing_frobenius p
      ((padicIntEquivValuationSubring p).symm z)

/-- The induced map on p-adic integer units. -/
noncomputable def padicValuationUnitToCompletedUnramifiedWittUnit
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).valuationSubringˣ →*
      (padicCompletedUnramifiedWittRing p)ˣ :=
  Units.map
    (padicValuationSubringToCompletedUnramifiedWittRing p).toMonoidHom

private theorem completedUnramifiedWittUnit_coeff_zero_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicCompletedUnramifiedWittRing p)ˣ) :
    ((u : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 := by
  have hu :
      IsUnit
        (WittVector.constantCoeff
          (u : padicCompletedUnramifiedWittRing p)) :=
    u.isUnit.map WittVector.constantCoeff
  simpa only [WittVector.constantCoeff_apply] using hu.ne_zero

private theorem padicChangedUniformizerRotation_coeff_zero_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    (WittVector.frobeniusRotation p
      (show
        ((1 : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 by
        simp)
      (completedUnramifiedWittUnit_coeff_zero_ne_zero p
        (padicValuationUnitToCompletedUnramifiedWittUnit p u))).coeff 0 ≠ 0 := by
  simpa only [WittVector.frobeniusRotation,
    WittVector.coeff_mk, WittVector.frobeniusRotationCoeff] using
    (WittVector.RecursionBase.solution_nonzero p
      (show
        ((1 : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 by
        simp)
      (completedUnramifiedWittUnit_coeff_zero_ne_zero p
        (padicValuationUnitToCompletedUnramifiedWittUnit p u)))

/-- The actual unit `ε` used as the linear coefficient of the p-adic
changed-uniformizer intertwiner. -/
noncomputable def padicChangedUniformizerLinearCoefficient
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedUnramifiedWittRing p)ˣ :=
  Classical.choose
    (WittVector.isUnit_of_coeff_zero_ne_zero
      (WittVector.frobeniusRotation p
        (show
          ((1 : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 by
          simp)
        (completedUnramifiedWittUnit_coeff_zero_ne_zero p
          (padicValuationUnitToCompletedUnramifiedWittUnit p u)))
      (padicChangedUniformizerRotation_coeff_zero_ne_zero p u))

@[simp]
private theorem padicChangedUniformizerLinearCoefficient_coe
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicChangedUniformizerLinearCoefficient p u :
        padicCompletedUnramifiedWittRing p) =
      WittVector.frobeniusRotation p
        (show
          ((1 : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 by
          simp)
        (completedUnramifiedWittUnit_coeff_zero_ne_zero p
          (padicValuationUnitToCompletedUnramifiedWittUnit p u)) :=
  Classical.choose_spec
    (WittVector.isUnit_of_coeff_zero_ne_zero
      (WittVector.frobeniusRotation p
        (show
          ((1 : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 by
          simp)
        (completedUnramifiedWittUnit_coeff_zero_ne_zero p
          (padicValuationUnitToCompletedUnramifiedWittUnit p u)))
      (padicChangedUniformizerRotation_coeff_zero_ne_zero p u))

/-- The linear coefficient satisfies the semilinear equation
`φ(ε) = ε u`. -/
theorem padicChangedUniformizerLinearCoefficient_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    WittVector.frobenius
        (padicChangedUniformizerLinearCoefficient p u :
          padicCompletedUnramifiedWittRing p) =
      (padicChangedUniformizerLinearCoefficient p u :
          padicCompletedUnramifiedWittRing p) *
        (padicValuationUnitToCompletedUnramifiedWittUnit p u :
          padicCompletedUnramifiedWittRing p) := by
  rw [padicChangedUniformizerLinearCoefficient_coe]
  simpa only [mul_one] using
    (WittVector.frobenius_frobeniusRotation p
      (show
        ((1 : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 by
        simp)
      (completedUnramifiedWittUnit_coeff_zero_ne_zero p
        (padicValuationUnitToCompletedUnramifiedWittUnit p u)))

private noncomputable def padicChangedUniformizerCoefficientOperator
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (m : ℕ) :
    padicCompletedUnramifiedWittRing p →+
      padicCompletedUnramifiedWittRing p where
  toFun a :=
    (↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) :
        padicCompletedUnramifiedWittRing p) *
      (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
      WittVector.frobenius a
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, mul_add]

private theorem padicChangedUniformizerCoefficientOperator_maps_pow_succ
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (m : ℕ) (hm : 2 ≤ m) :
    let I : Ideal (padicCompletedUnramifiedWittRing p) :=
      Ideal.span ({(p : padicCompletedUnramifiedWittRing p)} : Set _)
    ∀ (n : ℕ) {x : padicCompletedUnramifiedWittRing p},
      x ∈ I ^ n →
        padicChangedUniformizerCoefficientOperator p u m x ∈
          I ^ (n + 1) := by
  dsimp only
  let W := padicCompletedUnramifiedWittRing p
  let I : Ideal W := Ideal.span ({(p : W)} : Set W)
  let φ : W →+* W := WittVector.frobenius
  have hφI : I.map φ = I := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    dsimp only [φ]
    rw [map_natCast]
  have hpI : (p : W) ∈ I :=
    Ideal.subset_span (Set.mem_singleton (p : W))
  have hmPos : 0 < m - 1 := by omega
  have hpPowI : (p : W) ^ (m - 1) ∈ I :=
    I.pow_mem_of_mem hpI (m - 1) hmPos
  have hcI :
      (↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) : W) *
          (p : W) ^ (m - 1) ∈ I :=
    I.mul_mem_left
      (↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) : W)
      hpPowI
  intro n x hx
  have hφxMap : φ x ∈ (I ^ n).map φ :=
    Ideal.mem_map_of_mem φ hx
  have hφx : φ x ∈ I ^ n := by
    rw [Ideal.map_pow φ I n, hφI] at hφxMap
    exact hφxMap
  have hmul :
      ((↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) : W) *
          (p : W) ^ (m - 1)) * φ x ∈ I * I ^ n :=
    Ideal.mul_mem_mul hcI hφx
  change
    ((↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) : W) *
          (p : W) ^ (m - 1)) * φ x ∈ I ^ (n + 1)
  rw [pow_succ, mul_comm (I ^ n) I]
  exact hmul

/-- Every coefficient equation of degree at least two in the p-adic
semilinear intertwiner has a unique solution in the completed-unramified
Witt ring. -/
theorem existsUnique_padicChangedUniformizerCoefficient
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (m : ℕ) (hm : 2 ≤ m)
    (b : padicCompletedUnramifiedWittRing p) :
    ∃! a : padicCompletedUnramifiedWittRing p,
      a =
        b +
          (↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) :
              padicCompletedUnramifiedWittRing p) *
            (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
            WittVector.frobenius a := by
  let I : Ideal (padicCompletedUnramifiedWittRing p) :=
    Ideal.span
      ({(p : padicCompletedUnramifiedWittRing p)} : Set _)
  change
    ∃! a : padicCompletedUnramifiedWittRing p,
      a = b + padicChangedUniformizerCoefficientOperator p u m a
  exact
    IsAdicComplete.existsUnique_eq_add_of_maps_pow_succ
      I (padicChangedUniformizerCoefficientOperator p u m)
      (padicChangedUniformizerCoefficientOperator_maps_pow_succ
        p u m hm)
      b

end LubinTate

end
