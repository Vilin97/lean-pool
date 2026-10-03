/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase
public import Mathlib.RingTheory.Valuation.Extension
/-!
# Uniformizers and unit subgroups for induced integer valuations

This file relates the induced integer valuation to normalized uniformizers,
valuation-ring units, and scalar extension of field units.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  mem_zeroSubgroup_iff →
    mem_zeroSubgroup_iff


noncomputable
section

universe u

open WithZero
open scoped WithZero

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- An element of `ℤᵐ⁰`-value `exp (-1)` is a uniformizer for the attached
integer-valued multiplicative valuation. -/
theorem ofWithZeroValuation_isUniformizer_of_valuation_eq_exp_neg
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (π : Kˣ)
    (hπ : v (π : K) = WithZero.exp (-1 : ℤ)) :
    (ofWithZeroValuation v).IsUniformizer π :=
  ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg v π hπ

/-- A normalized `ℤᵐ⁰`-valued valuation with an element of value `exp (-1)`
has a uniformizer in the attached integer-valued multiplicative valuation. -/
theorem ofWithZeroValuation_hasUniformizer_of_exists_valuation_eq_exp_neg
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∃ π : Kˣ, v (π : K) = WithZero.exp (-1 : ℤ)) :
    (ofWithZeroValuation v).HasUniformizer := by
  rcases h with ⟨π, hπ⟩
  exact ⟨π,
    ofWithZeroValuation_isUniformizer_of_valuation_eq_exp_neg v π hπ⟩

/-- A surjective `ℤᵐ⁰`-valued valuation has a field unit of value
`exp (-1)`. -/
theorem exists_unit_valuation_eq_exp_neg_of_surjective
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v) :
    ∃ π : Kˣ, v (π : K) = WithZero.exp (-1 : ℤ) := by
  rcases hv (WithZero.exp (-1 : ℤ)) with ⟨π, hπ⟩
  have hπ_ne : π ≠ 0 := by
    intro hzero
    have hzero_val : v π = 0 := by
      simp [hzero]
    rw [hπ] at hzero_val
    exact WithZero.exp_ne_zero hzero_val
  exact ⟨Units.mk0 π hπ_ne, by simpa using hπ⟩

/-- A surjective `ℤᵐ⁰`-valued valuation gives a uniformizer for the attached
integer-valued multiplicative valuation. -/
theorem ofWithZeroValuation_hasUniformizer_of_surjective
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v) :
    (ofWithZeroValuation v).HasUniformizer :=
  ofWithZeroValuation_hasUniformizer_of_exists_valuation_eq_exp_neg v
    (exists_unit_valuation_eq_exp_neg_of_surjective v hv)

/-- A surjective `ℤᵐ⁰`-valued valuation gives a surjective integer-valued
valuation on field units. -/
theorem ofWithZeroValuation_val_surjective_of_surjective
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v) :
    Function.Surjective (ofWithZeroValuation v).val := by
  intro n
  rcases hv (WithZero.exp (-n)) with ⟨x, hx⟩
  have hx_ne : x ≠ 0 := by
    intro hzero
    have hzero_val : v x = 0 := by
      simp [hzero]
    rw [hx] at hzero_val
    exact WithZero.exp_ne_zero hzero_val
  exact ⟨Units.mk0 x hx_ne,
    ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
      v (Units.mk0 x hx_ne) (by simpa using hx)⟩

/--
Establishes the identity `(ofWithZeroValuation v).zeroSubgroup = v.valuationSubring.unitGroup`.
-/
theorem ofWithZeroValuation_zeroSubgroup_eq_unitGroup
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    (ofWithZeroValuation v).zeroSubgroup =
      v.valuationSubring.unitGroup := by
  ext x
  rw [mem_zeroSubgroup_iff, _root_.Valuation.mem_unitGroup_iff]
  change -WithZero.log (v (x : K)) = 0 ↔ v (x : K) = 1
  have hx : v (x : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
  constructor
  · intro h
    have hlog : WithZero.log (v (x : K)) = 0 := by
      exact neg_eq_zero.mp h
    calc
      v (x : K) = WithZero.exp (WithZero.log (v (x : K))) := by
        rw [WithZero.exp_log hx]
      _ = 1 := by
        rw [hlog]
        simp
  · intro h
    rw [h]
    simp

variable {L : Type u} [Field L] [Algebra K L]

/--
Establishes the membership statement `∀ u : Kˣ, u ∈ (ofWithZeroValuation vK).zeroSubgroup →
baseUnitsMap (K := K) (L := L) u ∈ (ofWithZeroValuation vL).zeroSubgroup`.
-/
theorem baseUnitsMap_zeroSubgroup_ofWithZeroValuation
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ))) [vK.HasExtension vL] :
    ∀ u : Kˣ, u ∈ (ofWithZeroValuation vK).zeroSubgroup →
      baseUnitsMap (K := K) (L := L) u ∈
        (ofWithZeroValuation vL).zeroSubgroup := by
  intro u hu
  rw [ofWithZeroValuation_zeroSubgroup_eq_unitGroup] at hu ⊢
  rw [_root_.Valuation.mem_unitGroup_iff] at hu ⊢
  simpa using
    (_root_.Valuation.HasExtension.val_map_eq_one_iff
      (vR := vK) (vA := vL) (u : K)).2 hu


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
