/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
/-!
# Integer valuations from complete-DVF uniformizers

A chosen uniformizer determines the exponent of every nonzero field value and
therefore an integer-valued multiplicative valuation on field units.
-/

@[expose] public section

noncomputable
section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The nonzero value of a field unit, regarded as a unit of the ambient value
group. -/
noncomputable def fieldUnitValueUnit
    (F : CompleteDVF.{u, v} K) (x : Kˣ) : F.ValueGroupˣ :=
  Units.mk0 (F.valuation (x : K))
    ((_root_.Valuation.ne_zero_iff F.valuation).2 x.ne_zero)

/-- Establishes the identity `(CompleteDVF.fieldUnitValueUnit F) (1 : Kˣ) = 1`. -/
@[simp]
theorem fieldUnitValueUnit_one (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) (1 : Kˣ) = 1 := by
  ext
  simp [fieldUnitValueUnit]

/--
`fieldUnitValueUnit` satisfies the multiplication formula `(CompleteDVF.fieldUnitValueUnit F) (x *
y) = (CompleteDVF.fieldUnitValueUnit F) x * (CompleteDVF.fieldUnitValueUnit F) y`.
-/
@[simp]
theorem fieldUnitValueUnit_mul
    (F : CompleteDVF.{u, v} K) (x y : Kˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) (x * y) =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x *
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) y := by
  ext
  simp [fieldUnitValueUnit]

/-- The value of a chosen uniformizer, regarded as a unit of the ambient value
group. -/
noncomputable def uniformizerValueUnit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    F.ValueGroupˣ :=
  Units.mk0 (F.valuation (π : K)) hπ.val_ne_zero

/-- The value of every field unit is an integral power of the value of a chosen
uniformizer. -/
theorem exists_uniformizerValueUnit_zpow_eq_fieldUnitValueUnit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ∃ n : ℤ,
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ n =
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x := by
  have hxmem :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x ∈
        MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass F.valuation) := by
    exact
      MonoidWithZeroHom.mem_valueGroup
        (MonoidWithZeroHom.ofClass F.valuation)
        (show (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x :
          F.ValueGroup)) ∈
            Set.range F.valuation from
          ⟨(x : K), by simp [fieldUnitValueUnit]⟩)
  rw [hπ.zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hxmem
  simpa [uniformizerValueUnit] using hxmem

/-- Integral powers of the value of a uniformizer are indexed uniquely. -/
theorem uniformizerValueUnit_zpow_inj
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {m n : ℤ} :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ m =
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ n ↔
      m = n := by
  constructor
  · intro h
    have hvalue :
        F.valuation (π : K) ^ m =
          F.valuation (π : K) ^ n := by
      simpa [uniformizerValueUnit, Units.val_zpow_eq_zpow_val] using
        congrArg (fun γ : F.ValueGroupˣ => (γ : F.ValueGroup)) h
    exact
      (zpow_right_inj₀ hπ.val_pos (ne_of_lt hπ.val_lt_one)).1 hvalue
  · intro h
    rw [h]

/-- The integer exponent of the value of a field unit with respect to a chosen
uniformizer. -/
noncomputable def uniformizerValueExponent
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) : ℤ :=
  Classical.choose
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.exists_uniformizerValueUnit_zpow_eq_fieldUnitValueUnit F) hπ x)

/-- The chosen exponent really recovers the value of the field unit. -/
theorem uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x :=
  Classical.choose_spec
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.exists_uniformizerValueUnit_zpow_eq_fieldUnitValueUnit F) hπ x)

/-- The integer-valued multiplicative valuation on `Kˣ` attached to a chosen
uniformizer of an arbitrary complete DVF.  Its value is the exponent of the
field-unit value as a power of the uniformizer value. -/
noncomputable def multiplicativeIntegerValuationOfUniformizer
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    MultiplicativeIntegerValuation Kˣ where
  val x := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x
  map_one := by
    apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F)
      hπ).1
    rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
    simp
  map_mul x y := by
    apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F)
      hπ).1
    calc
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ (x
            * y) =
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) (x * y) := by
        rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
      _ = (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x *
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) y := by
        rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul F)]
      _ =
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x *
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F)
              hπ y := by
        rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F),
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
      _ =
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
            ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x +
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F)
                hπ y) := by
        rw [← zpow_add]

/--
Establishes the identity `((CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val x =
(CompleteDVF.uniformizerValueExponent F) hπ x`.
-/
@[simp]
theorem multiplicativeIntegerValuationOfUniformizer_val
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val x =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x :=
  rfl

/-- The chosen uniformizer has integer value one for the attached valuation. -/
theorem multiplicativeIntegerValuationOfUniformizer_isUniformizer
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).IsUniformizer
      (Units.mk0 (π : K) hπ.ne_zero) := by
  change (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ
    (Units.mk0 (π : K) hπ.ne_zero) = 1
  apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F) hπ).1
  rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
  ext
  simp [fieldUnitValueUnit, uniformizerValueUnit]

/-- The zero subgroup of the attached integer-valued valuation is exactly the
valuation-subring unit group. -/
theorem multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).zeroSubgroup =
      F.valuation.valuationSubring.unitGroup := by
  ext x
  rw [LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.mem_zeroSubgroup_iff,
    _root_.Valuation.mem_unitGroup_iff]
  change (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x = 0 ↔
    F.valuation (x : K) = 1
  constructor
  · intro hx
    have hvalue :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F) hπ x
    rw [hx, zpow_zero] at hvalue
    have hvalue' :=
      congrArg (fun γ : F.ValueGroupˣ => (γ : F.ValueGroup)) hvalue
    simpa [fieldUnitValueUnit] using hvalue'.symm
  · intro hx
    apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F)
      hπ).1
    rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
    ext
    simp [fieldUnitValueUnit, hx]

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
